import compcert.lib.Coqlib
import compcert.lib.Integers
import Std.Tactic
import Lean.Elab.Tactic.Omega

namespace SimpleC.SL.IntLib

abbrev INT_MIN : Int := -2147483648
abbrev INT_MAX : Int := 2147483647
abbrev UINT_MAX : Int := 4294967295
abbrev Zabs : Int -> Int := Z.abs
abbrev Zgcd : Int -> Int -> Int := Z.gcd

def unsigned_last_nbits (x n : Int) : Int :=
  Z.modulo x (Z.pow 2 n)

def signed_last_nbits (x n : Int) : Int :=
  let v := Z.modulo x (Z.pow 2 n)
  if v < Z.pow 2 (n - 1) then v else v - Z.pow 2 n

private theorem pow_two_pos (n : Int) (hn : 0 <= n) :
    0 < Z.pow 2 n := by
  cases n with
  | ofNat n =>
      simp only [Z.pow]
      exact Int.pow_pos (by decide)
  | negSucc n => omega

private theorem pow_two_pred (n : Int) (hn : n > 0) :
    Z.pow 2 n = 2 * Z.pow 2 (n - 1) := by
  cases n with
  | negSucc n => omega
  | ofNat n =>
      cases n with
      | zero => simp at hn
      | succ n =>
          simp [Z.pow, Int.pow_succ, Int.mul_comm]

private theorem eqmod_add_l {m a b : Int} (h : Zbits.eqmod m a b) (c : Int) :
    Zbits.eqmod m (a + c) (b + c) := by
  rcases h with ⟨k, rfl⟩
  exact ⟨k, by simp [Int.add_assoc]⟩

private theorem eqmod_add_r {m a b : Int} (c : Int) (h : Zbits.eqmod m a b) :
    Zbits.eqmod m (c + a) (c + b) := by
  rcases h with ⟨k, rfl⟩
  exact ⟨k, by simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]⟩

private theorem eqmod_sub_l {m a b : Int} (h : Zbits.eqmod m a b) (c : Int) :
    Zbits.eqmod m (a - c) (b - c) := by
  rcases h with ⟨k, rfl⟩
  exact ⟨k, by simp [Int.sub_eq_add_neg, Int.add_assoc]⟩

private theorem eqmod_sub_r {m a b : Int} (c : Int) (h : Zbits.eqmod m a b) :
    Zbits.eqmod m (c - a) (c - b) := by
  rcases h with ⟨k, rfl⟩
  exact ⟨-k, by
    simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul]
    omega⟩

private theorem eqmod_mul_l {m a b : Int} (h : Zbits.eqmod m a b) (c : Int) :
    Zbits.eqmod m (a * c) (b * c) := by
  rcases h with ⟨k, rfl⟩
  exact ⟨k * c, by
    rw [Int.add_mul]
    simp only [Int.mul_assoc]
    rw [Int.mul_comm m c]⟩

private theorem eqmod_mul_r {m a b : Int} (c : Int) (h : Zbits.eqmod m a b) :
    Zbits.eqmod m (c * a) (c * b) := by
  rcases h with ⟨k, rfl⟩
  exact ⟨c * k, by
    rw [Int.mul_add, Int.mul_assoc]⟩

private theorem unsigned_eqmod (x n : Int) :
    Zbits.eqmod (Z.pow 2 n) x (unsigned_last_nbits x n) := by
  exact Zbits.eqmod_mod (Z.pow 2 n) x

private theorem eqmod_unsigned (x n : Int) :
    Zbits.eqmod (Z.pow 2 n) (unsigned_last_nbits x n) x := by
  exact Zbits.eqmod_sym _ _ _ (unsigned_eqmod x n)

private theorem signed_eqmod (x n : Int) :
    Zbits.eqmod (Z.pow 2 n) x (signed_last_nbits x n) := by
  simp only [signed_last_nbits]
  split
  · exact unsigned_eqmod x n
  · rcases unsigned_eqmod x n with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    calc
      x = k * Z.pow 2 n + unsigned_last_nbits x n := hk
      _ = (k + 1) * Z.pow 2 n +
          (unsigned_last_nbits x n - Z.pow 2 n) := by
        rw [Int.add_mul]
        omega

private theorem eqmod_signed (x n : Int) :
    Zbits.eqmod (Z.pow 2 n) (signed_last_nbits x n) x := by
  exact Zbits.eqmod_sym _ _ _ (signed_eqmod x n)

private theorem unsigned_congr {a b n : Int} (hn : n > 0)
    (h : Zbits.eqmod (Z.pow 2 n) a b) :
    unsigned_last_nbits a n = unsigned_last_nbits b n := by
  exact Zbits.eqmod_mod_eq (Z.pow 2 n) (pow_two_pos n (by omega)) a b h

private theorem signed_congr {a b n : Int} (hn : n > 0)
    (h : Zbits.eqmod (Z.pow 2 n) a b) :
    signed_last_nbits a n = signed_last_nbits b n := by
  unfold signed_last_nbits
  rw [Zbits.eqmod_mod_eq (Z.pow 2 n) (pow_two_pos n (by omega)) a b h]

theorem Zland_land (x y c : Int) :
    Z.land (Z.land x y) c = Z.land (Z.land x c) (Z.land y c) := by
  apply Z.bits_inj'
  intro n _hn
  simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

theorem Byte_cast_correct (x : Int) :
    Byte.eqm x (unsigned_last_nbits x 8) := by
  simpa [Byte.eqm, Byte.modulus, Byte.wordsize, Wordsize_8.wordsize, Z.pow] using
    unsigned_eqmod x 8

theorem UByte_cast_correct (x : Int) :
    Byte.eqm x (signed_last_nbits x 8) := by
  simpa [Byte.eqm, Byte.modulus, Byte.wordsize, Wordsize_8.wordsize, Z.pow] using
    signed_eqmod x 8

theorem Int_cast_correct (x : Int)
    (_h : Int.min_signed <= x ∧ x <= Int.max_signed) :
    Int.cast_unsigned x = unsigned_last_nbits x 32 := by
  rfl

theorem UInt_cast_correct (x : Int)
    (_h : 0 <= x ∧ x <= Int.max_unsigned) :
    Int.cast_signed x = signed_last_nbits x 32 := by
  rfl

theorem Int64_cast_correct (x : Int)
    (_h : Int64.min_signed <= x ∧ x <= Int64.max_signed) :
    Int64.cast_unsigned x = unsigned_last_nbits x 64 := by
  rfl

theorem UInt64_cast_correct (x : Int)
    (_h : 0 <= x ∧ x <= Int64.max_unsigned) :
    Int64.cast_signed x = signed_last_nbits x 64 := by
  rfl

theorem unsigned_Lastnbits_mod_correct (x n : Int) (hn : n > 0) :
    Z.modulo x (Z.pow 2 n) =
      Z.modulo (unsigned_last_nbits x n) (Z.pow 2 n) := by
  exact unsigned_congr hn (eqmod_unsigned x n) |>.symm

theorem signed_Lastnbits_mod_correct (x n : Int) (hn : n > 0) :
    Z.modulo x (Z.pow 2 n) =
      Z.modulo (signed_last_nbits x n) (Z.pow 2 n) := by
  exact unsigned_congr hn (eqmod_signed x n) |>.symm

theorem unsigned_Lastnbits_range (x n : Int) (hn : n > 0) :
    0 <= unsigned_last_nbits x n ∧ unsigned_last_nbits x n < Z.pow 2 n := by
  constructor
  · exact Int.fmod_nonneg_of_pos x (pow_two_pos n (by omega))
  · exact Int.fmod_lt_of_pos x (pow_two_pos n (by omega))

theorem signed_Lastnbits_range (x n : Int) (hn : n > 0) :
    -Z.pow 2 (n - 1) <= signed_last_nbits x n ∧
      signed_last_nbits x n < Z.pow 2 (n - 1) := by
  have hr := unsigned_Lastnbits_range x n hn
  change 0 <= Z.modulo x (Z.pow 2 n) ∧
    Z.modulo x (Z.pow 2 n) < Z.pow 2 n at hr
  have hp := pow_two_pos (n - 1) (by omega)
  have hd := pow_two_pred n hn
  simp only [signed_last_nbits]
  split <;> omega

theorem unsigned_last_nbits_eq (x n : Int)
    (h : 0 <= x ∧ x < Z.pow 2 n) :
    unsigned_last_nbits x n = x := by
  exact Int.fmod_eq_of_lt h.1 h.2

private theorem modulo_eq_add_modulus_of_neg {x m : Int}
    (hm : 0 < m) (hx0 : x < 0) (hxm : -m <= x) :
    Z.modulo x m = x + m := by
  unfold Z.modulo
  rw [Int.fmod_eq_emod_of_nonneg x (by omega)]
  have hrange : 0 <= x + m ∧ x + m < m := by omega
  calc
    x % m = (x + m) % m := by rw [Int.add_emod_right]
    _ = x + m := Int.emod_eq_of_lt hrange.1 hrange.2

theorem signed_last_nbits_eq (x n : Int) (hn : n > 0)
    (h : -Z.pow 2 (n - 1) <= x ∧ x < Z.pow 2 (n - 1)) :
    signed_last_nbits x n = x := by
  have hp := pow_two_pos (n - 1) (by omega)
  have hd := pow_two_pred n hn
  by_cases hx : x < 0
  · have hm := pow_two_pos n (by omega)
    have hmod : Z.modulo x (Z.pow 2 n) = x + Z.pow 2 n := by
      apply modulo_eq_add_modulus_of_neg hm hx
      omega
    simp only [signed_last_nbits]
    rw [hmod]
    split <;> omega
  · have hmod : Z.modulo x (Z.pow 2 n) = x := by
      exact Int.fmod_eq_of_lt (by omega) (by omega)
    simp only [signed_last_nbits]
    rw [hmod]
    split <;> omega

theorem Int_signed_eq (x : Int)
    (h : Int.min_signed <= x ∧ x <= Int.max_signed) :
    x = signed_last_nbits x 32 := by
  symm
  apply signed_last_nbits_eq x 32 (by decide)
  change -2147483648 <= x ∧ x <= 2147483647 at h
  have hp : Z.pow 2 (32 - 1) = 2147483648 := by decide
  rw [hp]
  omega

theorem UInt_unsigned_eq (x : Int)
    (h : 0 <= x ∧ x <= Int.max_unsigned) :
    x = unsigned_last_nbits x 32 := by
  symm
  apply unsigned_last_nbits_eq
  change 0 <= x ∧ x <= 4294967295 at h
  have hp : Z.pow 2 32 = 4294967296 := by decide
  rw [hp]
  omega

theorem Int64_signed_eq (x : Int)
    (h : Int64.min_signed <= x ∧ x <= Int64.max_signed) :
    x = signed_last_nbits x 64 := by
  symm
  apply signed_last_nbits_eq x 64 (by decide)
  change -9223372036854775808 <= x ∧ x <= 9223372036854775807 at h
  have hp : Z.pow 2 (64 - 1) = 9223372036854775808 := by decide
  rw [hp]
  omega

theorem UInt64_unsigned_eq (x : Int)
    (h : 0 <= x ∧ x <= Int64.max_unsigned) :
    x = unsigned_last_nbits x 64 := by
  symm
  apply unsigned_last_nbits_eq
  change 0 <= x ∧ x <= 18446744073709551615 at h
  have hp : Z.pow 2 64 = 18446744073709551616 := by decide
  rw [hp]
  omega

theorem unsigned_unsigned_add_l (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n + y) n =
      unsigned_last_nbits (x + y) n :=
  unsigned_congr hn (eqmod_add_l (eqmod_unsigned x n) y)

theorem unsigned_unsigned_add_r (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (x + unsigned_last_nbits y n) n =
      unsigned_last_nbits (x + y) n :=
  unsigned_congr hn (eqmod_add_r x (eqmod_unsigned y n))

theorem unsigned_unsigned_sub_l (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n - y) n =
      unsigned_last_nbits (x - y) n :=
  unsigned_congr hn (eqmod_sub_l (eqmod_unsigned x n) y)

theorem unsigned_unsigned_sub_r (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (x - unsigned_last_nbits y n) n =
      unsigned_last_nbits (x - y) n :=
  unsigned_congr hn (eqmod_sub_r x (eqmod_unsigned y n))

theorem unsigned_unsigned_mul_l (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n * y) n =
      unsigned_last_nbits (x * y) n :=
  unsigned_congr hn (eqmod_mul_l (eqmod_unsigned x n) y)

theorem unsigned_unsigned_mul_r (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (x * unsigned_last_nbits y n) n =
      unsigned_last_nbits (x * y) n :=
  unsigned_congr hn (eqmod_mul_r x (eqmod_unsigned y n))

theorem unsigned_unsigned_mul_l_add_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n * y + z) n =
      unsigned_last_nbits (x * y + z) n :=
  unsigned_congr hn (eqmod_add_l (eqmod_mul_l (eqmod_unsigned x n) y) z)

theorem unsigned_unsigned_mul_r_add_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (x * unsigned_last_nbits y n + z) n =
      unsigned_last_nbits (x * y + z) n :=
  unsigned_congr hn (eqmod_add_l (eqmod_mul_r x (eqmod_unsigned y n)) z)

theorem unsigned_unsigned_add_mul_l_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (x + unsigned_last_nbits y n * z) n =
      unsigned_last_nbits (x + y * z) n :=
  unsigned_congr hn (eqmod_add_r x (eqmod_mul_l (eqmod_unsigned y n) z))

theorem unsigned_unsigned_add_mul_r_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (x + y * unsigned_last_nbits z n) n =
      unsigned_last_nbits (x + y * z) n :=
  unsigned_congr hn (eqmod_add_r x (eqmod_mul_r y (eqmod_unsigned z n)))

theorem unsigned_unsigned_sub_mul_l_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (x - unsigned_last_nbits y n * z) n =
      unsigned_last_nbits (x - y * z) n :=
  unsigned_congr hn (eqmod_sub_r x (eqmod_mul_l (eqmod_unsigned y n) z))

theorem unsigned_unsigned_sub_mul_r_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (x - y * unsigned_last_nbits z n) n =
      unsigned_last_nbits (x - y * z) n :=
  unsigned_congr hn (eqmod_sub_r x (eqmod_mul_r y (eqmod_unsigned z n)))

theorem unsigned_unsigned_mul_l_sub_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n * y - z) n =
      unsigned_last_nbits (x * y - z) n :=
  unsigned_congr hn (eqmod_sub_l (eqmod_mul_l (eqmod_unsigned x n) y) z)

theorem unsigned_unsigned_mul_r_sub_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (x * unsigned_last_nbits y n - z) n =
      unsigned_last_nbits (x * y - z) n :=
  unsigned_congr hn (eqmod_sub_l (eqmod_mul_r x (eqmod_unsigned y n)) z)

theorem unsigned_unsigned_mul_l_mul_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n * y * z) n =
      unsigned_last_nbits (x * y * z) n :=
  unsigned_congr hn (eqmod_mul_l (eqmod_mul_l (eqmod_unsigned x n) y) z)

theorem unsigned_unsigned_mul_r_mul_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (x * unsigned_last_nbits y n * z) n =
      unsigned_last_nbits (x * (y * z)) n := by
  simpa [Int.mul_assoc] using
    unsigned_congr hn (eqmod_mul_l (eqmod_mul_r x (eqmod_unsigned y n)) z)

theorem unsigned_unsigned_add_l_sub_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n + y - z) n =
      unsigned_last_nbits (x + y - z) n :=
  unsigned_congr hn (eqmod_sub_l (eqmod_add_l (eqmod_unsigned x n) y) z)

theorem unsigned_unsigned_add_r_sub_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (x + unsigned_last_nbits y n - z) n =
      unsigned_last_nbits (x + (y - z)) n := by
  simpa [Int.sub_eq_add_neg, Int.add_assoc] using
    unsigned_congr hn (eqmod_sub_l (eqmod_add_r x (eqmod_unsigned y n)) z)

theorem unsigned_unsigned_add_l_add_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n + y + z) n =
      unsigned_last_nbits (x + y + z) n :=
  unsigned_congr hn (eqmod_add_l (eqmod_add_l (eqmod_unsigned x n) y) z)

theorem unsigned_unsigned_add_r_add_other (x y z n : Int) (hn : n > 0) :
    unsigned_last_nbits (x + unsigned_last_nbits y n + z) n =
      unsigned_last_nbits (x + (y + z)) n := by
  simpa [Int.add_assoc] using
    unsigned_congr hn (eqmod_add_l (eqmod_add_r x (eqmod_unsigned y n)) z)

theorem unsigned_revolutive (x n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n) n =
      unsigned_last_nbits x n :=
  unsigned_congr hn (eqmod_unsigned x n)

theorem Pow2Mod_less (x n m : Int) (hn : n >= 0) (hm : m >= 0) (hnm : n <= m) :
    Z.modulo x (Z.pow 2 n) =
      Z.modulo (Z.modulo x (Z.pow 2 m)) (Z.pow 2 n) := by
  rw [← Z.land_ones x n hn]
  rw [← Z.land_ones (Z.modulo x (Z.pow 2 m)) n hn]
  rw [← Z.land_ones x m hm]
  rw [← Z.land_assoc]
  rw [Z.land_ones (Z.ones m) n hn, Z.ones_mod_pow2 m n ⟨hn, hnm⟩]

theorem Pow2Mod_greater (x n m : Int) (hn : n >= 0) (hm : m >= 0) (hnm : n >= m) :
    Z.modulo x (Z.pow 2 m) =
      Z.modulo (Z.modulo x (Z.pow 2 m)) (Z.pow 2 n) := by
  rw [← Z.land_ones x m hm]
  rw [← Z.land_ones (Z.land x (Z.ones m)) n hn]
  rw [← Z.land_assoc]
  rw [Z.land_comm (Z.ones m) (Z.ones n)]
  rw [Z.land_ones (Z.ones n) m hm, Z.ones_mod_pow2 n m ⟨hm, hnm⟩]

theorem unsigned_revolutive_less (x n m : Int)
    (hn : n > 0) (hm : m > 0) (hnm : n <= m) :
    unsigned_last_nbits (unsigned_last_nbits x m) n =
      unsigned_last_nbits x n := by
  exact (Pow2Mod_less x n m (by omega) (by omega) hnm).symm

theorem unsigned_revolutive_greater (x n m : Int)
    (hn : n > 0) (hm : m > 0) (hnm : n >= m) :
    unsigned_last_nbits (unsigned_last_nbits x m) n =
      unsigned_last_nbits x m := by
  exact (Pow2Mod_greater x n m (by omega) (by omega) hnm).symm

theorem signed_revolutive (x n : Int) (hn : n > 0) :
    signed_last_nbits (signed_last_nbits x n) n =
      signed_last_nbits x n := by
  apply signed_last_nbits_eq _ n hn
  exact signed_Lastnbits_range x n hn

theorem Pow2Mod_zero (n m : Int) (hn : n >= 0) (hm : m >= 0) (hnm : n <= m) :
    Z.modulo (Z.pow 2 m) (Z.pow 2 n) = 0 := by
  have h := Pow2Mod_less (Z.pow 2 m) n m hn hm hnm
  simpa [Z.modulo] using h

private theorem pow_two_lt {m n : Int} (hm : 0 <= m) (hn : 0 <= n) (hmn : m < n) :
    Z.pow 2 m < Z.pow 2 n := by
  cases m with
  | negSucc m => omega
  | ofNat m =>
      cases n with
      | negSucc n => omega
      | ofNat n =>
          have hmn' : m < n := Int.ofNat_lt.mp hmn
          have hp := Nat.pow_lt_pow_right (a := 2) (by decide) hmn'
          simpa [Z.pow] using Int.ofNat_lt.mpr hp

private theorem pow_two_le {m n : Int} (hm : 0 <= m) (hn : 0 <= n) (hmn : m <= n) :
    Z.pow 2 m <= Z.pow 2 n := by
  rcases Int.lt_or_eq_of_le hmn with hlt | rfl
  · exact Int.le_of_lt (pow_two_lt hm hn hlt)
  · exact Int.le_refl _

theorem Pow2Mod_self (n m : Int) (hn : n >= 0) (hm : m >= 0) (hnm : n > m) :
    Z.modulo (Z.pow 2 m) (Z.pow 2 n) = Z.pow 2 m := by
  exact Int.fmod_eq_of_lt (Int.le_of_lt (pow_two_pos m hm))
    (pow_two_lt hm hn hnm)

private theorem modulo_less_congr {a b n m : Int}
    (hn : n >= 0) (hm : m >= 0) (hnm : n <= m)
    (h : Z.modulo a (Z.pow 2 m) = Z.modulo b (Z.pow 2 m)) :
    Z.modulo a (Z.pow 2 n) = Z.modulo b (Z.pow 2 n) := by
  rw [Pow2Mod_less a n m hn hm hnm, Pow2Mod_less b n m hn hm hnm, h]

private theorem signed_eq_of_modulo_eq {a b n : Int}
    (h : Z.modulo a (Z.pow 2 n) = Z.modulo b (Z.pow 2 n)) :
    signed_last_nbits a n = signed_last_nbits b n := by
  simp only [signed_last_nbits]
  rw [h]

private theorem signed_eq_unsigned_of_nonneg (x n : Int) (hn : n > 0)
    (hs : signed_last_nbits x n >= 0) :
    signed_last_nbits x n = unsigned_last_nbits x n := by
  have hr := unsigned_Lastnbits_range x n hn
  change 0 <= Z.modulo x (Z.pow 2 n) ∧
    Z.modulo x (Z.pow 2 n) < Z.pow 2 n at hr
  change signed_last_nbits x n = Z.modulo x (Z.pow 2 n)
  simp only [signed_last_nbits] at hs ⊢
  split <;> omega

private theorem signed_eq_unsigned_sub_of_neg (x n : Int) (hn : n > 0)
    (hs : signed_last_nbits x n < 0) :
    signed_last_nbits x n = unsigned_last_nbits x n - Z.pow 2 n := by
  have hr := unsigned_Lastnbits_range x n hn
  change 0 <= Z.modulo x (Z.pow 2 n) ∧
    Z.modulo x (Z.pow 2 n) < Z.pow 2 n at hr
  change signed_last_nbits x n = Z.modulo x (Z.pow 2 n) - Z.pow 2 n
  simp only [signed_last_nbits] at hs ⊢
  split <;> omega

theorem signed_revolutive_less (x n m : Int)
    (hn : n > 0) (hm : m > 0) (hnm : n <= m) :
    signed_last_nbits (signed_last_nbits x m) n =
      signed_last_nbits x n := by
  have hmod := modulo_less_congr (a := signed_last_nbits x m) (b := x)
    (n := n) (m := m) (by omega) (by omega) hnm
    (signed_Lastnbits_mod_correct x m hm).symm
  exact signed_eq_of_modulo_eq hmod

theorem signed_revolutive_greater (x n m : Int)
    (hn : n > 0) (hm : m > 0) (hnm : n > m) :
    signed_last_nbits (signed_last_nbits x m) n =
      signed_last_nbits x m := by
  apply signed_last_nbits_eq _ n hn
  have hr := signed_Lastnbits_range x m hm
  have hp := pow_two_lt (m := m - 1) (n := n - 1) (by omega) (by omega) (by omega)
  omega

theorem signed_unsigned_revolutive (x n : Int) (hn : n > 0) :
    signed_last_nbits (unsigned_last_nbits x n) n =
      signed_last_nbits x n :=
  signed_congr hn (eqmod_unsigned x n)

theorem signed_unsigned_revolutive_less (x n m : Int)
    (hn : n > 0) (hm : m > 0) (hnm : n <= m) :
    signed_last_nbits (unsigned_last_nbits x m) n =
      signed_last_nbits x n := by
  have hmod := modulo_less_congr (a := unsigned_last_nbits x m) (b := x)
    (n := n) (m := m) (by omega) (by omega) hnm
    (unsigned_Lastnbits_mod_correct x m hm).symm
  exact signed_eq_of_modulo_eq hmod

theorem signed_unsigned_revolutive_greater (x n m : Int)
    (hn : n > 0) (hm : m > 0) (hnm : n > m) :
    signed_last_nbits (unsigned_last_nbits x m) n =
      unsigned_last_nbits x m := by
  apply signed_last_nbits_eq _ n hn
  have hr := unsigned_Lastnbits_range x m hm
  have hp := pow_two_le (m := m) (n := n - 1) (by omega) (by omega) (by omega)
  omega

theorem unsigned_signed_revolutive (x n : Int) (hn : n > 0) :
    unsigned_last_nbits (signed_last_nbits x n) n =
      unsigned_last_nbits x n :=
  unsigned_congr hn (eqmod_signed x n)

theorem unsigned_signed_revolutive_less (x n m : Int)
    (hn : n > 0) (hm : m > 0) (hnm : n <= m) :
    unsigned_last_nbits (signed_last_nbits x m) n =
      unsigned_last_nbits x n := by
  exact modulo_less_congr (a := signed_last_nbits x m) (b := x)
    (n := n) (m := m) (by omega) (by omega) hnm
    (signed_Lastnbits_mod_correct x m hm).symm

theorem unsigned_signed_revolutive_greater_pos (x n m : Int)
    (hn : n > 0) (hm : m > 0) (hnm : n > m)
    (hs : signed_last_nbits x m >= 0) :
    unsigned_last_nbits (signed_last_nbits x m) n =
      unsigned_last_nbits x m := by
  have heq := signed_eq_unsigned_of_nonneg x m hm hs
  have hr := unsigned_Lastnbits_range x m hm
  have hp := pow_two_lt (m := m) (n := n) (by omega) (by omega) hnm
  calc
    unsigned_last_nbits (signed_last_nbits x m) n =
        unsigned_last_nbits (unsigned_last_nbits x m) n :=
      congrArg (fun v => unsigned_last_nbits v n) heq
    _ = unsigned_last_nbits x m := unsigned_last_nbits_eq _ _ ⟨hr.1, by omega⟩

theorem unsigned_signed_revolutive_greater_neg (x n m : Int)
    (hn : n > 0) (hm : m > 0) (hnm : n > m)
    (hs : signed_last_nbits x m < 0) :
    unsigned_last_nbits (signed_last_nbits x m) n =
      Z.pow 2 n - Z.pow 2 m + unsigned_last_nbits x m := by
  have hsform := signed_eq_unsigned_sub_of_neg x m hm hs
  have hr := signed_Lastnbits_range x m hm
  have hpn := pow_two_pos n (by omega)
  have hpow := pow_two_lt (m := m - 1) (n := n) (by omega) (by omega) (by omega)
  change Z.modulo (signed_last_nbits x m) (Z.pow 2 n) =
    Z.pow 2 n - Z.pow 2 m + unsigned_last_nbits x m
  rw [modulo_eq_add_modulus_of_neg hpn hs (by omega), hsform]
  omega

theorem signed_unsigned_sub_l (x y n : Int) (hn : n > 0) :
    signed_last_nbits (unsigned_last_nbits x n - y) n =
      signed_last_nbits (x - y) n :=
  signed_congr hn (eqmod_sub_l (eqmod_unsigned x n) y)

theorem signed_unsigned_sub_r (x y n : Int) (hn : n > 0) :
    signed_last_nbits (x - unsigned_last_nbits y n) n =
      signed_last_nbits (x - y) n :=
  signed_congr hn (eqmod_sub_r x (eqmod_unsigned y n))

theorem signed_unsigned_add_l (x y n : Int) (hn : n > 0) :
    signed_last_nbits (unsigned_last_nbits x n + y) n =
      signed_last_nbits (x + y) n :=
  signed_congr hn (eqmod_add_l (eqmod_unsigned x n) y)

theorem signed_unsigned_add_r (x y n : Int) (hn : n > 0) :
    signed_last_nbits (x + unsigned_last_nbits y n) n =
      signed_last_nbits (x + y) n :=
  signed_congr hn (eqmod_add_r x (eqmod_unsigned y n))

theorem signed_unsigned_mul_l (x y n : Int) (hn : n > 0) :
    signed_last_nbits (unsigned_last_nbits x n * y) n =
      signed_last_nbits (x * y) n :=
  signed_congr hn (eqmod_mul_l (eqmod_unsigned x n) y)

theorem signed_unsigned_mul_r (x y n : Int) (hn : n > 0) :
    signed_last_nbits (x * unsigned_last_nbits y n) n =
      signed_last_nbits (x * y) n :=
  signed_congr hn (eqmod_mul_r x (eqmod_unsigned y n))

theorem signed_signed_add_r (x y n : Int) (hn : n > 0) :
    signed_last_nbits (x + signed_last_nbits y n) n =
      signed_last_nbits (x + y) n :=
  signed_congr hn (eqmod_add_r x (eqmod_signed y n))

theorem signed_signed_add_l (x y n : Int) (hn : n > 0) :
    signed_last_nbits (signed_last_nbits x n + y) n =
      signed_last_nbits (x + y) n :=
  signed_congr hn (eqmod_add_l (eqmod_signed x n) y)

theorem signed_signed_sub_r (x y n : Int) (hn : n > 0) :
    signed_last_nbits (x - signed_last_nbits y n) n =
      signed_last_nbits (x - y) n :=
  signed_congr hn (eqmod_sub_r x (eqmod_signed y n))

theorem signed_signed_sub_l (x y n : Int) (hn : n > 0) :
    signed_last_nbits (signed_last_nbits x n - y) n =
      signed_last_nbits (x - y) n :=
  signed_congr hn (eqmod_sub_l (eqmod_signed x n) y)

theorem signed_signed_mul_l (x y n : Int) (hn : n > 0) :
    signed_last_nbits (signed_last_nbits x n * y) n =
      signed_last_nbits (x * y) n :=
  signed_congr hn (eqmod_mul_l (eqmod_signed x n) y)

theorem signed_signed_mul_r (x y n : Int) (hn : n > 0) :
    signed_last_nbits (x * signed_last_nbits y n) n =
      signed_last_nbits (x * y) n :=
  signed_congr hn (eqmod_mul_r x (eqmod_signed y n))

theorem unsigned_signed_add_l (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (signed_last_nbits x n + y) n =
      unsigned_last_nbits (x + y) n :=
  unsigned_congr hn (eqmod_add_l (eqmod_signed x n) y)

theorem unsigned_signed_add_r (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (x + signed_last_nbits y n) n =
      unsigned_last_nbits (x + y) n :=
  unsigned_congr hn (eqmod_add_r x (eqmod_signed y n))

theorem unsigned_signed_sub_l (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (signed_last_nbits x n - y) n =
      unsigned_last_nbits (x - y) n :=
  unsigned_congr hn (eqmod_sub_l (eqmod_signed x n) y)

theorem unsigned_signed_sub_r (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (x - signed_last_nbits y n) n =
      unsigned_last_nbits (x - y) n :=
  unsigned_congr hn (eqmod_sub_r x (eqmod_signed y n))

theorem unsigned_signed_mul_l (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (signed_last_nbits x n * y) n =
      unsigned_last_nbits (x * y) n :=
  unsigned_congr hn (eqmod_mul_l (eqmod_signed x n) y)

theorem unsigned_signed_mul_r (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (x * signed_last_nbits y n) n =
      unsigned_last_nbits (x * y) n :=
  unsigned_congr hn (eqmod_mul_r x (eqmod_signed y n))

theorem Ztestbits_unsigned_eq (x n m : Int) (hmn : m < n) :
    Z.testbit (unsigned_last_nbits x n) m = Z.testbit x m := by
  exact Z.mod_pow2_bits_low x n m hmn

theorem Ztestbits_unsigned_high (x n m : Int) (h : 0 <= n ∧ n <= m) :
    Z.testbit (unsigned_last_nbits x n) m = false := by
  exact Z.mod_pow2_bits_high x n m h

theorem Ztestbits_signed_eq (x n m : Int) (h : 0 <= m ∧ m < n) :
    Z.testbit (signed_last_nbits x n) m = Z.testbit x m := by
  simp only [signed_last_nbits]
  split
  · exact Z.mod_pow2_bits_low x n m h.2
  · change Z.testbit (Z.modulo x (Z.pow 2 n) - Z.pow 2 n) m = Z.testbit x m
    rw [show Z.modulo x (Z.pow 2 n) - Z.pow 2 n =
      Z.modulo x (Z.pow 2 n) + (-(Z.pow 2 n)) by omega]
    rw [Zbits.Z_add_is_or m h.1]
    · rw [Z.mod_pow2_bits_low x n m h.2]
      rw [show -(Z.pow 2 n) = -(two_p n) by rfl]
      rw [Zbits.Ztestbit_neg_two_p n m (by omega) h.1]
      simp [h.2]
    · intro j hj
      rw [Z.mod_pow2_bits_low x n j (by omega)]
      rw [show -(Z.pow 2 n) = -(two_p n) by rfl]
      rw [Zbits.Ztestbit_neg_two_p n j (by omega) (by omega)]
      simp [show j < n by omega]

theorem Ztestbits_signed_high_lt (x n m : Int)
    (h : 0 <= n ∧ n <= m)
    (hlt : Z.modulo x (Z.pow 2 n) < Z.pow 2 (n - 1)) :
    Z.testbit (signed_last_nbits x n) m = false := by
  simp only [signed_last_nbits]
  split
  · exact Z.mod_pow2_bits_high x n m h
  · omega

theorem Ztestbits_signed_high_ge (x n m : Int)
    (h : 0 <= n ∧ n <= m)
    (hge : Z.modulo x (Z.pow 2 n) >= Z.pow 2 (n - 1)) :
    Z.testbit (signed_last_nbits x n) m = true := by
  simp only [signed_last_nbits]
  split
  · omega
  · change Z.testbit (Z.modulo x (Z.pow 2 n) - Z.pow 2 n) m = true
    rw [show Z.modulo x (Z.pow 2 n) - Z.pow 2 n =
      Z.modulo x (Z.pow 2 n) + (-(Z.pow 2 n)) by omega]
    rw [Zbits.Z_add_is_or m (by omega)]
    · rw [Z.mod_pow2_bits_high x n m h]
      rw [show -(Z.pow 2 n) = -(two_p n) by rfl]
      rw [Zbits.Ztestbit_neg_two_p n m h.1 (by omega)]
      simp [show ¬m < n by omega]
    · intro j hj
      by_cases hjn : n <= j
      · rw [Z.mod_pow2_bits_high x n j ⟨h.1, hjn⟩]
        simp
      · rw [show -(Z.pow 2 n) = -(two_p n) by rfl]
        rw [Zbits.Ztestbit_neg_two_p n j h.1 (by omega)]
        simp [show j < n by omega]

theorem Ztestbits_signed_high (x n m : Int) (h : 0 <= n ∧ n <= m) :
    Z.testbit (signed_last_nbits x n) m =
      decide (Z.pow 2 (n - 1) <= Z.modulo x (Z.pow 2 n)) := by
  by_cases hge : Z.pow 2 (n - 1) <= Z.modulo x (Z.pow 2 n)
  · rw [Ztestbits_signed_high_ge x n m h hge]
    simp [hge]
  · rw [Ztestbits_signed_high_lt x n m h (by omega)]
    simp [hge]

theorem unsigned_last_nbits_land_distr (x y n : Int) (hn : 0 <= n) :
    unsigned_last_nbits (Z.land x y) n =
      Z.land (unsigned_last_nbits x n) (unsigned_last_nbits y n) := by
  apply Z.bits_inj'
  intro i hi
  rw [Z.land_spec]
  by_cases hin : i < n
  · rw [Ztestbits_unsigned_eq _ _ _ hin, Ztestbits_unsigned_eq _ _ _ hin,
      Ztestbits_unsigned_eq _ _ _ hin, Z.land_spec]
  · rw [Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩]
    simp

theorem unsigned_last_nbits_lor_distr (x y n : Int) (hn : 0 <= n) :
    unsigned_last_nbits (Z.lor x y) n =
      Z.lor (unsigned_last_nbits x n) (unsigned_last_nbits y n) := by
  apply Z.bits_inj'
  intro i hi
  rw [Z.lor_spec]
  by_cases hin : i < n
  · rw [Ztestbits_unsigned_eq _ _ _ hin, Ztestbits_unsigned_eq _ _ _ hin,
      Ztestbits_unsigned_eq _ _ _ hin, Z.lor_spec]
  · rw [Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩]
    simp

theorem unsigned_last_nbits_ldiff_distr (x y n : Int) (hn : 0 <= n) :
    unsigned_last_nbits (Z.ldiff x y) n =
      Z.ldiff (unsigned_last_nbits x n) (unsigned_last_nbits y n) := by
  apply Z.bits_inj'
  intro i hi
  rw [Z.ldiff_spec]
  by_cases hin : i < n
  · rw [Ztestbits_unsigned_eq _ _ _ hin, Ztestbits_unsigned_eq _ _ _ hin,
      Ztestbits_unsigned_eq _ _ _ hin, Z.ldiff_spec]
  · rw [Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩]
    simp

theorem unsigned_last_nbits_lxor_distr (x y n : Int) (hn : 0 <= n) :
    unsigned_last_nbits (Z.lxor x y) n =
      Z.lxor (unsigned_last_nbits x n) (unsigned_last_nbits y n) := by
  apply Z.bits_inj'
  intro i hi
  rw [Z.lxor_spec]
  by_cases hin : i < n
  · rw [Ztestbits_unsigned_eq _ _ _ hin, Ztestbits_unsigned_eq _ _ _ hin,
      Ztestbits_unsigned_eq _ _ _ hin, Z.lxor_spec]
  · rw [Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩]
    simp

private theorem testbit_high_of_range {x n i : Int}
    (hn : 0 <= n) (hx : 0 <= x ∧ x < Z.pow 2 n) (hi : n <= i) :
    Z.testbit x i = false := by
  have hpow : two_power_nat n.toNat = Z.pow 2 n := by
    rw [two_power_nat_equiv]
    exact congrArg (Z.pow 2) (Int.toNat_of_nonneg hn)
  apply Zbits.Ztestbit_above n.toNat x i
  · simpa [hpow] using hx
  · simpa [Int.toNat_of_nonneg hn] using hi

theorem unsigned_last_nbits_land_missing_l (x y n : Int) (hn : 0 <= n)
    (hx : 0 <= x ∧ x < Z.pow 2 n) :
    unsigned_last_nbits (Z.land x y) n = Z.land x y := by
  apply Z.bits_inj'
  intro i hi
  rw [Z.land_spec]
  by_cases hin : i < n
  · rw [Ztestbits_unsigned_eq _ _ _ hin, Z.land_spec]
  · rw [Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      testbit_high_of_range hn hx (by omega)]
    simp

theorem unsigned_last_nbits_land_missing_r (x y n : Int) (hn : 0 <= n)
    (hy : 0 <= y ∧ y < Z.pow 2 n) :
    unsigned_last_nbits (Z.land x y) n = Z.land x y := by
  rw [Z.land_comm x y]
  exact unsigned_last_nbits_land_missing_l y x n hn hy

theorem unsigned_last_nbits_land_clear_l (x y n : Int) (hn : 0 <= n) :
    Z.land (unsigned_last_nbits x n) (unsigned_last_nbits y n) =
      Z.land x (unsigned_last_nbits y n) := by
  apply Z.bits_inj'
  intro i hi
  rw [Z.land_spec, Z.land_spec]
  by_cases hin : i < n
  · rw [Ztestbits_unsigned_eq _ _ _ hin, Ztestbits_unsigned_eq _ _ _ hin]
  · rw [Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩]
    simp

theorem unsigned_last_nbits_land_clear_r (x y n : Int) (hn : 0 <= n) :
    Z.land (unsigned_last_nbits x n) (unsigned_last_nbits y n) =
      Z.land (unsigned_last_nbits x n) y := by
  apply Z.bits_inj'
  intro i hi
  rw [Z.land_spec, Z.land_spec]
  by_cases hin : i < n
  · rw [Ztestbits_unsigned_eq _ _ _ hin, Ztestbits_unsigned_eq _ _ _ hin]
  · rw [Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩]
    simp

theorem unsigned_last_nbits_lor_distr_missing (x y n : Int) (hn : 0 <= n)
    (hx : 0 <= x ∧ x < Z.pow 2 n) (hy : 0 <= y ∧ y < Z.pow 2 n) :
    unsigned_last_nbits (Z.lor x y) n = Z.lor x y := by
  rw [unsigned_last_nbits_lor_distr x y n hn,
    unsigned_last_nbits_eq x n hx, unsigned_last_nbits_eq y n hy]

theorem unsigned_last_nbits_ldiff_distr_missing_l (x y n : Int) (hn : 0 <= n)
    (hx : 0 <= x ∧ x < Z.pow 2 n) :
    unsigned_last_nbits (Z.ldiff x y) n = Z.ldiff x y := by
  apply Z.bits_inj'
  intro i hi
  rw [Z.ldiff_spec]
  by_cases hin : i < n
  · rw [Ztestbits_unsigned_eq _ _ _ hin, Z.ldiff_spec]
  · rw [Ztestbits_unsigned_high _ _ _ ⟨hn, by omega⟩,
      testbit_high_of_range hn hx (by omega)]
    simp

theorem unsigned_last_nbits_lxor_distr_missing (x y n : Int) (hn : 0 <= n)
    (hx : 0 <= x ∧ x < Z.pow 2 n) (hy : 0 <= y ∧ y < Z.pow 2 n) :
    unsigned_last_nbits (Z.lxor x y) n = Z.lxor x y := by
  rw [unsigned_last_nbits_lxor_distr x y n hn,
    unsigned_last_nbits_eq x n hx, unsigned_last_nbits_eq y n hy]

private theorem unsigned_last_nbits_arg_congr (x y n : Int) (h : x = y) :
    unsigned_last_nbits x n = unsigned_last_nbits y n :=
  congrArg (fun z => unsigned_last_nbits z n) h

private theorem signed_last_nbits_arg_congr (x y n : Int) (h : x = y) :
    signed_last_nbits x n = signed_last_nbits y n :=
  congrArg (fun z => signed_last_nbits z n) h

syntax "unsigned_unsigned_simpl" : tactic

macro_rules
  | `(tactic| unsigned_unsigned_simpl) =>
      `(tactic|
        repeat
          first
          | (rw [unsigned_unsigned_add_l] <;> try omega)
          | (rw [unsigned_unsigned_add_r] <;> try omega)
          | (rw [unsigned_unsigned_sub_l] <;> try omega)
          | (rw [unsigned_unsigned_sub_r] <;> try omega)
          | (rw [unsigned_unsigned_mul_l] <;> try omega)
          | (rw [unsigned_unsigned_mul_r] <;> try omega)
          | (rw [unsigned_revolutive] <;> try omega)
          | (rw [unsigned_unsigned_mul_l_add_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_r_add_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_l_sub_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_r_sub_other] <;> try omega)
          | (rw [unsigned_unsigned_add_l_sub_other] <;> try omega)
          | (rw [unsigned_unsigned_add_r_sub_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_l_mul_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_r_mul_other] <;> try omega)
          | (rw [unsigned_unsigned_add_l_add_other] <;> try omega)
          | (rw [unsigned_unsigned_add_r_add_other] <;> try omega)
          | (rw [unsigned_unsigned_add_mul_l_other] <;> try omega)
          | (rw [unsigned_unsigned_add_mul_r_other] <;> try omega)
          | (rw [unsigned_unsigned_sub_mul_l_other] <;> try omega)
          | (rw [unsigned_unsigned_sub_mul_r_other] <;> try omega)
          | (apply unsigned_last_nbits_arg_congr <;> omega))

syntax "signed_signed_simpl" : tactic

macro_rules
  | `(tactic| signed_signed_simpl) =>
      `(tactic|
        repeat
          first
          | (rw [signed_signed_add_l] <;> try omega)
          | (rw [signed_signed_add_r] <;> try omega)
          | (rw [signed_signed_sub_l] <;> try omega)
          | (rw [signed_signed_sub_r] <;> try omega)
          | (rw [signed_signed_mul_l] <;> try omega)
          | (rw [signed_signed_mul_r] <;> try omega)
          | (rw [signed_revolutive] <;> try omega)
          | (apply signed_last_nbits_arg_congr <;> omega))

syntax "unsigned_signed_simpl" : tactic

macro_rules
  | `(tactic| unsigned_signed_simpl) =>
      `(tactic|
        repeat
          first
          | (rw [unsigned_signed_add_l] <;> try omega)
          | (rw [unsigned_signed_add_r] <;> try omega)
          | (rw [unsigned_signed_sub_l] <;> try omega)
          | (rw [unsigned_signed_sub_r] <;> try omega)
          | (rw [unsigned_signed_mul_l] <;> try omega)
          | (rw [unsigned_signed_mul_r] <;> try omega)
          | (rw [unsigned_signed_revolutive] <;> try omega))

syntax "signed_unsigned_simpl" : tactic

macro_rules
  | `(tactic| signed_unsigned_simpl) =>
      `(tactic|
        repeat
          first
          | (rw [signed_unsigned_add_l] <;> try omega)
          | (rw [signed_unsigned_add_r] <;> try omega)
          | (rw [signed_unsigned_sub_l] <;> try omega)
          | (rw [signed_unsigned_sub_r] <;> try omega)
          | (rw [signed_unsigned_mul_l] <;> try omega)
          | (rw [signed_unsigned_mul_r] <;> try omega)
          | (rw [signed_unsigned_revolutive] <;> try omega))

syntax "lastnbits_simpl" : tactic

macro_rules
  | `(tactic| lastnbits_simpl) =>
      `(tactic|
        repeat
          first
          | (rw [unsigned_unsigned_add_l] <;> try omega)
          | (rw [unsigned_unsigned_add_r] <;> try omega)
          | (rw [unsigned_unsigned_sub_l] <;> try omega)
          | (rw [unsigned_unsigned_sub_r] <;> try omega)
          | (rw [unsigned_unsigned_mul_l] <;> try omega)
          | (rw [unsigned_unsigned_mul_r] <;> try omega)
          | (rw [unsigned_revolutive] <;> try omega)
          | (rw [unsigned_unsigned_mul_l_add_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_r_add_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_l_sub_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_r_sub_other] <;> try omega)
          | (rw [unsigned_unsigned_add_l_sub_other] <;> try omega)
          | (rw [unsigned_unsigned_add_r_sub_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_l_mul_other] <;> try omega)
          | (rw [unsigned_unsigned_mul_r_mul_other] <;> try omega)
          | (rw [unsigned_unsigned_add_l_add_other] <;> try omega)
          | (rw [unsigned_unsigned_add_r_add_other] <;> try omega)
          | (rw [unsigned_unsigned_add_mul_l_other] <;> try omega)
          | (rw [unsigned_unsigned_add_mul_r_other] <;> try omega)
          | (rw [unsigned_unsigned_sub_mul_l_other] <;> try omega)
          | (rw [unsigned_unsigned_sub_mul_r_other] <;> try omega)
          | (rw [unsigned_signed_add_l] <;> try omega)
          | (rw [unsigned_signed_add_r] <;> try omega)
          | (rw [unsigned_signed_sub_l] <;> try omega)
          | (rw [unsigned_signed_sub_r] <;> try omega)
          | (rw [unsigned_signed_mul_l] <;> try omega)
          | (rw [unsigned_signed_mul_r] <;> try omega)
          | (rw [unsigned_signed_revolutive] <;> try omega)
          | (rw [signed_unsigned_add_l] <;> try omega)
          | (rw [signed_unsigned_add_r] <;> try omega)
          | (rw [signed_unsigned_sub_l] <;> try omega)
          | (rw [signed_unsigned_sub_r] <;> try omega)
          | (rw [signed_unsigned_mul_l] <;> try omega)
          | (rw [signed_unsigned_mul_r] <;> try omega)
          | (rw [signed_unsigned_revolutive] <;> try omega)
          | (rw [signed_signed_add_l] <;> try omega)
          | (rw [signed_signed_add_r] <;> try omega)
          | (rw [signed_signed_sub_l] <;> try omega)
          | (rw [signed_signed_sub_r] <;> try omega)
          | (rw [signed_signed_mul_l] <;> try omega)
          | (rw [signed_signed_mul_r] <;> try omega)
          | (rw [signed_revolutive] <;> try omega)
          | (apply unsigned_last_nbits_arg_congr <;> omega)
          | (apply signed_last_nbits_arg_congr <;> omega))

syntax "lastnbits_eq_step " term : tactic

macro_rules
  | `(tactic| lastnbits_eq_step $x:term) =>
      `(tactic|
        rw [show $x = _ by
          first
          | (apply unsigned_last_nbits_eq <;> try omega)
          | (apply signed_last_nbits_eq <;> try omega)])

syntax "lastnbits_eq" : tactic

macro_rules
  | `(tactic| lastnbits_eq) =>
      `(tactic|
        repeat
          first
          | (rw [unsigned_last_nbits_eq] <;> try omega)
          | (rw [signed_last_nbits_eq] <;> try omega))

end SimpleC.SL.IntLib
