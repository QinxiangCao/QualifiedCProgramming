import compcert.lib.Integers

open scoped CoqZ

-- Coq `Z.pow` has an integer exponent and returns zero for negative exponents.
example : Z.pow 2 (-1) = 0 := rfl
example : Z.pow (-2) 3 = -8 := rfl
example (n : Int) : (2 : Int) ^ n = Z.pow 2 n := rfl
example : Z.abs 0 = 0 := rfl
example : Z.abs 5 = 5 := rfl
example : Z.abs (-5) = 5 := rfl
example : Z.gcd 0 0 = 0 := rfl
example : Z.gcd (-12) 18 = 6 := rfl
example : Z.gcd (-12) (-18) = 6 := rfl
example : Z.gcd 0 (-18) = 18 := rfl

-- Coq division rounds toward negative infinity and returns zero on division by zero.
example : Z.div 5 3 = 1 := rfl
example : Z.div (-5) 3 = -2 := rfl
example : Z.div 5 (-3) = -2 := rfl
example : Z.div (-5) (-3) = 1 := rfl
example : Z.div 7 0 = 0 := rfl
example : Z.div (-7) 0 = 0 := rfl

-- Coq floor modulo and truncating remainder differ on negative operands.
example : Z.modulo (-5) 3 = 1 := rfl
example : Z.modulo 5 (-3) = -1 := rfl
example : Z.modulo (-5) (-3) = -2 := rfl
example : Z.rem (-5) 3 = -2 := rfl
example : Z.rem 5 (-3) = 2 := rfl
example : Z.modulo 7 0 = 7 := rfl
example : Z.rem 7 0 = 7 := rfl

-- Coq integers use infinite two's-complement bit operations.
example : Z.land 5 6 = 4 := rfl
example : Z.lor 5 6 = 7 := rfl
example : Z.lxor 5 6 = 3 := rfl
example : Z.ldiff 5 6 = 1 := rfl
example : Z.land (-5) 6 = 2 := rfl
example : Z.lor (-5) 6 = -1 := rfl
example : Z.lxor (-5) 6 = -3 := rfl
example : Z.ldiff (-5) 6 = -7 := rfl
example : Z.land 6 (-5) = 2 := rfl
example : Z.lor 6 (-5) = -1 := rfl
example : Z.lxor 6 (-5) = -3 := rfl
example : Z.ldiff 6 (-5) = 4 := rfl
example : Z.land (-5) (-3) = -7 := rfl
example : Z.lor (-5) (-3) = -1 := rfl
example : Z.lxor (-5) (-3) = 6 := rfl
example : Z.ldiff (-5) (-3) = 2 := rfl
example : Z.lnot 0 = -1 := rfl
example : Z.lnot (-1) = 0 := rfl
example : Z.lnot 5 = -6 := rfl
example : Z.lnot (-5) = 4 := rfl
example : Z.testbit 5 0 = true := rfl
example : Z.testbit 5 1 = false := rfl
example : Z.testbit 5 2 = true := rfl
example : Z.testbit 5 40 = false := rfl
example : Z.testbit (-5) 0 = true := rfl
example : Z.testbit (-5) 1 = true := rfl
example : Z.testbit (-5) (-1) = false := rfl
example : Z.ones (-1) = -1 := rfl
example : Z.ones 4 = 15 := rfl

example : Byte.wordsize = 8 := rfl
example : Byte.modulus = 256 := rfl
example : Byte.half_modulus = 128 := rfl
example : Byte.min_signed = -128 := rfl
example : Byte.max_signed = 127 := rfl
example : Byte.max_unsigned = 255 := rfl

example : Int.wordsize = 32 := rfl
example : Int.min_signed = -2147483648 := rfl
example : Int.max_signed = 2147483647 := rfl
example : Int.max_unsigned = 4294967295 := rfl

example : Int64.wordsize = 64 := rfl
example : Int64.min_signed = -9223372036854775808 := rfl
example : Int64.max_signed = 9223372036854775807 := rfl
example : Int64.max_unsigned = 18446744073709551615 := rfl

example : Byte.cast_unsigned (-1) = 255 := rfl
example : Byte.cast_unsigned 256 = 0 := rfl
example : Byte.cast_signed 127 = 127 := rfl
example : Byte.cast_signed 128 = -128 := rfl
example : Byte.cast_signed 255 = -1 := rfl
example : Byte.unsigned (Byte.repr (-1)) = Byte.max_unsigned := by native_decide
example : Byte.signed (Byte.repr 127) = 127 := by native_decide
example : Byte.signed (Byte.repr 128) = -128 := by native_decide
example : Byte.eqm (-17) (Byte.signed (Byte.repr (-17))) :=
  Byte.eqm_signed_repr (-17)
example : Byte.min_signed <= Byte.signed (Byte.repr 255) ∧
    Byte.signed (Byte.repr 255) <= Byte.max_signed :=
  Byte.signed_range (Byte.repr 255)
example : Int.cast_unsigned (-1) = 4294967295 := rfl
example : Int.cast_signed 4294967295 = -1 := rfl
example : Int.cast_signed 2147483647 = 2147483647 := rfl
example : Int.cast_signed 2147483648 = -2147483648 := rfl
example : Int.cast_unsigned (-2147483648) = 2147483648 := rfl
example : Int.cast_signed (-2147483648) = -2147483648 := rfl
example : Int.cast_unsigned (-4294967297) = 4294967295 := rfl
example : Int.cast_signed (-4294967297) = -1 := rfl
example : Int64.cast_unsigned (-1) = 18446744073709551615 := rfl
example : Int64.cast_signed 18446744073709551615 = -1 := rfl
example : Int64.cast_signed 9223372036854775807 = 9223372036854775807 := rfl
example : Int64.cast_signed 9223372036854775808 = -9223372036854775808 := rfl
example : Int64.cast_unsigned (-9223372036854775808) = 9223372036854775808 := rfl
example : Int64.cast_signed (-9223372036854775808) = -9223372036854775808 := rfl
example : Int64.cast_unsigned (-18446744073709551617) = 18446744073709551615 := rfl
example : Int64.cast_signed (-18446744073709551617) = -1 := rfl

example : Int64.unsigned (Int64.repr (-1)) = Int64.max_unsigned := by native_decide
example : Int64.unsigned (Int64.repr Int64.modulus) = 0 := by native_decide
example : Int64.signed (Int64.repr Int64.max_signed) = Int64.max_signed := by
  native_decide
example : Int64.signed (Int64.repr Int64.half_modulus) = Int64.min_signed := by
  native_decide
example : Int64.repr (Int64.unsigned (Int64.repr 17)) = Int64.repr 17 :=
  Int64.repr_unsigned _
example : Int64.repr (Int64.signed (Int64.repr (-17))) = Int64.repr (-17) :=
  Int64.repr_signed _
example : Int64.unsigned
    (CompCert.Int64.add (Int64.repr Int64.max_unsigned) Int64.one) = 0 := by
  native_decide
example : Int64.signed (CompCert.Int64.sub Int64.zero Int64.one) = -1 := by
  native_decide
example : Int64.signed (CompCert.Int64.mul (Int64.repr (-7)) (Int64.repr 6)) = -42 := by
  native_decide
example : Int64.unsigned (Int64.divu (Int64.repr 10) (Int64.repr 3)) = 3 := by
  native_decide
example : Int64.signed (Int64.divs (Int64.repr (-10)) (Int64.repr 3)) = -3 := by
  native_decide
example : Int64.unsigned (Int64.modu (Int64.repr 10) (Int64.repr 3)) = 1 := by
  native_decide
example : Int64.unsigned (Int64.and (Int64.repr 6) (Int64.repr 3)) = 2 := by
  native_decide
example : Int64.unsigned (Int64.or (Int64.repr 4) (Int64.repr 3)) = 7 := by
  native_decide
example : Int64.unsigned (Int64.shl Int64.one (Int64.repr 5)) = 32 := by
  native_decide
example : Int64.signed (Int64.shr (Int64.repr (-16)) (Int64.repr 2)) = -4 := by
  native_decide
example : Int64.cmpu Clt (Int64.repr 3) (Int64.repr 4) = true := by native_decide

example : Byte.eqm (-1) 255 := by
  exact ⟨-1, by decide⟩

example : Byte.eqm 255 (-1) := by
  exact Byte.eqm_sym (-1) 255 ⟨-1, by decide⟩

example : Byte.eqm 511 255 := by
  exact ⟨1, by decide⟩

example : Byte.eqm 17 17 := Byte.eqm_refl 17
example : Byte.eqm 17 17 := Byte.eqm_refl2 17 17 rfl
example : Byte.eqm (-1) 511 :=
  Byte.eqm_trans (-1) 255 511 ⟨-1, by decide⟩ ⟨-1, by decide⟩

example : Not (Byte.eqm 0 1) := by
  intro h
  have hm := Byte.eqm_mod_eq 0 1 h
  exact (by decide : Not (Z.modulo 0 Byte.modulus = Z.modulo 1 Byte.modulus)) hm

example : Int.eqm 17 17 := Int.eqm_refl 17
example : Int.eqm 17 17 := Int.eqm_refl2 17 17 rfl
example : Int.eqm 4294967295 (-1) :=
  Int.eqm_sym (-1) 4294967295 ⟨-1, by decide⟩
example : Int.eqm (-1) 8589934591 :=
  Int.eqm_trans (-1) 4294967295 8589934591
    ⟨-1, by decide⟩ ⟨-1, by decide⟩
example : Z.modulo (-1) Int.modulus = Z.modulo 4294967295 Int.modulus :=
  Int.eqm_mod_eq (-1) 4294967295 ⟨-1, by decide⟩

example : Int64.eqm 17 17 := Int64.eqm_refl 17
example : Int64.eqm 17 17 := Int64.eqm_refl2 17 17 rfl
example : Int64.eqm 18446744073709551615 (-1) :=
  Int64.eqm_sym (-1) 18446744073709551615 ⟨-1, by decide⟩
example : Int64.eqm (-1) 36893488147419103231 :=
  Int64.eqm_trans (-1) 18446744073709551615 36893488147419103231
    ⟨-1, by decide⟩ ⟨-1, by decide⟩
example : Z.modulo (-1) Int64.modulus =
    Z.modulo 18446744073709551615 Int64.modulus :=
  Int64.eqm_mod_eq (-1) 18446744073709551615 ⟨-1, by decide⟩

example : Z.land (Z.land 7 6) 5 = Z.land 7 (Z.land 6 5) :=
  (Z.land_assoc 7 6 5).symm
example : Z.land 7 (Z.ones 3) = Z.modulo 7 (Z.pow 2 3) :=
  Z.land_ones 7 3 (by decide)
example : Z.modulo (Z.ones 8) (Z.pow 2 3) = Z.ones 3 :=
  Z.ones_mod_pow2 8 3 (by decide)
example : Z.testbit (Z.modulo (-5) (Z.pow 2 4)) 2 = Z.testbit (-5) 2 :=
  Z.mod_pow2_bits_low (-5) 4 2 (by decide)
example : Z.testbit (Z.modulo (-5) (Z.pow 2 4)) 7 = false :=
  Z.mod_pow2_bits_high (-5) 4 7 (by decide)
example : Z.testbit 15 7 = false :=
  Zbits.Ztestbit_above 4 15 7 (by decide) (by decide)
example : Z.testbit (-(two_p 4)) 7 = true :=
  Zbits.Ztestbit_neg_two_p 4 7 (by decide) (by decide)
example : Z.testbit (1 + 2) 1 = (Z.testbit 1 1 || Z.testbit 2 1) := by
  apply Zbits.Z_add_is_or 1 (by decide) 1 2
  intro j hj
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl <;> decide
example (x : Int) : x = x := by
  apply Z.bits_inj'
  intro n hn
  rfl
example (n : Int) : two_p n = Z.pow 2 n := two_p_equiv n
example (n : Nat) : two_power_nat n = Z.pow 2 (Int.ofNat n) :=
  two_power_nat_equiv n
example : Z.modulo 513 (16 * 32) =
    Z.modulo (Z.div 513 32) 16 * 32 + Z.modulo 513 32 :=
  Zmod_recombine 513 16 32 (by decide) (by decide)
example : Z.quot 0 (-7) = 0 := Z.quot_0_l (-7) (by decide)
example : Z.quot 7 8 = 0 := (Z.quot_small_iff 7 8 (by decide)).mpr (by decide)
example : Z.gcd (-12) 0 = 12 := Z.gcd_0_r (-12)
example : Z.gcd (Z.rem 17 5) 5 = Z.gcd 5 17 :=
  Z.gcd_rem 17 5 (by decide)
example : 0 <= Z.rem 17 5 ∧ Z.rem 17 5 < 5 :=
  Z.rem_bound_pos_pos 17 5 (by decide) (by decide)
example : 0 <= Z.rem 17 (-5) ∧ Z.rem 17 (-5) < 5 :=
  Z.rem_bound_neg_pos 17 (-5) (by decide) (by decide)
example : -5 < Z.rem (-17) 5 ∧ Z.rem (-17) 5 <= 0 :=
  Z.rem_bound_pos_neg (-17) 5 (by decide) (by decide)
example : -5 < Z.rem (-17) (-5) ∧ Z.rem (-17) (-5) <= 0 :=
  Z.rem_bound_neg_neg (-17) (-5) (by decide) (by decide)
example : Z.abs (-17) = 17 := by decide
example : Z.abs (-17) <= 20 ↔ -20 <= (-17 : Int) ∧ (-17 : Int) <= 20 :=
  Z.abs_le_iff (-17) 20
example : Z.quot 17 5 = 3 := by decide
example : Z.quot (-17) 5 = -3 := by decide
example : Z.quot 17 (-5) = -3 := by decide
example : Z.quot (-17) (-5) = 3 := by decide
example : Z.quot 17 0 = 0 := rfl
example : Z.quot (-17) 0 = 0 := rfl
example : Z.rem (-17) 0 = -17 := rfl
example : Z.rem 21 7 = 0 ↔ Z.divide 7 21 :=
  Z.rem_divide 21 7 (by decide)
example : Z.gcd 21 14 = 7 := by decide
example : Z.quot (3 * 21) 7 = 3 * Z.quot 21 7 :=
  Z.divide_quot_mul_exact 21 7 3 (by decide) ⟨3, by decide⟩
example : Z.rem (17 * 3) (5 * 3) = Z.rem 17 5 * 3 :=
  Zquot.Zmult_rem_distr_r 17 5 3
example : Z.rem (17 * (-3)) (5 * (-3)) = Z.rem 17 5 * (-3) :=
  Zquot.Zmult_rem_distr_r 17 5 (-3)
example : Z.rem (17 * 0) (5 * 0) = Z.rem 17 5 * 0 :=
  Zquot.Zmult_rem_distr_r 17 5 0
example : Z.quot (17 * (-3)) (5 * (-3)) = Z.quot 17 5 :=
  Zquot.Zquot_mult_cancel_r 17 5 (-3) (by decide)
example : Z.quot (7 + 2 * 3) 3 = Z.quot 7 3 + 2 :=
  Zquot.Z_quot_plus 7 2 3 (by decide) (by decide)
example : Z.quot ((-7) + (-2) * 3) 3 = Z.quot (-7) 3 + (-2) :=
  Zquot.Z_quot_plus (-7) (-2) 3 (by decide) (by decide)
example : Z.quot (7 + 2 * (-3)) (-3) = Z.quot 7 (-3) + 2 :=
  Zquot.Z_quot_plus 7 2 (-3) (by decide) (by decide)
example : Z.quot (0 + 5 * (-3)) (-3) = Z.quot 0 (-3) + 5 :=
  Zquot.Z_quot_plus 0 5 (-3) (by decide) (by decide)

#check Zbits.eqmod
#check Z.abs
#check Z.gcd
#check Z.quot_0_l
#check Z.quot_small_iff
#check Z.quot_le_lower_bound
#check Z.quot_lt_upper_bound
#check Z.quot_le_upper_bound
#check Z.quot_abs
#check Z.rem_abs
#check Z.rem_bound_abs
#check Z.rem_divide
#check Z.divide_quot_mul_exact
#check Z.gcd_0_r
#check Z.gcd_0_l
#check Z.gcd_nonneg
#check Z.gcd_divide_l
#check Z.gcd_divide_r
#check Z.gcd_rem
#check Z.gcd_comm
#check Z.abs_le_iff
#check Z.abs_lt_iff
#check Zquot.Zmult_rem_distr_r
#check Zquot.Zquot_mult_cancel_r
#check Zquot.Z_quot_plus
#check Z.rem_bound_pos_pos
#check Z.rem_bound_neg_pos
#check Z.rem_bound_pos_neg
#check Z.rem_bound_neg_neg
#check Zbits.eqmod_mod
#check Wordsize_8.wordsize_not_zero
#check Wordsize_32.wordsize_not_zero
#check Wordsize_64.wordsize_not_zero
#check Byte.eqm_refl
#check Byte.eqm_refl2
#check Byte.eqm_sym
#check Byte.eqm_trans
#check Byte.eqm_mod_eq
#check Byte.int
#check Byte.unsigned
#check Byte.signed
#check Byte.repr
#check Byte.unsigned_range
#check Byte.signed_range
#check Byte.eqm_signed_unsigned
#check Byte.eqm_signed_repr
#check Zmod_recombine
#check Z.land_assoc
#check Z.bits_inj'
#check Z.land_comm
#check Z.land_diag
#check Z.land_spec
#check Z.lor_spec
#check Z.lxor_spec
#check Z.ldiff_spec
#check Z.land_ones
#check Z.ones_mod_pow2
#check Z.mod_pow2_bits_low
#check Z.mod_pow2_bits_high
#check Zbits.Z_add_is_or
#check Zbits.Zquot_Zdiv
#check Zbits.Ztestbit_above
#check Zbits.Ztestbit_neg_two_p
#check two_p_equiv
#check two_power_nat_equiv
#check Int.eqm_refl
#check Int.eqm_refl2
#check Int.eqm_sym
#check Int.eqm_trans
#check Int.eqm_mod_eq
#check Int64.eqm_refl
#check Int64.eqm_refl2
#check Int64.eqm_sym
#check Int64.eqm_trans
#check Int64.eqm_mod_eq
#check Int.cast_unsigned
#check Int.cast_signed
#check Int64.cast_unsigned
#check Int64.cast_signed
#check Int64.int
#check Int64.unsigned
#check Int64.signed
#check Int64.repr
#check Int64.ltu
#check Int64.divs
#check Int64.divu
#check Int64.modu
#check Int64.shl
#check Int64.shr
#check Int64.cmpu
#check Int64.unsigned_range
#check Int64.unsigned_range_2
#check Int64.signed_range
#check Int64.repr_unsigned
#check Int64.repr_signed
#check Int64.unsigned_repr
#check Int64.signed_repr
#check CompCert.Int64.add
#check CompCert.Int64.sub
#check CompCert.Int64.mul
#check CompCert.Int64.lt
#check CompCert.Int64.neg
#check CompCert.Int64.xor
#check CompCert.Int64.and_zero

-- Lean core already owns these root `Int64` names for native machine integers.
-- The CompCert word API is therefore intentionally qualified for the collisions.
#check (Int64.add : _root_.Int64 -> _root_.Int64 -> _root_.Int64)
#check (Int64.lt : _root_.Int64 -> _root_.Int64 -> Prop)
#check (CompCert.Int64.add : Int64.int -> Int64.int -> Int64.int)
#check (CompCert.Int64.sub : Int64.int -> Int64.int -> Int64.int)
#check (CompCert.Int64.mul : Int64.int -> Int64.int -> Int64.int)
#check (CompCert.Int64.neg : Int64.int -> Int64.int)
#check (CompCert.Int64.lt : Int64.int -> Int64.int -> Bool)
#check (CompCert.Int64.xor : Int64.int -> Int64.int -> Int64.int)
#check CompCert.Int64.sub_add_cancel
#check CompCert.Int64.and_zero

#print axioms Zbits.eqmod_mod_eq
#print axioms Byte.eqm_mod_eq
#print axioms Z.land_ones
#print axioms Zbits.Z_add_is_or
#print axioms Zbits.Zquot_Zdiv
#print axioms Z.quot_small_iff
#print axioms Z.divide_quot_mul_exact
#print axioms Zquot.Z_quot_plus
#print axioms Z.gcd_rem
#print axioms Z.rem_bound_neg_neg
#print axioms Int64.signed_repr
#print axioms CompCert.Int64.mul_signed
