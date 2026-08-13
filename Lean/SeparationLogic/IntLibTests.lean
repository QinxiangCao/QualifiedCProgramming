import SimpleC.SL.IntLib

open SimpleC.SL.IntLib

-- Source definitions and notation-level constants.
#check INT_MIN
#check INT_MAX
#check UINT_MAX
#check Zabs
#check Zgcd
#check unsigned_last_nbits
#check signed_last_nbits

-- All 89 Coq lemmas/theorems.
#check Zland_land
#check Byte_cast_correct
#check UByte_cast_correct
#check Int_cast_correct
#check UInt_cast_correct
#check Int64_cast_correct
#check UInt64_cast_correct
#check unsigned_Lastnbits_mod_correct
#check signed_Lastnbits_mod_correct
#check unsigned_Lastnbits_range
#check signed_Lastnbits_range
#check unsigned_last_nbits_eq
#check signed_last_nbits_eq
#check Int_signed_eq
#check UInt_unsigned_eq
#check Int64_signed_eq
#check UInt64_unsigned_eq
#check unsigned_unsigned_add_l
#check unsigned_unsigned_add_r
#check unsigned_unsigned_sub_l
#check unsigned_unsigned_sub_r
#check unsigned_unsigned_mul_l
#check unsigned_unsigned_mul_r
#check unsigned_unsigned_mul_l_add_other
#check unsigned_unsigned_mul_r_add_other
#check unsigned_unsigned_add_mul_l_other
#check unsigned_unsigned_add_mul_r_other
#check unsigned_unsigned_sub_mul_l_other
#check unsigned_unsigned_sub_mul_r_other
#check unsigned_unsigned_mul_l_sub_other
#check unsigned_unsigned_mul_r_sub_other
#check unsigned_unsigned_mul_l_mul_other
#check unsigned_unsigned_mul_r_mul_other
#check unsigned_unsigned_add_l_sub_other
#check unsigned_unsigned_add_r_sub_other
#check unsigned_unsigned_add_l_add_other
#check unsigned_unsigned_add_r_add_other
#check unsigned_revolutive
#check Pow2Mod_less
#check Pow2Mod_greater
#check unsigned_revolutive_less
#check unsigned_revolutive_greater
#check signed_revolutive
#check Pow2Mod_zero
#check Pow2Mod_self
#check signed_revolutive_less
#check signed_revolutive_greater
#check signed_unsigned_revolutive
#check signed_unsigned_revolutive_less
#check signed_unsigned_revolutive_greater
#check unsigned_signed_revolutive
#check unsigned_signed_revolutive_less
#check unsigned_signed_revolutive_greater_pos
#check unsigned_signed_revolutive_greater_neg
#check signed_unsigned_sub_l
#check signed_unsigned_sub_r
#check signed_unsigned_add_l
#check signed_unsigned_add_r
#check signed_unsigned_mul_l
#check signed_unsigned_mul_r
#check signed_signed_add_r
#check signed_signed_add_l
#check signed_signed_sub_r
#check signed_signed_sub_l
#check signed_signed_mul_l
#check signed_signed_mul_r
#check unsigned_signed_add_l
#check unsigned_signed_add_r
#check unsigned_signed_sub_l
#check unsigned_signed_sub_r
#check unsigned_signed_mul_l
#check unsigned_signed_mul_r
#check Ztestbits_unsigned_eq
#check Ztestbits_unsigned_high
#check Ztestbits_signed_eq
#check Ztestbits_signed_high_lt
#check Ztestbits_signed_high_ge
#check Ztestbits_signed_high
#check unsigned_last_nbits_land_distr
#check unsigned_last_nbits_lor_distr
#check unsigned_last_nbits_ldiff_distr
#check unsigned_last_nbits_lxor_distr
#check unsigned_last_nbits_land_missing_l
#check unsigned_last_nbits_land_missing_r
#check unsigned_last_nbits_land_clear_l
#check unsigned_last_nbits_land_clear_r
#check unsigned_last_nbits_lor_distr_missing
#check unsigned_last_nbits_ldiff_distr_missing_l
#check unsigned_last_nbits_lxor_distr_missing

-- Representative normalization and boundary behavior.
example : unsigned_last_nbits (-1) 8 = 255 := by native_decide
example : signed_last_nbits 255 8 = -1 := by native_decide
example : signed_last_nbits 128 8 = -128 := by native_decide
example : unsigned_last_nbits 511 8 = 255 := by native_decide
example : unsigned_last_nbits 37 (-1) = 37 := by native_decide
example : signed_last_nbits 37 (-1) = 37 := by native_decide
example : Z.rem (-5) 3 = -2 := by native_decide

-- Every migrated Ltac entry point retains a Lean tactic call form.
example (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (unsigned_last_nbits x n + y) n =
      unsigned_last_nbits (x + y) n := by
  unsigned_unsigned_simpl

example (x y n : Int) (hn : n > 0) :
    signed_last_nbits (signed_last_nbits x n - y) n =
      signed_last_nbits (x - y) n := by
  signed_signed_simpl

example (x y n : Int) (hn : n > 0) :
    unsigned_last_nbits (signed_last_nbits x n * y) n =
      unsigned_last_nbits (x * y) n := by
  unsigned_signed_simpl

example (x y n : Int) (hn : n > 0) :
    signed_last_nbits (x + unsigned_last_nbits y n) n =
      signed_last_nbits (x + y) n := by
  signed_unsigned_simpl

example (x y n : Int) (hn : n > 0) :
    signed_last_nbits
      (unsigned_last_nbits (signed_last_nbits x n + y) n) n =
      signed_last_nbits (x + y) n := by
  lastnbits_simpl

example (x n : Int) (hx : 0 <= x ∧ x < Z.pow 2 n) :
    unsigned_last_nbits x n = x := by
  lastnbits_eq_step unsigned_last_nbits x n

example (x n : Int) (hn : n > 0)
    (hx : -Z.pow 2 (n - 1) <= x ∧ x < Z.pow 2 (n - 1)) :
    signed_last_nbits x n = x := by
  lastnbits_eq

-- Bitwise distribution and sign extension smoke tests.
example : unsigned_last_nbits (Z.land (-1) 170) 8 = 170 := by native_decide
example : Z.testbit (signed_last_nbits 128 8) 12 = true := by native_decide
example : Z.testbit (unsigned_last_nbits (-1) 8) 12 = false := by native_decide

#print axioms unsigned_Lastnbits_range
#print axioms signed_last_nbits_eq
#print axioms unsigned_last_nbits_land_distr
