import Flocq.Core.Core
import Flocq.IEEE754.Binary
import Flocq.IEEE754.Bits
import Flocq.Compatibility.IEEEReal
import compcert.lib.Integers
import Lean.Elab.Tactic.Omega

namespace SimpleC.SL.FloatLib

open CompCert
open Flocq.IEEE754
open Flocq.IEEE754.BinaryFloat
open Flocq.Core

private instance fp32_prec_gt_0 : Prec_gt_0 24 := ⟨by decide⟩
private instance fp32_prec_lt_emax : Prec_lt_emax 24 128 := ⟨by decide⟩
private instance fp64_prec_gt_0 : Prec_gt_0 53 := ⟨by decide⟩
private instance fp64_prec_lt_emax : Prec_lt_emax 53 1024 := ⟨by decide⟩
private instance fp128_prec_gt_0 : Prec_gt_0 113 := ⟨by decide⟩
private instance fp128_prec_lt_emax : Prec_lt_emax 113 16384 := ⟨by decide⟩

abbrev fp32 : Type := binary32
abbrev fp64 : Type := binary64
abbrev fp128 : Type := binary_float 113 16384

def fp32_nan_payload : Nat := 1
theorem fp32_nan_payload_valid :
    nan_pl 24 fp32_nan_payload = true := by decide

def fp64_nan_payload : Nat := 1
theorem fp64_nan_payload_valid :
    nan_pl 53 fp64_nan_payload = true := by decide

def fp128_nan_payload : Nat := 1
theorem fp128_nan_payload_valid :
    nan_pl 113 fp128_nan_payload = true := by decide

def fp32_nan : fp32 := nan binary32Format false fp32_nan_payload
def fp64_nan : fp64 := nan binary64Format false fp64_nan_payload
def fp128_nan : fp128 := nan binary128Format false fp128_nan_payload

def fp32_unary_nan (_ : fp32) : {x : fp32 // is_nan 24 128 x = true} :=
  ⟨fp32_nan, by decide⟩

def fp64_unary_nan (_ : fp64) : {x : fp64 // is_nan 53 1024 x = true} :=
  ⟨fp64_nan, by decide⟩

def fp128_unary_nan (_ : fp128) : {x : fp128 // is_nan 113 16384 x = true} :=
  ⟨fp128_nan, by decide⟩

def fp32_binary_nan (_ _ : fp32) : {x : fp32 // is_nan 24 128 x = true} :=
  ⟨fp32_nan, by decide⟩

def fp64_binary_nan (_ _ : fp64) : {x : fp64 // is_nan 53 1024 x = true} :=
  ⟨fp64_nan, by decide⟩

def fp128_binary_nan (_ _ : fp128) : {x : fp128 // is_nan 113 16384 x = true} :=
  ⟨fp128_nan, by decide⟩

def fp32_add : fp32 -> fp32 -> fp32 :=
  Bplus 24 128 inferInstance inferInstance fp32_binary_nan mode_NE
def fp32_sub : fp32 -> fp32 -> fp32 :=
  Bminus 24 128 inferInstance inferInstance fp32_binary_nan mode_NE
def fp32_mul : fp32 -> fp32 -> fp32 :=
  Bmult 24 128 inferInstance inferInstance fp32_binary_nan mode_NE
def fp32_div : fp32 -> fp32 -> fp32 :=
  Bdiv 24 128 inferInstance inferInstance fp32_binary_nan mode_NE
def fp32_neg : fp32 -> fp32 := Bopp 24 128 fp32_unary_nan

def fp64_add : fp64 -> fp64 -> fp64 :=
  Bplus 53 1024 inferInstance inferInstance fp64_binary_nan mode_NE
def fp64_sub : fp64 -> fp64 -> fp64 :=
  Bminus 53 1024 inferInstance inferInstance fp64_binary_nan mode_NE
def fp64_mul : fp64 -> fp64 -> fp64 :=
  Bmult 53 1024 inferInstance inferInstance fp64_binary_nan mode_NE
def fp64_div : fp64 -> fp64 -> fp64 :=
  Bdiv 53 1024 inferInstance inferInstance fp64_binary_nan mode_NE
def fp64_neg : fp64 -> fp64 := Bopp 53 1024 fp64_unary_nan

def fp128_add : fp128 -> fp128 -> fp128 :=
  Bplus 113 16384 inferInstance inferInstance fp128_binary_nan mode_NE
def fp128_sub : fp128 -> fp128 -> fp128 :=
  Bminus 113 16384 inferInstance inferInstance fp128_binary_nan mode_NE
def fp128_mul : fp128 -> fp128 -> fp128 :=
  Bmult 113 16384 inferInstance inferInstance fp128_binary_nan mode_NE
def fp128_div : fp128 -> fp128 -> fp128 :=
  Bdiv 113 16384 inferInstance inferInstance fp128_binary_nan mode_NE
def fp128_neg : fp128 -> fp128 := Bopp 113 16384 fp128_unary_nan

def fp32_isFinite (x : fp32) : Prop := is_finite 24 128 x = true
def fp64_isFinite (x : fp64) : Prop := is_finite 53 1024 x = true
def fp128_isFinite (x : fp128) : Prop := is_finite 113 16384 x = true

def fp32_isNaN (x : fp32) : Prop := is_nan 24 128 x = true
def fp64_isNaN (x : fp64) : Prop := is_nan 53 1024 x = true
def fp128_isNaN (x : fp128) : Prop := is_nan 113 16384 x = true

def fp32_isInf (x : fp32) : Prop := isInfBool x = true
def fp64_isInf (x : fp64) : Prop := isInfBool x = true
def fp128_isInf (x : fp128) : Prop := isInfBool x = true

def fp32_compare : fp32 -> fp32 -> Option Ordering := Bcompare 24 128
def fp64_compare : fp64 -> fp64 -> Option Ordering := Bcompare 53 1024
def fp128_compare : fp128 -> fp128 -> Option Ordering := Bcompare 113 16384

def fp32_eq (x y : fp32) : Prop := fp32_compare x y = some .eq
def fp32_ne (x y : fp32) : Prop := fp32_compare x y ≠ some .eq
def fp32_lt (x y : fp32) : Prop := fp32_compare x y = some .lt
def fp32_le (x y : fp32) : Prop :=
  match fp32_compare x y with
  | some .lt | some .eq => True
  | _ => False
def fp32_gt (x y : fp32) : Prop := fp32_compare x y = some .gt
def fp32_ge (x y : fp32) : Prop :=
  match fp32_compare x y with
  | some .gt | some .eq => True
  | _ => False

def fp64_eq (x y : fp64) : Prop := fp64_compare x y = some .eq
def fp64_ne (x y : fp64) : Prop := fp64_compare x y ≠ some .eq
def fp64_lt (x y : fp64) : Prop := fp64_compare x y = some .lt
def fp64_le (x y : fp64) : Prop :=
  match fp64_compare x y with
  | some .lt | some .eq => True
  | _ => False
def fp64_gt (x y : fp64) : Prop := fp64_compare x y = some .gt
def fp64_ge (x y : fp64) : Prop :=
  match fp64_compare x y with
  | some .gt | some .eq => True
  | _ => False

def fp128_eq (x y : fp128) : Prop := fp128_compare x y = some .eq
def fp128_ne (x y : fp128) : Prop := fp128_compare x y ≠ some .eq
def fp128_lt (x y : fp128) : Prop := fp128_compare x y = some .lt
def fp128_le (x y : fp128) : Prop :=
  match fp128_compare x y with
  | some .lt | some .eq => True
  | _ => False
def fp128_gt (x y : fp128) : Prop := fp128_compare x y = some .gt
def fp128_ge (x y : fp128) : Prop :=
  match fp128_compare x y with
  | some .gt | some .eq => True
  | _ => False

def fp32_of_bits (z : Int) : fp32 := b32_of_bits z
def fp64_of_bits (z : Int) : fp64 := b64_of_bits z
def fp128_of_bits (z : Int) : fp128 :=
  binary_float_of_bits 112 15 (by decide) (by decide) (by decide) z

def bits_of_fp32 (x : fp32) : Int := bits_of_b32 x
def bits_of_fp64 (x : fp64) : Int := bits_of_b64 x
def bits_of_fp128 (x : fp128) : Int := bits_of_binary_float 112 15 x

def bits_of_float_value (x : fp32) : Option Int := some (bits_of_fp32 x)
def bits_of_double_value (x : fp64) : Option Int := some (bits_of_fp64 x)
def bits_of_long_double_value (x : fp128) : Option Int := some (bits_of_fp128 x)

def max_unsigned_128 : Int := Z.pow 2 128 - 1

theorem bits_of_float_value_range :
    forall v z, bits_of_float_value v = some z -> 0 <= z ∧ z <= Int.max_unsigned := by
  intro v z h
  simp only [bits_of_float_value, Option.some.injEq] at h
  subst z
  constructor
  · exact (bits_of_binary_float_range 23 8 (by decide) (by decide) v).1
  · have hlt := (bits_of_binary_float_range 23 8
      (by decide) (by decide) v).2
    change bits_of_fp32 v < 4294967296 at hlt
    change bits_of_fp32 v <= 4294967295
    omega

theorem bits_of_double_value_range :
    forall v z, bits_of_double_value v = some z -> 0 <= z ∧ z <= Int64.max_unsigned := by
  intro v z h
  simp only [bits_of_double_value, Option.some.injEq] at h
  subst z
  constructor
  · exact (bits_of_binary_float_range 52 11 (by decide) (by decide) v).1
  · have hlt := (bits_of_binary_float_range 52 11
      (by decide) (by decide) v).2
    change bits_of_fp64 v < 18446744073709551616 at hlt
    change bits_of_fp64 v <= 18446744073709551615
    omega

theorem bits_of_long_double_value_range :
    forall v z, bits_of_long_double_value v = some z ->
      0 <= z ∧ z <= max_unsigned_128 := by
  intro v z h
  simp only [bits_of_long_double_value, Option.some.injEq] at h
  subst z
  constructor
  · exact (bits_of_binary_float_range 112 15 (by decide) (by decide) v).1
  · have hlt := (bits_of_binary_float_range 112 15
      (by decide) (by decide) v).2
    set_option maxRecDepth 100000 in
      change bits_of_fp128 v < 340282366920938463463374607431768211456 at hlt
    change bits_of_fp128 v <= max_unsigned_128
    have hmax : max_unsigned_128 = 340282366920938463463374607431768211455 := by
      set_option maxRecDepth 100000 in
        rfl
    rw [hmax]
    omega

def fexp32 : Int -> Int := FLT_exp (-149) 24
def fexp64 : Int -> Int := FLT_exp (-1074) 53
def fexp128 : Int -> Int := FLT_exp (-16494) 113

noncomputable def rounded32 (m : mode) (r : Real) : Real :=
  Flocq.Compatibility.IEEEReal.implementation_round fexp32 m r

noncomputable def rounded64 (m : mode) (r : Real) : Real :=
  Flocq.Compatibility.IEEEReal.implementation_round fexp64 m r

noncomputable def rounded128 (m : mode) (r : Real) : Real :=
  Flocq.Compatibility.IEEEReal.implementation_round fexp128 m r

def in_float32_range (m : mode) (r : Real) : Prop :=
  |rounded32 m r| < bpow radix2 128

def in_float64_range (m : mode) (r : Real) : Prop :=
  |rounded64 m r| < bpow radix2 1024

def in_float128_range (m : mode) (r : Real) : Prop :=
  |rounded128 m r| < bpow radix2 16384

theorem rounded32_generic :
    forall m r, generic_format radix2 fexp32 (rounded32 m r) := by
  intro m r
  simpa [fexp32, rounded32] using
    Flocq.Compatibility.IEEEReal.round_FLT_generic_format
      (-149) 24 (by decide) m r

theorem rounded64_generic :
    forall m r, generic_format radix2 fexp64 (rounded64 m r) := by
  intro m r
  simpa [fexp64, rounded64] using
    Flocq.Compatibility.IEEEReal.round_FLT_generic_format
      (-1074) 53 (by decide) m r

theorem rounded128_generic :
    forall m r, generic_format radix2 fexp128 (rounded128 m r) := by
  intro m r
  simpa [fexp128, rounded128] using
    Flocq.Compatibility.IEEEReal.round_FLT_generic_format
      (-16494) 113 (by decide) m r

noncomputable def fp32_of_real (r : Real) : fp32 :=
  let rr := rounded32 mode_NE r
  binary_normalize 24 128 inferInstance inferInstance mode_NE
    (Ztrunc (scaled_mantissa radix2 fexp32 rr))
    (cexp radix2 fexp32 rr) (decide (r < 0))

noncomputable def fp64_of_real (r : Real) : fp64 :=
  let rr := rounded64 mode_NE r
  binary_normalize 53 1024 inferInstance inferInstance mode_NE
    (Ztrunc (scaled_mantissa radix2 fexp64 rr))
    (cexp radix2 fexp64 rr) (decide (r < 0))

noncomputable def fp128_of_real (r : Real) : fp128 :=
  let rr := rounded128 mode_NE r
  binary_normalize 113 16384 inferInstance inferInstance mode_NE
    (Ztrunc (scaled_mantissa radix2 fexp128 rr))
    (cexp radix2 fexp128 rr) (decide (r < 0))

noncomputable def fp32_of_Z (z : Int) : fp32 := fp32_of_real (z : Real)
noncomputable def fp64_of_Z (z : Int) : fp64 := fp64_of_real (z : Real)
noncomputable def fp128_of_Z (z : Int) : fp128 := fp128_of_real (z : Real)

noncomputable abbrev Z_to_fp32 := fp32_of_Z
noncomputable abbrev Z_to_fp64 := fp64_of_Z
noncomputable abbrev Z_to_fp128 := fp128_of_Z

noncomputable def fp32_to_R (x : fp32) : Option Real :=
  if is_finite 24 128 x then some (B2R 24 128 x) else none

noncomputable def fp64_to_R (x : fp64) : Option Real :=
  if is_finite 53 1024 x then some (B2R 53 1024 x) else none

noncomputable def fp128_to_R (x : fp128) : Option Real :=
  if is_finite 113 16384 x then some (B2R 113 16384 x) else none

noncomputable def fp32_to_R_total (x : fp32) : Real :=
  B2R 24 128 x

noncomputable def fp64_to_R_total (x : fp64) : Real :=
  B2R 53 1024 x

noncomputable def fp128_to_R_total (x : fp128) : Real :=
  B2R 113 16384 x

def fp32_zero : fp32 := fp32_of_bits 0
def fp32_neg_zero : fp32 := fp32_of_bits 2147483648
def fp64_zero : fp64 := fp64_of_bits 0
def fp64_neg_zero : fp64 := fp64_of_bits 9223372036854775808
def fp128_zero : fp128 := fp128_of_bits 0
def fp128_neg_zero : fp128 := fp128_of_bits (Z.pow 2 127)

def fp32_pos_infinity : fp32 := infinity binary32Format false
def fp32_neg_infinity : fp32 := infinity binary32Format true
def fp64_pos_infinity : fp64 := infinity binary64Format false
def fp64_neg_infinity : fp64 := infinity binary64Format true
def fp128_pos_infinity : fp128 := infinity binary128Format false
def fp128_neg_infinity : fp128 := infinity binary128Format true

def FLT_MAX : fp32 := fp32_of_bits 2139095039
def FLT_MIN : fp32 := fp32_of_bits 8388608
def DBL_MAX : fp64 := fp64_of_bits 9218868437227405311
def DBL_MIN : fp64 := fp64_of_bits 4503599627370496
def LDBL_MAX : fp128 := fp128_of_bits (Z.pow 2 127 - Z.pow 2 112)
def LDBL_MIN : fp128 := fp128_of_bits (Z.pow 2 112)

end SimpleC.SL.FloatLib
