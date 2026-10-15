import SimpleC.SL.FloatLib
import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum

namespace FloatLibTests

open SimpleC.SL.FloatLib
open Flocq.IEEE754
open Flocq.IEEE754.BinaryFloat
open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "FloatLib API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkFloatLibApiContract)
  "#check_floatlib_api_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_floatlib_api_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "FloatLib API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "FloatLib declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"FloatLib API contract verified for {names.size} declarations"

#check fp32
#check fp64
#check fp128
#check fp32_nan_payload_valid
#check fp64_nan_payload_valid
#check fp128_nan_payload_valid
#check fp32_unary_nan
#check fp64_binary_nan
#check fp128_binary_nan
#check fp32_add
#check fp32_sub
#check fp32_mul
#check fp32_div
#check fp32_neg
#check fp64_add
#check fp64_sub
#check fp64_mul
#check fp64_div
#check fp64_neg
#check fp128_add
#check fp128_sub
#check fp128_mul
#check fp128_div
#check fp128_neg
#check fp32_isFinite
#check fp64_isNaN
#check fp128_isInf
#check fp32_compare
#check fp64_le
#check fp128_ge
#check fp32_of_bits
#check fp64_of_bits
#check fp128_of_bits
#check bits_of_fp32
#check bits_of_float_value
#check bits_of_float_value_range
#check bits_of_double_value_range
#check bits_of_long_double_value_range
#check fexp32
#check fexp64
#check fexp128
#check rounded32
#check rounded64
#check rounded128
#check in_float32_range
#check in_float64_range
#check in_float128_range
#check rounded32_generic
#check rounded64_generic
#check rounded128_generic
#check fp32_of_real
#check fp64_of_real
#check fp128_of_real
#check fp32_of_Z
#check Z_to_fp64
#check fp32_to_R
#check fp64_to_R
#check fp128_to_R
#check fp32_to_R_total
#check fp64_to_R_total
#check fp128_to_R_total
#check fp128_neg_zero
#check fp32_pos_infinity
#check DBL_MAX
#check LDBL_MIN

#check Flocq.IEEE754.Bplus
#check Flocq.IEEE754.binary_normalize
#check Flocq.IEEE754.bits_of_binary_float
#check Flocq.IEEE754.binary_float_of_bits

#check_floatlib_api_contract [
  fp32, fp64, fp128,
  fp32_nan_payload, fp32_nan_payload_valid,
  fp64_nan_payload, fp64_nan_payload_valid,
  fp128_nan_payload, fp128_nan_payload_valid,
  fp32_nan, fp64_nan, fp128_nan,
  fp32_unary_nan, fp64_unary_nan, fp128_unary_nan,
  fp32_binary_nan, fp64_binary_nan, fp128_binary_nan,
  fp32_add, fp32_sub, fp32_mul, fp32_div, fp32_neg,
  fp64_add, fp64_sub, fp64_mul, fp64_div, fp64_neg,
  fp128_add, fp128_sub, fp128_mul, fp128_div, fp128_neg,
  fp32_isFinite, fp64_isFinite, fp128_isFinite,
  fp32_isNaN, fp64_isNaN, fp128_isNaN,
  fp32_isInf, fp64_isInf, fp128_isInf,
  fp32_compare, fp64_compare, fp128_compare,
  fp32_eq, fp32_ne, fp32_lt, fp32_le, fp32_gt, fp32_ge,
  fp64_eq, fp64_ne, fp64_lt, fp64_le, fp64_gt, fp64_ge,
  fp128_eq, fp128_ne, fp128_lt, fp128_le, fp128_gt, fp128_ge,
  fp32_of_bits, fp64_of_bits, fp128_of_bits,
  bits_of_fp32, bits_of_fp64, bits_of_fp128,
  bits_of_float_value, bits_of_double_value, bits_of_long_double_value,
  max_unsigned_128,
  bits_of_float_value_range, bits_of_double_value_range,
  bits_of_long_double_value_range,
  fexp32, fexp64, fexp128,
  rounded32, rounded64, rounded128,
  in_float32_range, in_float64_range, in_float128_range,
  rounded32_generic, rounded64_generic, rounded128_generic,
  fp32_of_real, fp64_of_real, fp128_of_real,
  fp32_of_Z, fp64_of_Z, fp128_of_Z,
  Z_to_fp32, Z_to_fp64, Z_to_fp128,
  fp32_to_R, fp64_to_R, fp128_to_R,
  fp32_to_R_total, fp64_to_R_total, fp128_to_R_total,
  fp32_zero, fp32_neg_zero, fp64_zero, fp64_neg_zero,
  fp128_zero, fp128_neg_zero,
  fp32_pos_infinity, fp32_neg_infinity,
  fp64_pos_infinity, fp64_neg_infinity,
  fp128_pos_infinity, fp128_neg_infinity,
  FLT_MAX, FLT_MIN, DBL_MAX, DBL_MIN, LDBL_MAX, LDBL_MIN
] => 3584120699663807483

section KernelCompatibilityTests

set_option maxRecDepth 100000

theorem fp32_of_bits_neg_one :
    bits_of_fp32 (fp32_of_bits (-1)) = 2147483647 := by decide
theorem fp32_of_bits_width :
    bits_of_fp32 (fp32_of_bits 4294967296) = 2147483648 := by decide
theorem fp32_of_bits_double_width_pred :
    bits_of_fp32 (fp32_of_bits 8589934591) = 4294967295 := by decide
theorem fp64_of_bits_neg_one :
    bits_of_fp64 (fp64_of_bits (-1)) = 9223372036854775807 := by decide
theorem fp64_of_bits_width :
    bits_of_fp64 (fp64_of_bits 18446744073709551616) =
      9223372036854775808 := by decide
theorem fp64_of_bits_double_width_pred :
    bits_of_fp64 (fp64_of_bits 36893488147419103231) =
      18446744073709551615 := by decide
theorem fp128_of_bits_neg_one :
    bits_of_fp128 (fp128_of_bits (-1)) = Z.pow 2 127 - 1 := by decide
theorem fp128_of_bits_width :
    bits_of_fp128 (fp128_of_bits (Z.pow 2 128)) = Z.pow 2 127 := by decide
theorem fp128_of_bits_double_width_pred :
    bits_of_fp128 (fp128_of_bits (Z.pow 2 129 - 1)) = max_unsigned_128 := by
  decide

theorem fexp32_zero : fexp32 0 = -24 := by decide
theorem fexp32_below_emin : fexp32 (-200) = -149 := by decide
theorem fexp64_below_emin : fexp64 (-2000) = -1074 := by decide
theorem fexp128_zero : fexp128 0 = -113 := by decide

#print axioms fp32_of_bits_neg_one
#print axioms fp128_of_bits_double_width_pred
#print axioms fexp128_zero

end KernelCompatibilityTests

example : bits_of_fp32 (fp32_add (fp32_of_bits 0x3f800000)
    (fp32_of_bits 0x40000000)) = 0x40400000 := by native_decide
example : bits_of_fp64 (fp64_div (fp64_of_bits 0x3ff0000000000000)
    (fp64_of_bits 0x4000000000000000)) = 0x3fe0000000000000 := by native_decide
example : bits_of_fp128 (fp128_mul (fp128_of_bits 0x40000000000000000000000000000000)
    (fp128_of_bits 0x40008000000000000000000000000000)) =
    0x40018000000000000000000000000000 := by native_decide

example : fp32_isFinite FLT_MAX := by rfl
example : fp64_isInf fp64_pos_infinity := by rfl
example : fp128_isNaN fp128_nan := by rfl
example : fp32_compare fp32_zero fp32_neg_zero = some .eq := by native_decide
example : fp32_compare fp32_nan fp32_zero = none := by native_decide

example (z : Int) : fp32_of_Z z = fp32_of_real (z : Real) := rfl
example (z : Int) : fp64_of_Z z = fp64_of_real (z : Real) := rfl
example (z : Int) : fp128_of_Z z = fp128_of_real (z : Real) := rfl

section RealCompatibilityTests

example : rounded32 mode_NE 0 = 0 := by
  simp [rounded32, Flocq.Compatibility.IEEEReal.implementation_round,
    Flocq.Internal.RealRound.roundWithFexp]
example : in_float32_range mode_NE 0 := by
  norm_num [in_float32_range, rounded32,
    Flocq.Compatibility.IEEEReal.implementation_round,
    Flocq.Internal.RealRound.roundWithFexp, Flocq.Core.bpow,
    Flocq.Core.radix2]
example (m : mode) (r : Real) :
    Flocq.Core.generic_format Flocq.Core.radix2 fexp64 (rounded64 m r) :=
  rounded64_generic m r

example : fp32_to_R fp32_pos_infinity = none := by rfl
example : fp64_to_R_total fp64_nan = 0 := by rfl
example (x : fp32) (h : BinaryFloat.isFiniteBool x = true) :
    fp32_to_R x = some (B2R 24 128 x) := by
  simp [fp32_to_R, is_finite, h]
example (x : fp128) (h : BinaryFloat.isFiniteBool x = false) :
    fp128_to_R x = none := by
  simp [fp128_to_R, is_finite, h]
example : fp32_of_real 0 = fp32_zero := by
  simp [fp32_of_real, rounded32,
    Flocq.Compatibility.IEEEReal.implementation_round,
    Flocq.Internal.RealRound.roundWithFexp, Flocq.Core.scaled_mantissa,
    Flocq.Core.cexp, Flocq.Core.mag, Flocq.Core.Ztrunc,
    Flocq.IEEE754.binary_normalize, fp32_zero]
  change Flocq.Internal.IEEE.BinaryFloat.zero binary32Format =
    Flocq.Internal.IEEE.BinaryFloat.ofBits binary32Format 0
  decide

#print axioms rounded32_generic
#print axioms fp32_of_real
#print axioms fp128_to_R_total

end RealCompatibilityTests

#print axioms fp32_add
#print axioms bits_of_float_value_range
#print axioms bits_of_long_double_value_range

end FloatLibTests
