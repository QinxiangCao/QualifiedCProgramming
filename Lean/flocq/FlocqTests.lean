import Flocq
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum

namespace FlocqTests

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
      | throwError "Flocq slice declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkFlocqSourceApiContract)
  "#check_flocq_source_api_contract " "[" ident,* "]" " => " num : command

syntax (name := checkFlocqAdapterApiContract)
  "#check_flocq_adapter_api_contract " "[" ident,* "]" " => " num : command

private def checkApiContract (label : String) (ids : Array Syntax)
    (expectedSyntax : Syntax) : CommandElabM Unit := do
  let names <- resolveApiDecls ids
  let some expected := expectedSyntax.isNatLit?
    | throwErrorAt expectedSyntax "expected a natural-number API type hash"
  let actual <- apiTypeHash names
  unless actual = expected.toUInt64 do
    throwError "Flocq {label} API type hash changed: expected {expected}, got {actual}"
  let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    for axiomName in (← collectAxioms name) do
      unless allowedAxioms.contains axiomName do
        throwError "Flocq {label} declaration '{name}' depends on disallowed axiom '{axiomName}'"
  logInfo m!"Flocq {label} API contract verified for {names.size} declarations"

elab_rules : command
  | `(#check_flocq_source_api_contract [$ids:ident,*] => $expected:num) =>
      checkApiContract "source-shaped" ids expected
  | `(#check_flocq_adapter_api_contract [$ids:ident,*] => $expected:num) =>
      checkApiContract "Lean adapter" ids expected

-- This list contains only declarations assigned to same-name Flocq source
-- modules. Representation-level deviations are described in the mapping
-- document and are not hidden among the implementation declarations below.
#check_flocq_source_api_contract [
  Flocq.Core.Zaux.radix, Flocq.Core.Zaux.Build_radix,
  Flocq.Core.Zaux.radix.radix_val, Flocq.Core.Zaux.radix.radix_prop,
  Flocq.Core.Zaux.radix_val_inj, Flocq.Core.Zaux.radix2,
  Flocq.Core.Zaux.radix_gt_0, Flocq.Core.Zaux.radix_gt_1,
  Flocq.Core.Raux.Zfloor, Flocq.Core.Raux.Zceil, Flocq.Core.Raux.Ztrunc,
  Flocq.Core.Raux.bpow, Flocq.Core.Raux.mag_prop,
  Flocq.Core.Raux.Build_mag_prop, Flocq.Core.Raux.mag_prop.mag_val,
  Flocq.Core.Raux.mag,
  Flocq.Core.Defs.float, Flocq.Core.Defs.Float,
  Flocq.Core.Defs.float.Fnum, Flocq.Core.Defs.float.Fexp,
  Flocq.Core.Defs.F2R, Flocq.Core.Defs.round_pred_total,
  Flocq.Core.Defs.round_pred_monotone, Flocq.Core.Defs.round_pred,
  Flocq.Core.Generic_fmt.cexp, Flocq.Core.Generic_fmt.scaled_mantissa,
  Flocq.Core.Generic_fmt.generic_format, Flocq.Core.Generic_fmt.round,
  Flocq.Core.Generic_fmt.Znearest, Flocq.Core.Generic_fmt.ZnearestA,
  Flocq.Core.Round_NE.ZnearestE,
  Flocq.Core.FLX.Prec_gt_0, Flocq.Core.FLX.Build_Prec_gt_0,
  Flocq.Core.FLX.Prec_gt_0.prec_gt_0, Flocq.Core.FLT.FLT_exp,
  Flocq.IEEE754.BinarySingleNaN.mode,
  Flocq.IEEE754.BinarySingleNaN.mode.mode_NE,
  Flocq.IEEE754.BinarySingleNaN.mode.mode_ZR,
  Flocq.IEEE754.BinarySingleNaN.mode.mode_DN,
  Flocq.IEEE754.BinarySingleNaN.mode.mode_UP,
  Flocq.IEEE754.BinarySingleNaN.mode.mode_NA,
  Flocq.IEEE754.BinarySingleNaN.round_mode,
  Flocq.IEEE754.BinarySingleNaN.Prec_lt_emax,
  Flocq.IEEE754.BinarySingleNaN.Build_Prec_lt_emax,
  Flocq.IEEE754.BinarySingleNaN.Prec_lt_emax.prec_lt_emax,
  Flocq.IEEE754.Binary.binary_float, Flocq.IEEE754.Binary.nan_pl,
  Flocq.IEEE754.Binary.is_finite, Flocq.IEEE754.Binary.is_nan,
  Flocq.IEEE754.Binary.B2R, Flocq.IEEE754.Binary.Bcompare,
  Flocq.IEEE754.Binary.Bopp, Flocq.IEEE754.Binary.Bplus,
  Flocq.IEEE754.Binary.Bminus, Flocq.IEEE754.Binary.Bmult,
  Flocq.IEEE754.Binary.Bdiv, Flocq.IEEE754.Binary.binary_normalize,
  Flocq.IEEE754.Bits.bits_of_binary_float,
  Flocq.IEEE754.Bits.binary_float_of_bits,
  Flocq.IEEE754.Bits.binary32, Flocq.IEEE754.Bits.binary64,
  Flocq.IEEE754.Bits.b32_of_bits, Flocq.IEEE754.Bits.b64_of_bits,
  Flocq.IEEE754.Bits.bits_of_b32, Flocq.IEEE754.Bits.bits_of_b64,
  Flocq.IEEE754.Bits.bits_of_binary_float_range
] => 16455987168341103879

-- These declarations implement the Lean `BitVec`/`Rat`/`Real` adaptation.
-- They intentionally have no same-name Coq source-file ownership.
#check_flocq_adapter_api_contract [
  Flocq.Compatibility.IEEE.Format, Flocq.Compatibility.IEEE.Format.mk,
  Flocq.Compatibility.IEEE.Format.fracBits,
  Flocq.Compatibility.IEEE.Format.expBits,
  Flocq.Compatibility.IEEE.Format.width,
  Flocq.Compatibility.IEEE.Format.fractionModulus,
  Flocq.Compatibility.IEEE.Format.exponentModulus,
  Flocq.Compatibility.IEEE.Format.exponentMax,
  Flocq.Compatibility.IEEE.Format.bias,
  Flocq.Compatibility.IEEE.Format.minSubnormalExponent,
  Flocq.Compatibility.IEEE.Format.modulus,
  Flocq.Compatibility.IEEE.BinaryFloat,
  Flocq.Compatibility.IEEE.BinaryFloat.ofBits,
  Flocq.Compatibility.IEEE.BinaryFloat.bitsOf,
  Flocq.Compatibility.IEEE.BinaryFloat.sign,
  Flocq.Compatibility.IEEE.BinaryFloat.fraction,
  Flocq.Compatibility.IEEE.BinaryFloat.exponent,
  Flocq.Compatibility.IEEE.BinaryFloat.pack,
  Flocq.Compatibility.IEEE.BinaryFloat.zero,
  Flocq.Compatibility.IEEE.BinaryFloat.infinity,
  Flocq.Compatibility.IEEE.BinaryFloat.nan,
  Flocq.Compatibility.IEEE.BinaryFloat.maxFinite,
  Flocq.Compatibility.IEEE.BinaryFloat.isFiniteBool,
  Flocq.Compatibility.IEEE.BinaryFloat.isNaNBool,
  Flocq.Compatibility.IEEE.BinaryFloat.isInfBool,
  Flocq.Compatibility.IEEE.BinaryFloat.isZeroBool,
  Flocq.Compatibility.IEEE.BinaryFloat.payloadValid,
  Flocq.Compatibility.IEEE.BinaryFloat.pow2Rat,
  Flocq.Compatibility.IEEE.BinaryFloat.absRat,
  Flocq.Compatibility.IEEE.BinaryFloat.finiteToRat,
  Flocq.Compatibility.IEEE.BinaryFloat.toRat?,
  Flocq.Compatibility.IEEE.BinaryFloat.toRatTotal,
  Flocq.Compatibility.IEEE.BinaryFloat.roundWithFexp,
  Flocq.Compatibility.IEEE.BinaryFloat.genericFormat,
  Flocq.Compatibility.IEEE.BinaryFloat.ofRat,
  Flocq.Compatibility.IEEE.BinaryFloat.compare,
  Flocq.Compatibility.IEEE.BinaryFloat.neg,
  Flocq.Compatibility.IEEE.BinaryFloat.add,
  Flocq.Compatibility.IEEE.BinaryFloat.sub,
  Flocq.Compatibility.IEEE.BinaryFloat.mul,
  Flocq.Compatibility.IEEE.BinaryFloat.div,
  Flocq.Compatibility.IEEE.BinaryFloat.bitsOf_nonneg,
  Flocq.Compatibility.IEEE.BinaryFloat.bitsOf_lt_modulus,
  Flocq.Internal.RealRound.pow2, Flocq.Internal.RealRound.abs,
  Flocq.Internal.RealRound.floorLog2, Flocq.Internal.RealRound.fltExp,
  Flocq.Internal.RealRound.magnitude, Flocq.Internal.RealRound.cexp,
  Flocq.Internal.RealRound.scaledMantissa, Flocq.Internal.RealRound.trunc,
  Flocq.Internal.RealRound.f2r, Flocq.Internal.RealRound.roundWithFexp,
  Flocq.Internal.RealRound.genericFormat,
  Flocq.Internal.RealRound.genericFormat_of_representation,
  Flocq.Internal.RealRound.genericFormat_f2r_of_cexp_le,
  Flocq.Internal.RealRound.magnitude_pow2,
  Flocq.Internal.RealRound.genericFormat_pow2,
  Flocq.Internal.RealRound.roundMagnitude_bounds,
  Flocq.Internal.RealRound.magnitude_neg_pow2,
  Flocq.Internal.RealRound.genericFormat_signed_pow2,
  Flocq.Internal.RealRound.roundWithFexp_generic,
  Flocq.Internal.RealRound.finiteToReal,
  Flocq.Internal.RealRound.toReal?, Flocq.Internal.RealRound.toRealTotal,
  Flocq.Internal.RealRound.ofReal,
  Flocq.Compatibility.IEEE.binary32Format,
  Flocq.Compatibility.IEEE.binary64Format,
  Flocq.Compatibility.IEEE.binary128Format,
  Flocq.Compatibility.IEEE.binary128
] => 13096773483067424341

-- Coq split_bits treats its input as three independently decoded fields rather
-- than truncating the complete integer modulo the target width.
section SplitBitsKernelTests

set_option maxRecDepth 100000

theorem ofBits_binary32_zero : bitsOf (ofBits binary32Format 0) = 0 := by decide
theorem ofBits_binary32_neg_one :
    bitsOf (ofBits binary32Format (-1)) = 2147483647 := by decide
theorem ofBits_binary32_width :
    bitsOf (ofBits binary32Format 4294967296) = 2147483648 := by decide
theorem ofBits_binary32_double_width_pred :
    bitsOf (ofBits binary32Format 8589934591) = 4294967295 := by decide
theorem ofBits_binary64_neg_one :
    bitsOf (ofBits binary64Format (-1)) = 9223372036854775807 := by decide
theorem ofBits_binary64_width :
    bitsOf (ofBits binary64Format 18446744073709551616) =
      9223372036854775808 := by decide
theorem ofBits_binary64_double_width_pred :
    bitsOf (ofBits binary64Format 36893488147419103231) =
      18446744073709551615 := by decide
theorem ofBits_binary128_neg_one :
    bitsOf (ofBits binary128Format (-1)) =
    170141183460469231731687303715884105727 := by
  decide
theorem ofBits_binary128_width :
    bitsOf (ofBits binary128Format 340282366920938463463374607431768211456) =
    170141183460469231731687303715884105728 := by
  decide
theorem ofBits_binary128_double_width_pred :
    bitsOf (ofBits binary128Format 680564733841876926926749214863536422911) =
    340282366920938463463374607431768211455 := by
  decide

#print axioms ofBits_binary32_neg_one
#print axioms ofBits_binary64_width
#print axioms ofBits_binary128_double_width_pred

end SplitBitsKernelTests

example : isFiniteBool (ofBits binary32Format 0x7f7fffff) := by native_decide
example : isInfBool (ofBits binary32Format 0x7f800000) := by native_decide
example : isNaNBool (ofBits binary32Format 0x7f800001) := by native_decide

example : bitsOf (add binary32Format mode_NE
    (ofBits binary32Format 0x3f800000) (ofBits binary32Format 0x40000000)) =
    0x40400000 := by native_decide
example : bitsOf (sub binary32Format mode_NE
    (ofBits binary32Format 0x40000000) (ofBits binary32Format 0x3f800000)) =
    0x3f800000 := by native_decide
example : bitsOf (mul binary32Format mode_NE
    (ofBits binary32Format 0x40000000) (ofBits binary32Format 0x40400000)) =
    0x40c00000 := by native_decide
example : bitsOf (div binary32Format mode_NE
    (ofBits binary32Format 0x3f800000) (ofBits binary32Format 0x40000000)) =
    0x3f000000 := by native_decide
example : bitsOf (mul binary64Format mode_NE
    (ofBits binary64Format 0x4000000000000000)
    (ofBits binary64Format 0x4008000000000000)) =
    0x4018000000000000 := by native_decide
example : bitsOf (div binary128Format mode_NE
    (ofBits binary128Format 0x3fff0000000000000000000000000000)
    (ofBits binary128Format 0x40000000000000000000000000000000)) =
    0x3ffe0000000000000000000000000000 := by native_decide

-- Nearest-even tie: 1 + 2^-24 rounds back to 1 in binary32.
example : bitsOf (add binary32Format mode_NE
    (ofBits binary32Format 0x3f800000) (ofBits binary32Format 0x33800000)) =
    0x3f800000 := by native_decide
example : bitsOf (add binary32Format mode_NE
    (ofBits binary32Format 0x3f800000) (ofBits binary32Format 0x34000000)) =
    0x3f800001 := by native_decide

-- These values were computed by the Coq FloatLib at commit 8f2510a.
example : bitsOf (add binary32Format mode_NE
    (ofBits binary32Format 1) (ofBits binary32Format 1)) = 2 := by native_decide
example : bitsOf (add binary32Format mode_NE
    (maxFinite binary32Format) (maxFinite binary32Format)) = 0x7f800000 := by
  native_decide
example : bitsOf (add binary32Format mode_NE
    (infinity binary32Format) (infinity binary32Format true)) = 0x7f800001 := by
  native_decide
example : bitsOf (add binary32Format mode_NE
    (zero binary32Format) (zero binary32Format true)) = 0 := by native_decide
example : bitsOf (add binary32Format mode_NE
    (zero binary32Format true) (zero binary32Format true)) = 0x80000000 := by
  native_decide
example : bitsOf (mul binary32Format mode_NE
    (zero binary32Format) (infinity binary32Format)) = 0x7f800001 := by
  native_decide
example : bitsOf (div binary32Format mode_NE
    (ofBits binary32Format 0x3f800000) (zero binary32Format)) = 0x7f800000 := by
  native_decide
example : bitsOf (neg (ofBits binary32Format 0x7fc00000)) = 0x7f800001 := by
  native_decide

example : bitsOf (add binary64Format mode_NE
    (ofBits binary64Format 0x3ff0000000000000)
    (ofBits binary64Format 0x4000000000000000)) = 0x4008000000000000 := by
  native_decide
example : bitsOf (div binary64Format mode_NE
    (ofBits binary64Format 0x3ff0000000000000)
    (ofBits binary64Format 0x4000000000000000)) = 0x3fe0000000000000 := by
  native_decide
example : bitsOf (add binary128Format mode_NE
    (ofBits binary128Format 0x3fff0000000000000000000000000000)
    (ofBits binary128Format 0x40000000000000000000000000000000)) =
    0x40008000000000000000000000000000 := by native_decide

example : BinaryFloat.compare (ofBits binary32Format 0x80000000)
    (ofBits binary32Format 0) = some Ordering.eq := by native_decide
example : BinaryFloat.compare (nan binary32Format) (zero binary32Format) = none := by
  native_decide

section RealRoundingTests

private def toyFormat : Flocq.IEEE754.Format where
  fracBits := 1
  expBits := 1

private def boundaryFormat : Flocq.IEEE754.Format where
  fracBits := 2
  expBits := 2

example : Flocq.Internal.RealRound.roundWithFexp (fun _ => 0) mode_NE (5 / 2 : Real) = 2 := by
  norm_num [Flocq.Internal.RealRound.roundWithFexp, Flocq.Internal.RealRound.Internal.roundMagnitude,
    Flocq.Internal.RealRound.abs, Flocq.Internal.RealRound.pow2]
example : Flocq.Internal.RealRound.roundWithFexp (fun _ => 0) mode_NA (5 / 2 : Real) = 3 := by
  norm_num [Flocq.Internal.RealRound.roundWithFexp, Flocq.Internal.RealRound.Internal.roundMagnitude,
    Flocq.Internal.RealRound.abs, Flocq.Internal.RealRound.pow2]
example : Flocq.Internal.RealRound.roundWithFexp (fun _ => 0) mode_ZR (-5 / 2 : Real) = -2 := by
  norm_num [Flocq.Internal.RealRound.roundWithFexp, Flocq.Internal.RealRound.Internal.roundMagnitude,
    Flocq.Internal.RealRound.abs, Flocq.Internal.RealRound.pow2]
example : Flocq.Internal.RealRound.roundWithFexp (fun _ => 0) mode_DN (-5 / 2 : Real) = -3 := by
  norm_num [Flocq.Internal.RealRound.roundWithFexp, Flocq.Internal.RealRound.Internal.roundMagnitude,
    Flocq.Internal.RealRound.abs, Flocq.Internal.RealRound.pow2]
example : Flocq.Internal.RealRound.roundWithFexp (fun _ => 0) mode_UP (-5 / 2 : Real) = -2 := by
  norm_num [Flocq.Internal.RealRound.roundWithFexp, Flocq.Internal.RealRound.Internal.roundMagnitude,
    Flocq.Internal.RealRound.abs, Flocq.Internal.RealRound.pow2]

example : Flocq.Internal.RealRound.toReal? (infinity binary32Format) = none := by rfl
example : Flocq.Internal.RealRound.toRealTotal (nan binary64Format) = 0 := by rfl
example : Flocq.Internal.RealRound.ofReal binary128Format mode_NE 0 = zero binary128Format := by
  simp [Flocq.Internal.RealRound.ofReal]
example : bitsOf (Flocq.Internal.RealRound.ofReal toyFormat mode_NE 1) = 1 := by
  norm_num [Flocq.Internal.RealRound.ofReal, Flocq.Internal.RealRound.Internal.roundMagnitude, Flocq.Internal.RealRound.abs,
    Flocq.Internal.RealRound.pow2, Flocq.Internal.RealRound.floorLog2, toyFormat,
    Flocq.Internal.IEEE.BinaryFloat.bitsOf, Flocq.Internal.IEEE.BinaryFloat.pack,
    Flocq.Internal.IEEE.BinaryFloat.ofBits, Flocq.Internal.IEEE.Format.exponentMax,
    Flocq.Internal.IEEE.Format.exponentModulus,
    Flocq.Internal.IEEE.Format.fractionModulus,
    Flocq.Internal.IEEE.Format.minSubnormalExponent,
    Flocq.Internal.IEEE.Format.bias, Flocq.Internal.IEEE.Format.width]
example : bitsOf (Flocq.Internal.RealRound.ofReal toyFormat mode_NE (-1)) = 5 := by
  norm_num [Flocq.Internal.RealRound.ofReal, Flocq.Internal.RealRound.Internal.roundMagnitude, Flocq.Internal.RealRound.abs,
    Flocq.Internal.RealRound.pow2, Flocq.Internal.RealRound.floorLog2, toyFormat,
    Flocq.Internal.IEEE.BinaryFloat.bitsOf, Flocq.Internal.IEEE.BinaryFloat.pack,
    Flocq.Internal.IEEE.BinaryFloat.ofBits, Flocq.Internal.IEEE.Format.exponentMax,
    Flocq.Internal.IEEE.Format.exponentModulus,
    Flocq.Internal.IEEE.Format.fractionModulus,
    Flocq.Internal.IEEE.Format.minSubnormalExponent,
    Flocq.Internal.IEEE.Format.bias, Flocq.Internal.IEEE.Format.width]

example : Flocq.Internal.RealRound.floorLog2 (Flocq.Internal.RealRound.pow2 (-149)) = -149 := by
  exact Int.log_zpow (R := Real) (by decide : 1 < 2) (-149)

-- The small format exercises the same normalization branches as binary32
-- without turning each kernel test into a large BitVec reduction.
example : bitsOf (Flocq.Internal.RealRound.ofReal boundaryFormat mode_NE
    (Flocq.Internal.RealRound.pow2 (-2))) = 1 := by
  have hpos : 0 < Flocq.Internal.RealRound.pow2 (-2) := zpow_pos (by norm_num) _
  rw [Flocq.Internal.RealRound.ofReal, if_neg hpos.ne']
  have hnegative : decide (Flocq.Internal.RealRound.pow2 (-2) < 0) = false := by simp [hpos.le]
  rw [hnegative, Flocq.Internal.RealRound.abs, abs_of_pos hpos]
  have hlog : Flocq.Internal.RealRound.floorLog2 (Flocq.Internal.RealRound.pow2 (-2)) = -2 := by
    exact Int.log_zpow (R := Real) (by decide : 1 < 2) (-2)
  dsimp only
  rw [hlog]
  norm_num [Flocq.Internal.RealRound.Internal.roundMagnitude, Flocq.Internal.RealRound.pow2,
    Flocq.Internal.IEEE.BinaryFloat.bitsOf, Flocq.Internal.IEEE.BinaryFloat.pack,
    Flocq.Internal.IEEE.BinaryFloat.ofBits, Flocq.Internal.IEEE.Format.exponentMax,
    Flocq.Internal.IEEE.Format.exponentModulus,
    Flocq.Internal.IEEE.Format.fractionModulus,
    Flocq.Internal.IEEE.Format.minSubnormalExponent,
    Flocq.Internal.IEEE.Format.bias, Flocq.Internal.IEEE.Format.width, boundaryFormat]

example : bitsOf (Flocq.Internal.RealRound.ofReal boundaryFormat mode_NE
    (Flocq.Internal.RealRound.pow2 0)) = 4 := by
  have hpos : 0 < Flocq.Internal.RealRound.pow2 0 := zpow_pos (by norm_num) _
  rw [Flocq.Internal.RealRound.ofReal, if_neg hpos.ne']
  have hnegative : decide (Flocq.Internal.RealRound.pow2 0 < 0) = false := by simp [hpos.le]
  rw [hnegative, Flocq.Internal.RealRound.abs, abs_of_pos hpos]
  have hlog : Flocq.Internal.RealRound.floorLog2 (Flocq.Internal.RealRound.pow2 0) = 0 := by
    exact Int.log_zpow (R := Real) (by decide : 1 < 2) 0
  dsimp only
  rw [hlog]
  norm_num [Flocq.Internal.RealRound.Internal.roundMagnitude, Flocq.Internal.RealRound.pow2,
    Flocq.Internal.IEEE.BinaryFloat.bitsOf, Flocq.Internal.IEEE.BinaryFloat.pack,
    Flocq.Internal.IEEE.BinaryFloat.ofBits, Flocq.Internal.IEEE.Format.exponentMax,
    Flocq.Internal.IEEE.Format.exponentModulus,
    Flocq.Internal.IEEE.Format.fractionModulus,
    Flocq.Internal.IEEE.Format.minSubnormalExponent,
    Flocq.Internal.IEEE.Format.bias, Flocq.Internal.IEEE.Format.width, boundaryFormat]

private theorem log_seven_eighths :
    Flocq.Internal.RealRound.floorLog2 (7 / 8 : Real) = -1 := by
  rw [Flocq.Internal.RealRound.floorLog2]
  apply le_antisymm
  · have h := (Int.lt_zpow_iff_log_lt (R := Real) (by decide : 1 < 2)
      (by norm_num : (0 : Real) < 7 / 8)).mp
      (by norm_num : (7 / 8 : Real) < (2 : Real) ^ (0 : Int))
    omega
  · exact (Int.zpow_le_iff_le_log (R := Real) (by decide : 1 < 2)
      (by norm_num : (0 : Real) < 7 / 8)).mp
      (by norm_num : (2 : Real) ^ (-1 : Int) <= (7 / 8 : Real))

-- A mantissa carry crosses from the largest subnormal candidate to normal.
example : bitsOf (Flocq.Internal.RealRound.ofReal boundaryFormat mode_NE (7 / 8 : Real)) = 4 := by
  rw [Flocq.Internal.RealRound.ofReal, if_neg (by norm_num : (7 / 8 : Real) ≠ 0)]
  norm_num [Flocq.Internal.RealRound.abs]
  rw [log_seven_eighths]
  norm_num [Flocq.Internal.RealRound.Internal.roundMagnitude, Flocq.Internal.RealRound.pow2,
    Flocq.Internal.IEEE.BinaryFloat.bitsOf, Flocq.Internal.IEEE.BinaryFloat.pack,
    Flocq.Internal.IEEE.BinaryFloat.ofBits, Flocq.Internal.IEEE.Format.exponentMax,
    Flocq.Internal.IEEE.Format.exponentModulus,
    Flocq.Internal.IEEE.Format.fractionModulus,
    Flocq.Internal.IEEE.Format.minSubnormalExponent,
    Flocq.Internal.IEEE.Format.bias, Flocq.Internal.IEEE.Format.width, boundaryFormat]

private theorem log_three_eighths :
    Flocq.Internal.RealRound.floorLog2 (3 / 8 : Real) = -2 := by
  rw [Flocq.Internal.RealRound.floorLog2]
  apply le_antisymm
  · have h := (Int.lt_zpow_iff_log_lt (R := Real) (by decide : 1 < 2)
      (by norm_num : (0 : Real) < 3 / 8)).mp
      (by norm_num : (3 / 8 : Real) < (2 : Real) ^ (-1 : Int))
    omega
  · exact (Int.zpow_le_iff_le_log (R := Real) (by decide : 1 < 2)
      (by norm_num : (0 : Real) < 3 / 8)).mp
      (by norm_num : (2 : Real) ^ (-2 : Int) <= (3 / 8 : Real))

example : bitsOf (Flocq.Internal.RealRound.ofReal boundaryFormat mode_NE (3 / 8 : Real)) = 2 := by
  rw [Flocq.Internal.RealRound.ofReal, if_neg (by norm_num : (3 / 8 : Real) ≠ 0)]
  norm_num [Flocq.Internal.RealRound.abs]
  rw [log_three_eighths]
  norm_num [Flocq.Internal.RealRound.Internal.roundMagnitude, Flocq.Internal.RealRound.pow2,
    Flocq.Internal.IEEE.BinaryFloat.bitsOf, Flocq.Internal.IEEE.BinaryFloat.pack,
    Flocq.Internal.IEEE.BinaryFloat.ofBits, Flocq.Internal.IEEE.Format.exponentMax,
    Flocq.Internal.IEEE.Format.exponentModulus,
    Flocq.Internal.IEEE.Format.fractionModulus,
    Flocq.Internal.IEEE.Format.minSubnormalExponent,
    Flocq.Internal.IEEE.Format.bias, Flocq.Internal.IEEE.Format.width, boundaryFormat]

example : bitsOf (BinaryFloat.ofRat boundaryFormat mode_NE (3 / 8 : Rat)) = 2 := by
  native_decide

example (x : BinaryFloat boundaryFormat) (hfinite : isFiniteBool x = true) :
    Flocq.Internal.RealRound.toReal? x = some (Flocq.Internal.RealRound.finiteToReal x) := by
  simp [Flocq.Internal.RealRound.toReal?, hfinite]

private def positiveOverflowBits : mode -> Nat
  | mode_NE | mode_NA | mode_UP => 12
  | mode_ZR | mode_DN => 11

private def negativeOverflowBits : mode -> Nat
  | mode_NE | mode_NA | mode_DN => 28
  | mode_ZR | mode_UP => 27

example (m : mode) : bitsOf (Flocq.Internal.RealRound.ofReal boundaryFormat m
    (Flocq.Internal.RealRound.pow2 2)) = positiveOverflowBits m := by
  have hpos : 0 < Flocq.Internal.RealRound.pow2 2 := zpow_pos (by norm_num) _
  rw [Flocq.Internal.RealRound.ofReal, if_neg hpos.ne']
  have hnegative : decide (Flocq.Internal.RealRound.pow2 2 < 0) = false := by simp [hpos.le]
  rw [hnegative, Flocq.Internal.RealRound.abs, abs_of_pos hpos]
  have hlog : Flocq.Internal.RealRound.floorLog2 (Flocq.Internal.RealRound.pow2 2) = 2 := by
    exact Int.log_zpow (R := Real) (by decide : 1 < 2) 2
  dsimp only
  rw [hlog]
  cases m <;>
    norm_num [Flocq.Internal.RealRound.Internal.roundMagnitude, Flocq.Internal.RealRound.pow2,
      positiveOverflowBits, Flocq.Internal.IEEE.BinaryFloat.bitsOf,
      Flocq.Internal.IEEE.BinaryFloat.pack, Flocq.Internal.IEEE.BinaryFloat.ofBits,
      Flocq.Internal.IEEE.BinaryFloat.maxFinite,
      Flocq.Internal.IEEE.BinaryFloat.infinity,
      Flocq.Internal.RealRound.Internal.overflow,
      Flocq.Internal.IEEE.Format.exponentMax,
      Flocq.Internal.IEEE.Format.exponentModulus,
      Flocq.Internal.IEEE.Format.fractionModulus,
      Flocq.Internal.IEEE.Format.minSubnormalExponent,
      Flocq.Internal.IEEE.Format.bias, Flocq.Internal.IEEE.Format.width, boundaryFormat]

example (m : mode) : bitsOf (Flocq.Internal.RealRound.ofReal boundaryFormat m
    (-Flocq.Internal.RealRound.pow2 2)) = negativeOverflowBits m := by
  have hpos : 0 < Flocq.Internal.RealRound.pow2 2 := zpow_pos (by norm_num) _
  rw [Flocq.Internal.RealRound.ofReal, if_neg (neg_ne_zero.mpr hpos.ne')]
  have hnegative : decide (-Flocq.Internal.RealRound.pow2 2 < 0) = true := by simp [hpos]
  rw [hnegative, Flocq.Internal.RealRound.abs]
  simp only [abs_neg, abs_of_pos hpos]
  have hlog : Flocq.Internal.RealRound.floorLog2 (Flocq.Internal.RealRound.pow2 2) = 2 := by
    exact Int.log_zpow (R := Real) (by decide : 1 < 2) 2
  rw [hlog]
  cases m <;>
    norm_num [Flocq.Internal.RealRound.Internal.roundMagnitude, Flocq.Internal.RealRound.pow2,
      negativeOverflowBits, Flocq.Internal.IEEE.BinaryFloat.bitsOf,
      Flocq.Internal.IEEE.BinaryFloat.pack, Flocq.Internal.IEEE.BinaryFloat.ofBits,
      Flocq.Internal.IEEE.BinaryFloat.maxFinite,
      Flocq.Internal.IEEE.BinaryFloat.infinity,
      Flocq.Internal.RealRound.Internal.overflow,
      Flocq.Internal.IEEE.Format.exponentMax,
      Flocq.Internal.IEEE.Format.exponentModulus,
      Flocq.Internal.IEEE.Format.fractionModulus,
      Flocq.Internal.IEEE.Format.minSubnormalExponent,
      Flocq.Internal.IEEE.Format.bias, Flocq.Internal.IEEE.Format.width, boundaryFormat]

#print axioms Flocq.Internal.RealRound.roundWithFexp_generic
#print axioms Flocq.Internal.RealRound.ofReal

end RealRoundingTests

#print axioms BinaryFloat.add
#print axioms BinaryFloat.div
#print axioms BinaryFloat.bitsOf_lt_modulus

end FlocqTests
