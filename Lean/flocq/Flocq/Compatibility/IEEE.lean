import Flocq.Internal.IEEE

namespace Flocq.Compatibility.IEEE

open Flocq.IEEE754.BinarySingleNaN

/-!
Lean-only adapter for the internal `BitVec` IEEE representation.

This file has no Coq source-file counterpart. In particular, `Format`,
`BinaryFloat`, and their camelCase operations below are implementation APIs,
not declarations attributed to `IEEE754/Binary.v` or `IEEE754/Bits.v`.
-/

abbrev Format := Flocq.Internal.IEEE.Format

namespace Format

abbrev mk := Flocq.Internal.IEEE.Format.mk
abbrev fracBits := Flocq.Internal.IEEE.Format.fracBits
abbrev expBits := Flocq.Internal.IEEE.Format.expBits
abbrev width (fmt : Format) : Nat := Flocq.Internal.IEEE.Format.width fmt
abbrev fractionModulus (fmt : Format) : Nat :=
  Flocq.Internal.IEEE.Format.fractionModulus fmt
abbrev exponentModulus (fmt : Format) : Nat :=
  Flocq.Internal.IEEE.Format.exponentModulus fmt
abbrev exponentMax (fmt : Format) : Nat :=
  Flocq.Internal.IEEE.Format.exponentMax fmt
abbrev bias (fmt : Format) : Nat := Flocq.Internal.IEEE.Format.bias fmt
abbrev minSubnormalExponent (fmt : Format) : Int :=
  Flocq.Internal.IEEE.Format.minSubnormalExponent fmt
abbrev modulus (fmt : Format) : Nat := Flocq.Internal.IEEE.Format.modulus fmt

end Format

abbrev BinaryFloat := Flocq.Internal.IEEE.BinaryFloat

namespace BinaryFloat

abbrev ofBits (fmt : Format) (z : Int) : BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.ofBits fmt z
abbrev bitsOf {fmt : Format} (x : BinaryFloat fmt) : Int :=
  Flocq.Internal.IEEE.BinaryFloat.bitsOf x
abbrev sign {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  Flocq.Internal.IEEE.BinaryFloat.sign x
abbrev fraction {fmt : Format} (x : BinaryFloat fmt) : Nat :=
  Flocq.Internal.IEEE.BinaryFloat.fraction x
abbrev exponent {fmt : Format} (x : BinaryFloat fmt) : Nat :=
  Flocq.Internal.IEEE.BinaryFloat.exponent x
abbrev pack (fmt : Format) (negative : Bool) (exponent fraction : Nat) :
    BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.pack fmt negative exponent fraction
abbrev zero (fmt : Format) (negative : Bool := false) : BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.zero fmt negative
abbrev infinity (fmt : Format) (negative : Bool := false) : BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.infinity fmt negative
abbrev nan (fmt : Format) (negative : Bool := false) (payload : Nat := 1) :
    BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.nan fmt negative payload
abbrev maxFinite (fmt : Format) (negative : Bool := false) : BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.maxFinite fmt negative
abbrev payloadValid (fmt : Format) (payload : Nat) : Bool :=
  Flocq.Internal.IEEE.BinaryFloat.payloadValid fmt payload
abbrev isFiniteBool {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  Flocq.Internal.IEEE.BinaryFloat.isFiniteBool x
abbrev isNaNBool {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  Flocq.Internal.IEEE.BinaryFloat.isNaNBool x
abbrev isInfBool {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  Flocq.Internal.IEEE.BinaryFloat.isInfBool x
abbrev isZeroBool {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  Flocq.Internal.IEEE.BinaryFloat.isZeroBool x
abbrev finiteToRat {fmt : Format} (x : BinaryFloat fmt) : Rat :=
  Flocq.Internal.IEEE.BinaryFloat.finiteToRat x
abbrev pow2Rat := Flocq.Internal.IEEE.BinaryFloat.pow2Rat
abbrev absRat := Flocq.Internal.IEEE.BinaryFloat.absRat
abbrev toRat? {fmt : Format} (x : BinaryFloat fmt) : Option Rat :=
  Flocq.Internal.IEEE.BinaryFloat.toRat? x
abbrev toRatTotal {fmt : Format} (x : BinaryFloat fmt) : Rat :=
  Flocq.Internal.IEEE.BinaryFloat.toRatTotal x
abbrev compare {fmt : Format} (x y : BinaryFloat fmt) : Option Ordering :=
  Flocq.Internal.IEEE.BinaryFloat.compare x y
abbrev neg {fmt : Format} (x : BinaryFloat fmt) : BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.neg x
abbrev add (fmt : Format) (m : mode) (x y : BinaryFloat fmt) : BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.add fmt m x y
abbrev sub (fmt : Format) (m : mode) (x y : BinaryFloat fmt) : BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.sub fmt m x y
abbrev mul (fmt : Format) (m : mode) (x y : BinaryFloat fmt) : BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.mul fmt m x y
abbrev div (fmt : Format) (m : mode) (x y : BinaryFloat fmt) : BinaryFloat fmt :=
  Flocq.Internal.IEEE.BinaryFloat.div fmt m x y
abbrev roundWithFexp := Flocq.Internal.IEEE.BinaryFloat.roundWithFexp
abbrev genericFormat := Flocq.Internal.IEEE.BinaryFloat.genericFormat
abbrev ofRat := Flocq.Internal.IEEE.BinaryFloat.ofRat
abbrev bitsOf_nonneg {fmt : Format} (x : BinaryFloat fmt) : 0 <= bitsOf x :=
  Flocq.Internal.IEEE.BinaryFloat.bitsOf_nonneg x
abbrev bitsOf_lt_modulus {fmt : Format} (x : BinaryFloat fmt) :
    bitsOf x < Int.ofNat fmt.modulus :=
  Flocq.Internal.IEEE.BinaryFloat.bitsOf_lt_modulus x

end BinaryFloat

def formatOfParameters (prec emax : Int) : Format where
  fracBits := (prec - 1).toNat
  expBits := emax.toNat.log2 + 1

abbrev binary32Format : Format := formatOfParameters 24 128
abbrev binary64Format : Format := formatOfParameters 53 1024
abbrev binary128Format : Format := formatOfParameters 113 16384
abbrev binary128 := BinaryFloat binary128Format

end Flocq.Compatibility.IEEE

namespace Flocq.IEEE754

export Flocq.Compatibility.IEEE
  (Format BinaryFloat formatOfParameters binary32Format binary64Format
    binary128Format binary128)

namespace Format
export Flocq.Compatibility.IEEE.Format
  (mk fracBits expBits width fractionModulus exponentModulus exponentMax bias
    minSubnormalExponent modulus)
end Format

namespace BinaryFloat
export Flocq.Compatibility.IEEE.BinaryFloat
  (ofBits bitsOf sign fraction exponent pack zero infinity nan maxFinite
    payloadValid isFiniteBool isNaNBool isInfBool isZeroBool finiteToRat
    pow2Rat absRat toRat? toRatTotal compare neg add sub mul div roundWithFexp
    genericFormat ofRat bitsOf_nonneg bitsOf_lt_modulus)
end BinaryFloat

end Flocq.IEEE754
