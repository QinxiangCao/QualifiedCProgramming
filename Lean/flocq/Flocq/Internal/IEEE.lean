import Init.Data.BitVec.Lemmas
import Init.Data.Rat.Lemmas
import Flocq.IEEE754.BinarySingleNaN

/-!
Executable `BitVec`/`Rat` kernel used by the Lean adaptation. This module has
no Coq source-file counterpart and must not be counted as a migrated Flocq
source module.
-/

namespace Flocq.Internal.IEEE

open Flocq.IEEE754

structure Format where
  fracBits : Nat
  expBits : Nat

namespace Format

def width (fmt : Format) : Nat :=
  fmt.fracBits + fmt.expBits + 1

def fractionModulus (fmt : Format) : Nat :=
  2 ^ fmt.fracBits

def exponentModulus (fmt : Format) : Nat :=
  2 ^ fmt.expBits

def exponentMax (fmt : Format) : Nat :=
  fmt.exponentModulus - 1

def bias (fmt : Format) : Nat :=
  2 ^ (fmt.expBits - 1) - 1

def minSubnormalExponent (fmt : Format) : Int :=
  1 - Int.ofNat fmt.bias - Int.ofNat fmt.fracBits

def modulus (fmt : Format) : Nat :=
  2 ^ fmt.width

end Format

abbrev BinaryFloat (fmt : Format) : Type := BitVec fmt.width

namespace BinaryFloat

def ofBits (fmt : Format) (z : Int) : BinaryFloat fmt :=
  let fractionModulus := Int.ofNat fmt.fractionModulus
  let exponentModulus := Int.ofNat fmt.exponentModulus
  let signThreshold := fractionModulus * exponentModulus
  let signBits := if signThreshold <= z then signThreshold else 0
  let fraction := z % fractionModulus
  let exponent := (z / fractionModulus) % exponentModulus
  BitVec.ofInt fmt.width (signBits + exponent * fractionModulus + fraction)

def bitsOf {fmt : Format} (x : BinaryFloat fmt) : Int :=
  Int.ofNat x.toNat

def sign {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  x.toNat / (2 ^ (fmt.fracBits + fmt.expBits)) != 0

def fraction {fmt : Format} (x : BinaryFloat fmt) : Nat :=
  x.toNat % fmt.fractionModulus

def exponent {fmt : Format} (x : BinaryFloat fmt) : Nat :=
  x.toNat / fmt.fractionModulus % fmt.exponentModulus

def pack (fmt : Format) (negative : Bool) (exponent fraction : Nat) : BinaryFloat fmt :=
  let signBits := if negative then 2 ^ (fmt.fracBits + fmt.expBits) else 0
  ofBits fmt (Int.ofNat (signBits + exponent * fmt.fractionModulus + fraction))

def zero (fmt : Format) (negative : Bool := false) : BinaryFloat fmt :=
  pack fmt negative 0 0

def infinity (fmt : Format) (negative : Bool := false) : BinaryFloat fmt :=
  pack fmt negative fmt.exponentMax 0

def nan (fmt : Format) (negative : Bool := false) (payload : Nat := 1) : BinaryFloat fmt :=
  let payload := payload % fmt.fractionModulus
  pack fmt negative fmt.exponentMax (if payload = 0 then 1 else payload)

def maxFinite (fmt : Format) (negative : Bool := false) : BinaryFloat fmt :=
  pack fmt negative (fmt.exponentMax - 1) (fmt.fractionModulus - 1)

def isFiniteBool {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  exponent x != fmt.exponentMax

def isNaNBool {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  exponent x == fmt.exponentMax && fraction x != 0

def isInfBool {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  exponent x == fmt.exponentMax && fraction x == 0

def isZeroBool {fmt : Format} (x : BinaryFloat fmt) : Bool :=
  exponent x == 0 && fraction x == 0

def payloadValid (fmt : Format) (payload : Nat) : Bool :=
  payload != 0 && payload < fmt.fractionModulus

def pow2Rat : Int -> Rat
  | .ofNat n => (2 : Rat) ^ n
  | .negSucc n => 1 / ((2 : Rat) ^ (n + 1))

def absRat (x : Rat) : Rat :=
  if x < 0 then -x else x

def finiteToRat {fmt : Format} (x : BinaryFloat fmt) : Rat :=
  let frac := fraction x
  let exp := exponent x
  let mantissa := if exp = 0 then frac else fmt.fractionModulus + frac
  let unbiased :=
    if exp = 0 then fmt.minSubnormalExponent
    else Int.ofNat exp - Int.ofNat fmt.bias - Int.ofNat fmt.fracBits
  let magnitude := (Int.ofNat mantissa : Rat) * pow2Rat unbiased
  if sign x then -magnitude else magnitude

def toRat? {fmt : Format} (x : BinaryFloat fmt) : Option Rat :=
  if isFiniteBool x then some (finiteToRat x) else none

def toRatTotal {fmt : Format} (x : BinaryFloat fmt) : Rat :=
  (toRat? x).getD 0

private def floorLog2Positive (q : Rat) : Int :=
  let candidate :=
    Int.ofNat q.num.natAbs.log2 - Int.ofNat q.den.log2
  if q < pow2Rat candidate then candidate - 1 else candidate

private def roundMagnitude (m : mode) (negative : Bool) (q : Rat) : Int :=
  let n := q.floor
  let remainder := q - (n : Rat)
  let half : Rat := 1 / 2
  match m with
  | mode_NE =>
      if remainder < half then n
      else if half < remainder then n + 1
      else if n % 2 = 0 then n else n + 1
  | mode_ZR => n
  | mode_DN => if negative && remainder != 0 then n + 1 else n
  | mode_UP => if !negative && remainder != 0 then n + 1 else n
  | mode_NA => if remainder < half then n else n + 1

def roundWithFexp (fexp : Int -> Int) (m : mode) (r : Rat) : Rat :=
  if r = 0 then 0
  else
    let negative := r < 0
    let magnitude := absRat r
    let quantum := fexp (floorLog2Positive magnitude + 1)
    let mantissa := roundMagnitude m negative (magnitude / pow2Rat quantum)
    let rounded := (mantissa : Rat) * pow2Rat quantum
    if negative then -rounded else rounded

def genericFormat (fexp : Int -> Int) (r : Rat) : Prop :=
  Exists fun m : mode => Exists fun input : Rat => roundWithFexp fexp m input = r

private def overflow (fmt : Format) (m : mode) (negative : Bool) : BinaryFloat fmt :=
  match m with
  | mode_NE | mode_NA => infinity fmt negative
  | mode_ZR => maxFinite fmt negative
  | mode_DN => if negative then infinity fmt true else maxFinite fmt false
  | mode_UP => if negative then maxFinite fmt true else infinity fmt false

def ofRat (fmt : Format) (m : mode) (r : Rat) : BinaryFloat fmt :=
  if r = 0 then zero fmt false
  else
    let negative := r < 0
    let magnitude := absRat r
    let log2 := floorLog2Positive magnitude
    let quantum := max fmt.minSubnormalExponent (log2 - Int.ofNat fmt.fracBits)
    let roundedMantissa := roundMagnitude m negative (magnitude / pow2Rat quantum)
    if roundedMantissa <= 0 then zero fmt negative
    else
      let mantissa0 := roundedMantissa.toNat
      let carryLimit := 2 * fmt.fractionModulus
      let mantissa := if carryLimit <= mantissa0 then mantissa0 / 2 else mantissa0
      let quantum := if carryLimit <= mantissa0 then quantum + 1 else quantum
      if mantissa < fmt.fractionModulus then
        pack fmt negative 0 mantissa
      else
        let expField := quantum + Int.ofNat fmt.bias + Int.ofNat fmt.fracBits
        if Int.ofNat fmt.exponentMax <= expField then overflow fmt m negative
        else if expField <= 0 then pack fmt negative 0 mantissa
        else pack fmt negative expField.toNat (mantissa - fmt.fractionModulus)

def compare {fmt : Format} (x y : BinaryFloat fmt) : Option Ordering :=
  if isNaNBool x || isNaNBool y then none
  else
    let rx := finiteToRat x
    let ry := finiteToRat y
    if isInfBool x then
      if isInfBool y then
        if sign x = sign y then some .eq
        else if sign x then some .lt else some .gt
      else if sign x then some .lt else some .gt
    else if isInfBool y then
      if sign y then some .gt else some .lt
    else if rx < ry then some .lt
    else if ry < rx then some .gt
    else some .eq

def neg {fmt : Format} (x : BinaryFloat fmt) : BinaryFloat fmt :=
  if isNaNBool x then nan fmt
  else pack fmt (!sign x) (exponent x) (fraction x)

private def zeroSignForAdd (m : mode) (x y : Bool) : Bool :=
  match m with
  | mode_DN => x || y
  | _ => x && y

def add (fmt : Format) (m : mode) (x y : BinaryFloat fmt) : BinaryFloat fmt :=
  if isNaNBool x || isNaNBool y then nan fmt
  else if isInfBool x then
    if isInfBool y && sign x != sign y then nan fmt else infinity fmt (sign x)
  else if isInfBool y then infinity fmt (sign y)
  else
    let result := finiteToRat x + finiteToRat y
    if result = 0 then zero fmt (zeroSignForAdd m (sign x) (sign y))
    else ofRat fmt m result

def sub (fmt : Format) (m : mode) (x y : BinaryFloat fmt) : BinaryFloat fmt :=
  add fmt m x (neg y)

def mul (fmt : Format) (m : mode) (x y : BinaryFloat fmt) : BinaryFloat fmt :=
  let negative := sign x != sign y
  if isNaNBool x || isNaNBool y then nan fmt
  else if (isInfBool x && isZeroBool y) || (isZeroBool x && isInfBool y) then nan fmt
  else if isInfBool x || isInfBool y then infinity fmt negative
  else if isZeroBool x || isZeroBool y then zero fmt negative
  else ofRat fmt m (finiteToRat x * finiteToRat y)

def div (fmt : Format) (m : mode) (x y : BinaryFloat fmt) : BinaryFloat fmt :=
  let negative := sign x != sign y
  if isNaNBool x || isNaNBool y then nan fmt
  else if isInfBool x && isInfBool y then nan fmt
  else if isInfBool x then infinity fmt negative
  else if isInfBool y then zero fmt negative
  else if isZeroBool y then
    if isZeroBool x then nan fmt else infinity fmt negative
  else if isZeroBool x then zero fmt negative
  else ofRat fmt m (finiteToRat x / finiteToRat y)

theorem bitsOf_nonneg {fmt : Format} (x : BinaryFloat fmt) :
    0 <= bitsOf x :=
  Int.ofNat_zero_le x.toNat

theorem bitsOf_lt_modulus {fmt : Format} (x : BinaryFloat fmt) :
    bitsOf x < Int.ofNat fmt.modulus := by
  exact Int.ofNat_lt.mpr x.isLt

end BinaryFloat

def binary32Format : Format where
  fracBits := 23
  expBits := 8

def binary64Format : Format where
  fracBits := 52
  expBits := 11

def binary128Format : Format where
  fracBits := 112
  expBits := 15

abbrev binary32 := BinaryFloat binary32Format
abbrev binary64 := BinaryFloat binary64Format
abbrev binary128 := BinaryFloat binary128Format

end Flocq.Internal.IEEE
