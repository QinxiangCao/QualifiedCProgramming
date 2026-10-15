import Flocq.Internal.IEEE
import Mathlib.Data.Int.Log
import Mathlib.Data.Real.Archimedean

/-!
Lean `Real` implementation kernel used behind the source-shaped Flocq API.
This module has no Coq source-file counterpart and must not be counted as a
migrated Flocq source module.
-/

namespace Flocq.Internal.RealRound

open Flocq.IEEE754
open Flocq.Internal.IEEE
open Flocq.Internal.IEEE.BinaryFloat

noncomputable def pow2 (e : Int) : Real :=
  (2 : Real) ^ e

noncomputable def abs (x : Real) : Real :=
  |x|

noncomputable def floorLog2 (x : Real) : Int :=
  Int.log 2 x

def fltExp (emin : Int) (precision : Nat) (e : Int) : Int :=
  max (e - Int.ofNat precision) emin

noncomputable def magnitude (x : Real) : Int :=
  if x = 0 then 0 else floorLog2 (abs x) + 1

noncomputable def cexp (fexp : Int -> Int) (x : Real) : Int :=
  fexp (magnitude x)

noncomputable def scaledMantissa (fexp : Int -> Int) (x : Real) : Real :=
  x * pow2 (-cexp fexp x)

noncomputable def trunc (x : Real) : Int :=
  if x < 0 then Int.ceil x else Int.floor x

noncomputable def f2r (mantissa exponent : Int) : Real :=
  (mantissa : Real) * pow2 exponent

namespace Internal

noncomputable def roundMagnitude (m : mode) (negative : Bool)
    (x : Real) : Int :=
  let n := Int.floor x
  let remainder := x - n
  let half : Real := 1 / 2
  match m with
  | mode_NE =>
      if remainder < half then n
      else if half < remainder then n + 1
      else if n % 2 = 0 then n else n + 1
  | mode_ZR => n
  | mode_DN => if negative then if remainder = 0 then n else n + 1 else n
  | mode_UP => if negative then n else if remainder = 0 then n else n + 1
  | mode_NA => if remainder < half then n else n + 1

end Internal

noncomputable def roundWithFexp (fexp : Int -> Int) (m : mode)
    (r : Real) : Real :=
  if r = 0 then 0
  else
    let negative := decide (r < 0)
    let magnitude := abs r
    let quantum := fexp (floorLog2 magnitude + 1)
    let mantissa := Internal.roundMagnitude m negative (magnitude / pow2 quantum)
    let rounded := (mantissa : Real) * pow2 quantum
    if negative then -rounded else rounded

def genericFormat (fexp : Int -> Int) (r : Real) : Prop :=
  r = f2r (trunc (scaledMantissa fexp r)) (cexp fexp r)

theorem genericFormat_of_representation (fexp : Int -> Int) (r : Real)
    (mantissa : Int)
    (h : r = f2r mantissa (cexp fexp r)) : genericFormat fexp r := by
  rw [genericFormat]
  have hpow : pow2 (cexp fexp r) * pow2 (-cexp fexp r) = 1 := by
    rw [pow2, pow2, ← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    simp
  have hscaled : scaledMantissa fexp r = (mantissa : Real) := by
    simp only [scaledMantissa]
    calc
      r * pow2 (-cexp fexp r) =
          ((mantissa : Real) * pow2 (cexp fexp r)) *
            pow2 (-cexp fexp r) := congrArg
              (fun x : Real => x * pow2 (-cexp fexp r)) h
      _ = (mantissa : Real) *
          (pow2 (cexp fexp r) * pow2 (-cexp fexp r)) := by ring
      _ = (mantissa : Real) := by rw [hpow, mul_one]
  rw [hscaled]
  simpa [trunc, f2r] using h

theorem genericFormat_f2r_of_cexp_le (fexp : Int -> Int)
    (mantissa exponent : Int)
    (hcexp : cexp fexp (f2r mantissa exponent) <= exponent) :
    genericFormat fexp (f2r mantissa exponent) := by
  by_cases hm : mantissa = 0
  · subst mantissa
    simp [genericFormat, f2r, scaledMantissa, trunc]
  rw [genericFormat]
  let shift : Nat := (exponent - cexp fexp (f2r mantissa exponent)).toNat
  have hshift : (shift : Int) = exponent - cexp fexp (f2r mantissa exponent) := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hcexp)
  let integerMantissa : Int := mantissa * (2 : Int) ^ shift
  have hpow :
      pow2 exponent * pow2 (-cexp fexp (f2r mantissa exponent)) =
        ((2 : Int) ^ shift : Int) := by
    rw [pow2, pow2, ← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    rw [← sub_eq_add_neg, ← hshift]
    simp [zpow_natCast]
  have hscaled :
      scaledMantissa fexp (f2r mantissa exponent) =
        (integerMantissa : Real) := by
    rw [scaledMantissa]
    change ((mantissa : Real) * pow2 exponent) *
      pow2 (-cexp fexp (f2r mantissa exponent)) = (integerMantissa : Real)
    rw [mul_assoc, hpow]
    simp [integerMantissa]
  rw [hscaled]
  have htrunc : trunc (integerMantissa : Real) = integerMantissa := by
    simp [trunc]
  rw [htrunc]
  change (mantissa : Real) * pow2 exponent =
    (integerMantissa : Real) * pow2 (cexp fexp (f2r mantissa exponent))
  rw [show (integerMantissa : Real) =
      (mantissa : Real) * (2 : Real) ^ (shift : Int) by
    simp [integerMantissa, zpow_natCast]]
  simp only [pow2]
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
  rw [hshift]
  congr 2
  omega

theorem magnitude_pow2 (e : Int) : magnitude (pow2 e) = e + 1 := by
  have hpos : 0 < pow2 e := by
    exact zpow_pos (by norm_num : (0 : Real) < 2) e
  rw [magnitude, if_neg hpos.ne']
  rw [abs, abs_of_pos hpos]
  rw [floorLog2]
  exact congrArg (fun z : Int => z + 1)
    (Int.log_zpow (R := Real) (by decide : 1 < 2) e)

theorem genericFormat_pow2 (emin : Int) (precision : Nat)
    (hp : 0 < precision) (e : Int) (hemin : emin <= e) :
    genericFormat (fltExp emin precision) (pow2 e) := by
  rw [show pow2 e = f2r 1 e by simp [f2r]]
  apply genericFormat_f2r_of_cexp_le _ _ e
  rw [show f2r 1 e = pow2 e by simp [f2r]]
  rw [cexp, magnitude_pow2]
  simp [fltExp]
  omega

theorem roundMagnitude_bounds (m : mode) (negative : Bool)
    (x : Real) (bound : Int) (hx : 0 <= x) (hxb : x < (bound : Real)) :
    0 <= Internal.roundMagnitude m negative x /\
      Internal.roundMagnitude m negative x <= bound := by
  have hfloor0 : 0 <= Int.floor x :=
    (Int.le_floor).2 (by simpa using hx)
  have hfloorlt : Int.floor x < bound := (Int.floor_lt).2 hxb
  cases m <;> simp only [Internal.roundMagnitude]
  · repeat' first | split | constructor <;> omega
  · omega
  · repeat' first | split | constructor <;> omega
  · repeat' first | split | constructor <;> omega
  · repeat' first | split | constructor <;> omega

theorem magnitude_neg_pow2 (e : Int) : magnitude (-pow2 e) = e + 1 := by
  have hpos : 0 < pow2 e := zpow_pos (by norm_num) e
  rw [magnitude, if_neg (neg_ne_zero.mpr (ne_of_gt hpos))]
  change floorLog2 |-pow2 e| + 1 = e + 1
  rw [abs_neg, abs_of_pos hpos]
  rw [floorLog2]
  exact congrArg (fun z : Int => z + 1)
    (Int.log_zpow (R := Real) (by decide : 1 < 2) e)

theorem genericFormat_signed_pow2 (emin : Int) (precision : Nat)
    (hp : 0 < precision) (negative : Bool) (e : Int) (hemin : emin <= e) :
    genericFormat (fltExp emin precision)
      (if negative then -pow2 e else pow2 e) := by
  cases negative
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact genericFormat_pow2 emin precision hp e hemin
  · simp only [↓reduceIte]
    rw [show -pow2 e = f2r (-1) e by simp [f2r]]
    apply genericFormat_f2r_of_cexp_le _ _ e
    rw [show f2r (-1) e = -pow2 e by simp [f2r]]
    rw [cexp, magnitude_neg_pow2]
    simp [fltExp]
    omega

theorem roundWithFexp_generic (emin : Int) (precision : Nat)
    (hp : 0 < precision) (m : mode) (r : Real) :
    genericFormat (fltExp emin precision)
      (roundWithFexp (fltExp emin precision) m r) := by
  by_cases hr : r = 0
  · subst r
    simp [roundWithFexp, genericFormat, f2r, scaledMantissa, trunc]
  let negative : Bool := decide (r < 0)
  let q : Real := abs r
  let exponent : Int := floorLog2 q + 1
  let quantum : Int := fltExp emin precision exponent
  let n : Int := Internal.roundMagnitude m negative (q / pow2 quantum)
  let bound : Int := (2 : Int) ^ precision
  have hqpos : 0 < q := by
    simp [q, abs, abs_pos, hr]
  have hpowqpos : 0 < pow2 quantum := by
    exact zpow_pos (by norm_num : (0 : Real) < 2) quantum
  have hquantum_emin : emin <= quantum := by
    simp [quantum, fltExp]
  have hexponent_quantum : exponent <= quantum + (precision : Int) := by
    simp [quantum, fltExp]
    omega
  have hqpow : q < pow2 exponent := by
    exact Int.lt_zpow_succ_log_self (R := Real) (by decide : 1 < 2) q
  have hqpow' : q < pow2 (quantum + (precision : Int)) :=
    hqpow.trans_le (zpow_le_zpow_right₀ (by norm_num : (1 : Real) <= 2)
      hexponent_quantum)
  have hscaled0 : 0 <= q / pow2 quantum :=
    div_nonneg hqpos.le hpowqpos.le
  have hboundcast : (bound : Real) = pow2 (precision : Int) := by
    simp [bound, pow2, zpow_natCast]
  have hbound_mul : (bound : Real) * pow2 quantum =
      pow2 (quantum + (precision : Int)) := by
    rw [hboundcast, pow2, pow2, pow2, ← zpow_add₀
      (by norm_num : (2 : Real) ≠ 0)]
    congr 1
    omega
  have hscaledlt : q / pow2 quantum < (bound : Real) := by
    apply (div_lt_iff₀ hpowqpos).2
    calc
      q < pow2 (quantum + (precision : Int)) := hqpow'
      _ = (bound : Real) * pow2 quantum := hbound_mul.symm
  have hnbounds : 0 <= n /\ n <= bound := by
    exact roundMagnitude_bounds m negative (q / pow2 quantum) bound
      hscaled0 hscaledlt
  let signedMantissa : Int := if negative then -n else n
  have hround : roundWithFexp (fltExp emin precision) m r =
      f2r signedMantissa quantum := by
    rw [roundWithFexp, if_neg hr]
    simp only
    change (if negative then -((n : Real) * pow2 quantum)
      else (n : Real) * pow2 quantum) = f2r signedMantissa quantum
    cases hnegative : negative <;> simp [hnegative, signedMantissa, f2r]
  rw [hround]
  by_cases hn0 : n = 0
  · have hsigned0 : signedMantissa = 0 := by simp [signedMantissa, hn0]
    rw [hsigned0]
    simp [genericFormat, f2r, scaledMantissa, trunc]
  have hnpos : 0 < n := lt_of_le_of_ne hnbounds.1 (Ne.symm hn0)
  by_cases hnlt : n < bound
  · apply genericFormat_f2r_of_cexp_le
    have hsignedAbs : abs (f2r signedMantissa quantum) =
        (n : Real) * pow2 quantum := by
      rw [abs, f2r, abs_mul]
      have hsigned : |(signedMantissa : Real)| = (n : Real) := by
        cases hnegative : negative <;>
          simp [hnegative, signedMantissa, hnbounds.1]
      rw [hsigned, abs_of_pos hpowqpos]
    have hvaluepos : 0 < abs (f2r signedMantissa quantum) := by
      rw [hsignedAbs]
      positivity
    have hvaluelt : abs (f2r signedMantissa quantum) <
        pow2 (quantum + (precision : Int)) := by
      rw [hsignedAbs]
      have hncast : (n : Real) < (bound : Real) := by exact_mod_cast hnlt
      calc
        (n : Real) * pow2 quantum < (bound : Real) * pow2 quantum :=
          mul_lt_mul_of_pos_right hncast hpowqpos
        _ = pow2 (quantum + (precision : Int)) := hbound_mul
    have hmagnitude : magnitude (f2r signedMantissa quantum) <=
        quantum + (precision : Int) := by
      have hvalue_ne : f2r signedMantissa quantum ≠ 0 := by
        intro hzero
        rw [hzero, abs, abs_zero] at hvaluepos
        exact lt_irrefl 0 hvaluepos
      rw [magnitude, if_neg hvalue_ne]
      have hlog : floorLog2 (abs (f2r signedMantissa quantum)) <
          quantum + (precision : Int) := by
        exact (Int.lt_zpow_iff_log_lt (R := Real) (by decide : 1 < 2)
          hvaluepos).mp hvaluelt
      omega
    rw [cexp]
    simp [fltExp]
    omega
  · have hneq : n = bound := by omega
    have hpowRepresentation : f2r signedMantissa quantum =
        if negative then -pow2 (quantum + (precision : Int))
        else pow2 (quantum + (precision : Int)) := by
      cases hnegative : negative <;>
        simp [hnegative, signedMantissa, hneq, f2r, hbound_mul]
    rw [hpowRepresentation]
    exact genericFormat_signed_pow2 emin precision hp negative
      (quantum + (precision : Int)) (by omega)

noncomputable def finiteToReal {fmt : Format} (x : BinaryFloat fmt) : Real :=
  let frac := fraction x
  let exp := exponent x
  let mantissa := if exp = 0 then frac else fmt.fractionModulus + frac
  let unbiased :=
    if exp = 0 then fmt.minSubnormalExponent
    else Int.ofNat exp - Int.ofNat fmt.bias - Int.ofNat fmt.fracBits
  let magnitude := (Int.ofNat mantissa : Real) * pow2 unbiased
  if sign x then -magnitude else magnitude

noncomputable def toReal? {fmt : Format} (x : BinaryFloat fmt) : Option Real :=
  if isFiniteBool x then some (finiteToReal x) else none

noncomputable def toRealTotal {fmt : Format} (x : BinaryFloat fmt) : Real :=
  (toReal? x).getD 0

def Internal.overflow (fmt : Format) (m : mode)
    (negative : Bool) : BinaryFloat fmt :=
  match m with
  | mode_NE | mode_NA => infinity fmt negative
  | mode_ZR => maxFinite fmt negative
  | mode_DN => if negative then infinity fmt true else maxFinite fmt false
  | mode_UP => if negative then maxFinite fmt true else infinity fmt false

noncomputable def ofReal (fmt : Format) (m : mode) (r : Real) : BinaryFloat fmt :=
  if r = 0 then zero fmt false
  else
    let negative := decide (r < 0)
    let magnitude := abs r
    let log2 := floorLog2 magnitude
    let quantum := max fmt.minSubnormalExponent (log2 - Int.ofNat fmt.fracBits)
    let roundedMantissa := Internal.roundMagnitude m negative (magnitude / pow2 quantum)
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
        if Int.ofNat fmt.exponentMax <= expField then Internal.overflow fmt m negative
        else if expField <= 0 then pack fmt negative 0 mantissa
        else pack fmt negative expField.toNat (mantissa - fmt.fractionModulus)

end Flocq.Internal.RealRound
