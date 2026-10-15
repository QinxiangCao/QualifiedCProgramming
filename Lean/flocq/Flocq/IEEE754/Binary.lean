import Flocq.Compatibility.IEEE
import Flocq.Internal.RealRound

namespace Flocq.IEEE754.Binary

open Flocq.Core.FLX Flocq.Core.Raux
open Flocq.IEEE754.BinarySingleNaN
open Flocq.IEEE754

/-!
Lean migration of the FloatLib-reached operational slice from
`flocq/src/IEEE754/Binary.v`.
-/

abbrev binary_float (prec emax : Int) : Type :=
  BinaryFloat (formatOfParameters prec emax)

def nan_pl (prec : Int) (payload : Nat) : Bool :=
  payload != 0 && payload < 2 ^ (prec - 1).toNat

def is_finite (prec emax : Int) (x : binary_float prec emax) : Bool :=
  BinaryFloat.isFiniteBool x

def is_nan (prec emax : Int) (x : binary_float prec emax) : Bool :=
  BinaryFloat.isNaNBool x

noncomputable def B2R (prec emax : Int) (x : binary_float prec emax) : Real :=
  if BinaryFloat.isFiniteBool x then (BinaryFloat.finiteToRat x : Real) else 0

def Bcompare (prec emax : Int) (x y : binary_float prec emax) : Option Ordering :=
  BinaryFloat.compare x y

def Bopp (prec emax : Int)
    (opp_nan : binary_float prec emax ->
      {x : binary_float prec emax // is_nan prec emax x = true})
    (x : binary_float prec emax) : binary_float prec emax :=
  if BinaryFloat.isNaNBool x then (opp_nan x).1 else BinaryFloat.neg x

private def apply_binary_nan (prec emax : Int)
    (nan_policy : binary_float prec emax -> binary_float prec emax ->
      {x : binary_float prec emax // is_nan prec emax x = true})
    (x y result : binary_float prec emax) : binary_float prec emax :=
  if BinaryFloat.isNaNBool result then (nan_policy x y).1 else result

def Bplus (prec emax : Int) (_ : Prec_gt_0 prec) (_ : Prec_lt_emax prec emax)
    (plus_nan : binary_float prec emax -> binary_float prec emax ->
      {x : binary_float prec emax // is_nan prec emax x = true})
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  apply_binary_nan prec emax plus_nan x y
    (BinaryFloat.add (formatOfParameters prec emax) m x y)

def Bminus (prec emax : Int) (_ : Prec_gt_0 prec) (_ : Prec_lt_emax prec emax)
    (minus_nan : binary_float prec emax -> binary_float prec emax ->
      {x : binary_float prec emax // is_nan prec emax x = true})
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  apply_binary_nan prec emax minus_nan x y
    (BinaryFloat.sub (formatOfParameters prec emax) m x y)

def Bmult (prec emax : Int) (_ : Prec_gt_0 prec) (_ : Prec_lt_emax prec emax)
    (mult_nan : binary_float prec emax -> binary_float prec emax ->
      {x : binary_float prec emax // is_nan prec emax x = true})
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  apply_binary_nan prec emax mult_nan x y
    (BinaryFloat.mul (formatOfParameters prec emax) m x y)

def Bdiv (prec emax : Int) (_ : Prec_gt_0 prec) (_ : Prec_lt_emax prec emax)
    (div_nan : binary_float prec emax -> binary_float prec emax ->
      {x : binary_float prec emax // is_nan prec emax x = true})
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  apply_binary_nan prec emax div_nan x y
    (BinaryFloat.div (formatOfParameters prec emax) m x y)

noncomputable def binary_normalize (prec emax : Int)
    (_ : Prec_gt_0 prec) (_ : Prec_lt_emax prec emax)
    (m : mode) (mantissa exponent : Int) (zero_sign : Bool) :
    binary_float prec emax :=
  let value := (mantissa : Real) * (2 : Real) ^ exponent
  if value = 0 then BinaryFloat.zero (formatOfParameters prec emax) zero_sign
  else Flocq.Internal.RealRound.ofReal (formatOfParameters prec emax) m value

end Flocq.IEEE754.Binary

namespace Flocq.IEEE754
export Binary
  (binary_float nan_pl is_finite is_nan B2R Bcompare Bopp Bplus Bminus Bmult
    Bdiv binary_normalize)
end Flocq.IEEE754
