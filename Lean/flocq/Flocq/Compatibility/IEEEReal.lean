import Flocq.Core.Core
import Flocq.IEEE754.Binary
import Flocq.Internal.RealRound

namespace Flocq.Compatibility.IEEEReal

/-!
Implementation adapter between the source-shaped Flocq modules and Lean's
`BitVec`/`Real` representation. This file has no Coq source-file counterpart;
it must not be counted as a migrated Flocq source module.
-/

open Flocq.IEEE754
open Flocq.Core

noncomputable abbrev implementation_round :=
  Flocq.Internal.RealRound.roundWithFexp
abbrev implementation_generic_format :=
  Flocq.Internal.RealRound.genericFormat
abbrev implementation_generic_format_round_FLT :=
  Flocq.Internal.RealRound.roundWithFexp_generic
noncomputable abbrev binary_normalize := Flocq.Internal.RealRound.ofReal
noncomputable abbrev finite_to_real {fmt : Format} (x : BinaryFloat fmt) : Real :=
  Flocq.Internal.RealRound.finiteToReal x
noncomputable abbrev to_real? {fmt : Format} (x : BinaryFloat fmt) : Option Real :=
  Flocq.Internal.RealRound.toReal? x
noncomputable abbrev to_real_total {fmt : Format} (x : BinaryFloat fmt) : Real :=
  Flocq.Internal.RealRound.toRealTotal x

private theorem mag_val_eq (beta : radix) (x : Real) :
    (mag beta x).mag_val =
      if x = 0 then 0 else Int.log beta.radix_val.toNat |x| + 1 := by
  by_cases hx : x = 0 <;> simp [mag, hx]

theorem round_FLT_generic_format (emin : Int) (precision : Nat)
    (hp : 0 < precision) (m : mode) (x : Real) :
    generic_format radix2 (FLT_exp emin (Int.ofNat precision))
      (Flocq.Internal.RealRound.roundWithFexp
        (Flocq.Internal.RealRound.fltExp emin precision) m x) := by
  simpa [generic_format, F2R, scaled_mantissa, cexp, mag_val_eq,
    radix2, bpow, Ztrunc,
    FLT_exp, Flocq.Internal.RealRound.genericFormat,
    Flocq.Internal.RealRound.f2r, Flocq.Internal.RealRound.scaledMantissa,
    Flocq.Internal.RealRound.cexp, Flocq.Internal.RealRound.magnitude,
    Flocq.Internal.RealRound.floorLog2, Flocq.Internal.RealRound.pow2,
    Flocq.Internal.RealRound.trunc, Flocq.Internal.RealRound.fltExp,
    Flocq.Internal.RealRound.abs] using
      Flocq.Internal.RealRound.roundWithFexp_generic emin precision hp m x

end Flocq.Compatibility.IEEEReal
