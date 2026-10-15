import Flocq.Core.Defs

namespace Flocq.Core.Generic_fmt

open Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs

/-! Lean migration of the FloatLib-reached slice of `flocq/src/Core/Generic_fmt.v`. -/

noncomputable def cexp (beta : radix) (fexp : Int -> Int) (x : Real) : Int :=
  fexp ((mag beta x : mag_prop beta x) : Int)

noncomputable def scaled_mantissa (beta : radix) (fexp : Int -> Int)
    (x : Real) : Real :=
  x * bpow beta (-cexp beta fexp x)

def generic_format (beta : radix) (fexp : Int -> Int) (x : Real) : Prop :=
  x = F2R (float.mk (Ztrunc (scaled_mantissa beta fexp x))
    (cexp beta fexp x) : float beta)

noncomputable def round (beta : radix) (fexp : Int -> Int)
    (rnd : Real -> Int) (x : Real) : Real :=
  F2R (float.mk (rnd (scaled_mantissa beta fexp x))
    (cexp beta fexp x) : float beta)

/- `Znearest` and `ZnearestA` occur later in the same Coq source file. -/
noncomputable def Znearest (choice : Int -> Bool) (x : Real) : Int :=
  let n := Zfloor x
  let remainder := x - (n : Real)
  if remainder < (1 / 2 : Real) then n
  else if (1 / 2 : Real) < remainder then Zceil x
  else if choice n then Zceil x else n

noncomputable abbrev ZnearestA : Real -> Int :=
  Znearest fun n => decide (0 <= n)

end Flocq.Core.Generic_fmt

namespace Flocq.Core
export Generic_fmt (cexp scaled_mantissa generic_format round Znearest ZnearestA)
end Flocq.Core
