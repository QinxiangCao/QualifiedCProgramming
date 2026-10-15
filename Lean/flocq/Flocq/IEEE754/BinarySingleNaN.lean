import Flocq.Core.FLX
import Flocq.Core.Round_NE

namespace Flocq.IEEE754.BinarySingleNaN

open Flocq.Core.FLX Flocq.Core.Round_NE Flocq.Core.Raux Flocq.Core.Generic_fmt

/-! Lean migration of the `mode` and `round_mode` declarations from
`flocq/src/IEEE754/BinarySingleNaN.v`. -/

inductive mode where
  | mode_NE
  | mode_ZR
  | mode_DN
  | mode_UP
  | mode_NA

export mode (mode_NE mode_ZR mode_DN mode_UP mode_NA)

class Prec_lt_emax (prec emax : Int) : Prop where
  prec_lt_emax : prec < emax

abbrev Build_Prec_lt_emax (prec emax : Int)
    (h : prec < emax) : Prec_lt_emax prec emax :=
  ⟨h⟩

noncomputable def round_mode : mode -> Real -> Int
  | mode_NE => Flocq.Core.Round_NE.ZnearestE
  | mode_ZR => Flocq.Core.Raux.Ztrunc
  | mode_DN => Flocq.Core.Raux.Zfloor
  | mode_UP => Flocq.Core.Raux.Zceil
  | mode_NA => Flocq.Core.Generic_fmt.ZnearestA

end Flocq.IEEE754.BinarySingleNaN

namespace Flocq.IEEE754
export BinarySingleNaN
  (mode mode_NE mode_ZR mode_DN mode_UP mode_NA Prec_lt_emax
    Build_Prec_lt_emax round_mode)
end Flocq.IEEE754
