import Flocq.Core.Generic_fmt

namespace Flocq.Core.FLX

/-! Lean migration of `Prec_gt_0` from `flocq/src/Core/FLX.v`. -/

class Prec_gt_0 (prec : Int) : Prop where
  prec_gt_0 : 0 < prec

abbrev Build_Prec_gt_0 (prec : Int) (h : 0 < prec) : Prec_gt_0 prec :=
  ⟨h⟩

end Flocq.Core.FLX

namespace Flocq.Core
export FLX (Prec_gt_0 Build_Prec_gt_0)
end Flocq.Core
