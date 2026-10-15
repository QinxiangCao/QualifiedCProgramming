import Flocq.Core.Generic_fmt

namespace Flocq.Core.FLT

/-! Lean migration of the `FLT_exp` slice from `flocq/src/Core/FLT.v`. -/

def FLT_exp (emin precision e : Int) : Int :=
  max (e - precision) emin

end Flocq.Core.FLT

namespace Flocq.Core
export FLT (FLT_exp)
end Flocq.Core
