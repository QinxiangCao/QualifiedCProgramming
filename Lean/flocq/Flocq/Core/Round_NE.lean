import Flocq.Core.Generic_fmt

namespace Flocq.Core.Round_NE

open Flocq.Core.Generic_fmt

/-!
Lean migration of the `ZnearestE` notation reached from
`flocq/src/Core/Round_NE.v`. Coq defines it as `Znearest` with ties chosen
according to the parity of the lower integer.
-/

noncomputable abbrev ZnearestE : Real -> Int :=
  Znearest fun n => decide (n % 2 != 0)

end Flocq.Core.Round_NE

namespace Flocq.Core
export Round_NE (ZnearestE)
end Flocq.Core
