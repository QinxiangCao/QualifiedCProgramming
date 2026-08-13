/- 
Coq inventory from `MinimumLogic/Semantics/Trivial.v`:
- Module function `Semantics.impp`.
- Class `TrivialMinimumSemantics` with field `denote_impp`.
- Lemma `sat_impp`.

Lean note: `Semantics` is already the existing class from
`GeneralLogic/Base.lean`. Lean permits adding the connective function under
the same namespace as `Semantics.impp`, matching the Coq name without
changing the class.
-/

import Unifysl.GeneralLogic.Base
import Unifysl.MinimumLogic.Syntax

universe u v

namespace Unifysl

namespace Semantics

def impp {M : Type u} (X Y : Ensemble M) : Ensemble M :=
  fun m => X m -> Y m

end Semantics

class TrivialMinimumSemantics (L : Language.{u}) [MinimumLanguage L]
    (MD : Model.{v}) (SM : Semantics L MD) : Type (max (u + 1) (v + 1)) where
  denote_impp :
    forall x y : @Language.expr L,
      Same_set (@Model.model MD)
        (SM.denotation (x ⟶ y))
        (Semantics.impp (SM.denotation x) (SM.denotation y))

theorem sat_impp {L : Language.{u}} [MinimumLanguage L]
    {MD : Model.{v}} [SM : Semantics L MD]
    [tminSM : TrivialMinimumSemantics L MD SM] :
    forall (m : @Model.model MD) (x y : @Language.expr L),
      satisfies m (x ⟶ y) <-> (satisfies m x -> satisfies m y) := by
  intro m x y
  have h := TrivialMinimumSemantics.denote_impp (L := L) (MD := MD) (SM := SM) x y
  constructor
  · intro hxy hx
    exact h.left m hxy hx
  · intro hxy
    exact h.right m hxy

end Unifysl
