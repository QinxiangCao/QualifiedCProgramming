/- Coq inventory: unifysl-prp/MetaLogicInj/Syntax.v
   - Class CoqPropLanguage (field: coq_prop)
   - Module CoqPropInLogicNotation
   - Notation: `!! e`
-/

import Unifysl.GeneralLogic.Base

universe u

namespace Unifysl

class CoqPropLanguage (L : Language.{u}) : Type (u + 1) where
  coq_prop : Prop -> @Language.expr L

export CoqPropLanguage (coq_prop)

namespace CoqPropInLogicNotation

scoped notation:25 "!! " e:25 => coq_prop e

end CoqPropInLogicNotation

end Unifysl
