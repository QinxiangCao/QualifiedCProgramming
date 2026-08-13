/- Coq inventory: unifysl-prp/MinimumLogic/Syntax.v
   - Class MinimumLanguage (field: impp)
   - Scope syntax
   - Coq notation: `x --> y`
   Lean note: exact ASCII `-->` cannot be used because Lean lexes `--`
   as a line comment. The safe Lean notation is global `x ⟶ y`.
-/

import Unifysl.GeneralLogic.Base

universe u

namespace Unifysl

class MinimumLanguage (L : Language.{u}) : Type (u + 1) where
  impp : @Language.expr L -> @Language.expr L -> @Language.expr L

export MinimumLanguage (impp)

end Unifysl

infixr:55 " ⟶ " => Unifysl.impp
