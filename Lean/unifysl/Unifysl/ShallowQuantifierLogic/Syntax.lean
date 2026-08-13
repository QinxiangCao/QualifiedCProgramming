/-
Coq inventory from `unifysl-prp/ShallowQuantifierLogic/Syntax.v`.

Classes/fields:
- `ShallowExistsLanguage.exp`
- `ShallowForallLanguage.allp`

Coq notation in `ShallowQuantifierLanguageNotation` is preserved below as
comments only. No active Lean notation is introduced here.
-/

import Unifysl.MinimumLogic.Syntax
import Unifysl.PropositionalLogic.Syntax

universe u v

namespace Unifysl

class ShallowExistsLanguage (L : Language.{u}) : Type (max (u + 1) (v + 1)) where
  exp {A : Type v} : (A -> @Language.expr L) -> @Language.expr L

export ShallowExistsLanguage (exp)

class ShallowForallLanguage (L : Language.{u}) : Type (max (u + 1) (v + 1)) where
  allp {A : Type v} : (A -> @Language.expr L) -> @Language.expr L

export ShallowForallLanguage (allp)

namespace ShallowQuantifierLanguageNotation

-- Coq notation only:
-- Notation "∃ x , y" := (existsp x y) (at level 30, no associativity) : syntax.
-- Notation "∀ x , y" := (forallp x y) (at level 30, no associativity) : syntax.
-- Notation "p [ t \ x ]" := (substp p t x) (at level 20, no associativity) : syntax.

end ShallowQuantifierLanguageNotation

end Unifysl
