/- 
Coq inventory from `PropositionalLogic/Syntax.v`:
- Classes and fields:
  `AndLanguage.andp`, `OrLanguage.orp`, `FalseLanguage.falsep`,
  `NegLanguage.negp`, `IffLanguage.iffp`, `TrueLanguage.truep`,
  `IterAndLanguage.iter_andp`, `IterOrLanguage.iter_orp`.
- Notation from Coq:
  `&&`, `||`, `~~`, `FF`, `TT`.
- Coq notation `x <--> y` is not Lean-safe because `--` starts a line
  comment. Lean uses `x ⟷ y` for `iffp`.
-/

import Unifysl.MinimumLogic.Syntax
import Unifysl.GeneralLogic.Base

universe u

namespace Unifysl

class AndLanguage (L : Language.{u}) : Type (u + 1) where
  andp : @Language.expr L -> @Language.expr L -> @Language.expr L

export AndLanguage (andp)

class OrLanguage (L : Language.{u}) : Type (u + 1) where
  orp : @Language.expr L -> @Language.expr L -> @Language.expr L

export OrLanguage (orp)

class FalseLanguage (L : Language.{u}) : Type (u + 1) where
  falsep : @Language.expr L

export FalseLanguage (falsep)

class NegLanguage (L : Language.{u}) : Type (u + 1) where
  negp : @Language.expr L -> @Language.expr L

export NegLanguage (negp)

class IffLanguage (L : Language.{u}) : Type (u + 1) where
  iffp : @Language.expr L -> @Language.expr L -> @Language.expr L

export IffLanguage (iffp)

class TrueLanguage (L : Language.{u}) : Type (u + 1) where
  truep : @Language.expr L

export TrueLanguage (truep)

class IterAndLanguage (L : Language.{u}) : Type (u + 1) where
  iter_andp : List (@Language.expr L) -> @Language.expr L

export IterAndLanguage (iter_andp)

class IterOrLanguage (L : Language.{u}) : Type (u + 1) where
  iter_orp : List (@Language.expr L) -> @Language.expr L

export IterOrLanguage (iter_orp)

namespace PropositionalLanguageNotation

scoped infixl:40 " && " => Unifysl.andp
scoped infixl:50 " || " => Unifysl.orp
scoped infix:60 " ⟷ " => Unifysl.iffp
scoped prefix:35 "~~ " => Unifysl.negp
scoped notation "FF" => Unifysl.falsep
scoped notation "TT" => Unifysl.truep

end PropositionalLanguageNotation

end Unifysl
