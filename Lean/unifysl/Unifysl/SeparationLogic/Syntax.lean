/- Coq inventory: unifysl-prp/SeparationLogic/Syntax.v
   - Class SepconLanguage (field: sepcon)
   - Class WandLanguage (field: wand)
   - Class EmpLanguage (field: emp)
   - Module SeparationLogicNotation
   - Notations: `x * y`, `x -* y`
   - Class IterSepconLanguage (field: iter_sepcon)
   - Class IterWandLanguage (field: iter_wand)
-/

import Unifysl.GeneralLogic.Base

universe u

namespace Unifysl

class SepconLanguage (L : Language.{u}) : Type (u + 1) where
  sepcon : @Language.expr L -> @Language.expr L -> @Language.expr L

export SepconLanguage (sepcon)

class WandLanguage (L : Language.{u}) : Type (u + 1) where
  wand : @Language.expr L -> @Language.expr L -> @Language.expr L

export WandLanguage (wand)

class EmpLanguage (L : Language.{u}) : Type (u + 1) where
  emp : @Language.expr L

export EmpLanguage (emp)

namespace SeparationLogicNotation

scoped infixl:40 " * " => sepcon
scoped infixr:55 " -* " => wand

end SeparationLogicNotation

class IterSepconLanguage (L : Language.{u}) : Type (u + 1) where
  iter_sepcon : List (@Language.expr L) -> @Language.expr L

export IterSepconLanguage (iter_sepcon)

class IterWandLanguage (L : Language.{u}) : Type (u + 1) where
  iter_wand : List (@Language.expr L) -> @Language.expr L -> @Language.expr L

export IterWandLanguage (iter_wand)

end Unifysl
