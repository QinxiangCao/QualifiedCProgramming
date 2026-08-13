/-
Coq inventory from `unifysl-prp/ShallowQuantifierLogic/ModelConstrEX.v`.

Active declarations:
- `Model_L`
- `ExpDefinition_Model`, field `model2exp`
- `Model2Exp`
- `Model2Exp_Normal`
- `expL`
- `Model2Derivable1`
- `Model2ExpDeduction`
-/

import Unifysl.ShallowQuantifierLogic.ProofTheory

universe u v

namespace Unifysl
namespace ShallowQuantifierLogic
namespace ModelConstrEX

instance Model_L (M : Model.{u}) : Language.{u} where
  expr := @Model.model M -> Prop

class ExpDefinition_Model {M : Model.{u}}
    (expL : ShallowExistsLanguage.{u, v} (Model_L M)) : Prop where
  model2exp :
    forall {A : Type v} (x : A -> @Language.expr (Model_L M)),
      @exp (Model_L M) expL A x = fun m => exists a, x a m

def Model2Exp (M : Model.{u}) :
    ShallowExistsLanguage.{u, v} (Model_L M) where
  exp := fun {A} x m => exists a : A, x a m

theorem Model2Exp_Normal (M : Model.{u}) :
    ExpDefinition_Model (Model2Exp.{u, v} M) := by
  constructor
  intro A x
  rfl

instance expL (M : Model.{u}) :
    ShallowExistsLanguage.{u, v} (Model_L M) where
  exp := fun {A} x m => exists a : A, x a m

instance Model2Derivable1 (M : Model.{u}) : Derivable1 (Model_L M) where
  derivable1 := fun x y => forall m : @Model.model M, x m -> y m

abbrev GammaD1 (M : Model.{u}) : Derivable1 (Model_L M) :=
  Model2Derivable1 M

theorem Model2ExpDeduction (M : Model.{u}) :
    @ShallowExistsDeduction.{u, v} (Model_L M) (expL.{u, v} M)
      (Model2Derivable1 M) := by
  constructor
  · intro A P Q x h m hP
    exact ⟨x, h m hP⟩
  · intro A P Q h m hExp
    rcases hExp with ⟨a, ha⟩
    exact h a m ha

end ModelConstrEX
end ShallowQuantifierLogic
end Unifysl
