/-
Coq inventory from `unifysl-prp/ShallowQuantifierLogic/ModelConstrALL.v`.

Active declarations:
- `Model_L`
- `AllpDefinition_Model`, field `model2all`
- `Model2All`
- `Model2Allp_Normal`
- `allL`
- `Model2Derivable1`
- `Model2AllDeduction`
-/

import Unifysl.ShallowQuantifierLogic.ProofTheory

universe u v

namespace Unifysl
namespace ShallowQuantifierLogic
namespace ModelConstrALL

instance Model_L (M : Model.{u}) : Language.{u} where
  expr := @Model.model M -> Prop

class AllpDefinition_Model {M : Model.{u}}
    (allL : ShallowForallLanguage.{u, v} (Model_L M)) : Prop where
  model2all :
    forall {A : Type v} (x : A -> @Language.expr (Model_L M)),
      @allp (Model_L M) allL A x = fun m => forall a, x a m

def Model2All (M : Model.{u}) : ShallowForallLanguage.{u, v} (Model_L M) where
  allp := fun {A} x => fun m => forall a : A, x a m

theorem Model2Allp_Normal (M : Model.{u}) :
    AllpDefinition_Model (M := M) (Model2All M) := by
  constructor
  intro A x
  rfl

instance allL (M : Model.{u}) : ShallowForallLanguage.{u, v} (Model_L M) where
  allp := fun {A} x => fun m => forall a : A, x a m

instance Model2Derivable1 (M : Model.{u}) : Derivable1 (Model_L M) where
  derivable1 := fun x y => forall m : @Model.model M, x m -> y m

abbrev GammaD1 (M : Model.{u}) : Derivable1 (Model_L M) :=
  Model2Derivable1 M

theorem Model2AllDeduction (M : Model.{u}) :
    ShallowForallDeduction (Model_L M) (Model2Derivable1 M) := by
  constructor
  · intro A P Q h m hP a
    exact h a m hP
  · intro A P Q x h m hAll
    exact h m (hAll x)

end ModelConstrALL
end ShallowQuantifierLogic
end Unifysl
