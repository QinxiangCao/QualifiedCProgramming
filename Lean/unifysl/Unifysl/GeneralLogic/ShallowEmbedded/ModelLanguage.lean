/-
Coq inventory from `unifysl-prp-8.20/GeneralLogic/ShallowEmbedded/ModelLanguage.v`.

Active declarations:
- `Model_L`
- `Model2Provable`
- `ProvableDefinition_Model`, field `model2provable`
- `Model2Provable_Normal`
- `Model2Derivable1`
- `Derivable1Definition_Model`, field `model2deriable1`
- `Model2Derivable1_Normal`
- `modelR`
- `SM`

The Coq file defines these declarations inside section `ModelLanguage`.
Lean keeps them in namespace `Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage`
to avoid root-name collisions with older model-language helpers.
-/

import Unifysl.GeneralLogic.Base
import Unifysl.GeneralLogic.KripkeModel

universe u

namespace Unifysl
namespace GeneralLogic
namespace ShallowEmbedded
namespace ModelLanguage

instance Model_L (M : Model.{u}) : Language.{u} where
  expr := @Model.model M -> Prop

instance Model2Provable (M : Model.{u}) : Provable (Model_L M) where
  provable := fun x => forall m, x m

class ProvableDefinition_Model {M : Model.{u}}
    (GammaP : Provable (Model_L M)) : Prop where
  model2provable :
    forall x : @Language.expr (Model_L M),
      @provable (Model_L M) GammaP x = forall m, x m

theorem Model2Provable_Normal (M : Model.{u}) :
    ProvableDefinition_Model (M := M) (Model2Provable M) := by
  constructor
  intro x
  rfl

instance Model2Derivable1 (M : Model.{u}) : Derivable1 (Model_L M) where
  derivable1 := fun x y => forall m, x m -> y m

class Derivable1Definition_Model {M : Model.{u}}
    (GammaD1 : Derivable1 (Model_L M)) : Prop where
  model2deriable1 :
    forall x y : @Language.expr (Model_L M),
      @derivable1 (Model_L M) GammaD1 x y = forall m, x m -> y m

theorem Model2Derivable1_Normal (M : Model.{u}) :
    Derivable1Definition_Model (M := M) (Model2Derivable1 M) := by
  constructor
  intro x y
  rfl

instance modelR (M : Model.{u}) : KI.Relation (@Model.model M) where
  Krelation := fun x y => x = y

instance SM (M : Model.{u}) : Semantics (Model_L M) M where
  denotation := fun x => x

end ModelLanguage
end ShallowEmbedded
end GeneralLogic
end Unifysl
