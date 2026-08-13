/-
Coq inventory from
`unifysl-prp-8.20/MinimumLogic/ShallowEmbedded/ModelLanguageMinimumLogic.v`.

Active declarations:
- `Model2Impp`
- `ImppDefinition_Model`, field `model2impp`
- `Model2Impp_Normal`
- `kminSM`

The declarations are kept under
`Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic` and use the
L4 model-language base module.
-/

import Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage
import Unifysl.GeneralLogic.ProofTheory.BasicDeduction
import Unifysl.MinimumLogic.Syntax
import Unifysl.MinimumLogic.ProofTheory.Minimum
import Unifysl.MinimumLogic.Semantics.Trivial
import Unifysl.MinimumLogic.Semantics.Kripke
import Unifysl.MinimumLogic.Semantics.SemanticEquiv

universe u

namespace Unifysl
namespace MinimumLogic
namespace ShallowEmbedded
namespace ModelLanguageMinimumLogic

abbrev Model_L (M : Model.{u}) : Language.{u} :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model_L M

abbrev modelR (M : Model.{u}) : KI.Relation (@Model.model M) :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.modelR M

abbrev SM (M : Model.{u}) : Semantics (Model_L M) M :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.SM M

def Model2Impp (M : Model.{u}) : MinimumLanguage (Model_L M) where
  impp := fun x y m => x m -> y m

class ImppDefinition_Model {M : Model.{u}}
    (minL : MinimumLanguage (Model_L M)) : Prop where
  model2impp :
    forall x y : @Language.expr (Model_L M),
      @impp (Model_L M) minL x y = fun m => x m -> y m

theorem Model2Impp_Normal (M : Model.{u}) :
    ImppDefinition_Model (M := M) (Model2Impp M) := by
  constructor
  intro x y
  rfl

instance kminSM (M : Model.{u}) :
    @KripkeMinimumSemantics (Model_L M) (Model2Impp M) M
      (unit_kMD M) Unit.unit (modelR M) (SM M) := by
  letI : MinimumLanguage (Model_L M) := Model2Impp M
  exact @Trivial2Kripke (Model_L M) (Model2Impp M) M (SM M)
    (by
      constructor
      intro x y
      constructor
      · intro m hxy hx
        exact hxy hx
      · intro m hxy hx
        exact hxy hx)

end ModelLanguageMinimumLogic
end ShallowEmbedded
end MinimumLogic
end Unifysl
