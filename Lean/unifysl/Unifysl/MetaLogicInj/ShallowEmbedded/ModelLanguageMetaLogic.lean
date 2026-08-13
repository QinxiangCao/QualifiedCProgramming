/-
Coq inventory from
`unifysl-prp-8.20/MetaLogicInj/ShallowEmbedded/ModelLanguageMetaLogic.v`.

Active declarations:
- `Model2CoqProp`
- `CoqPropDefinition_Model`, field `model2coqprop`
- `Model2CoqProp_Normal`
- `Model2CoqPropDeduction`

Lean keeps these declarations under
`Unifysl.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic`
to avoid root-name collisions with other model-language builders.
-/

import Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage
import Unifysl.MetaLogicInj.Syntax
import Unifysl.MetaLogicInj.ProofTheory.ProofRules
import Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic

universe u

namespace Unifysl
namespace MetaLogicInj
namespace ShallowEmbedded
namespace ModelLanguageMetaLogic

abbrev Model_L (M : Model.{u}) : Language.{u} :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model_L M

abbrev Model2Derivable1 (M : Model.{u}) : Derivable1 (Model_L M) :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model2Derivable1 M

abbrev Model2Truep (M : Model.{u}) : TrueLanguage (Model_L M) :=
  Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2Truep M

def Model2CoqProp (M : Model.{u}) : CoqPropLanguage (Model_L M) where
  coq_prop := fun P _ => P

class CoqPropDefinition_Model {M : Model.{u}}
    (coq_prop_L : CoqPropLanguage (Model_L M)) : Prop where
  model2coqprop :
    forall (P : Prop) (m : @Model.model M),
      @coq_prop (Model_L M) coq_prop_L P m = P

theorem Model2CoqProp_Normal (M : Model.{u}) :
    CoqPropDefinition_Model (M := M) (Model2CoqProp M) := by
  constructor
  intro P m
  rfl

theorem Model2CoqPropDeduction (M : Model.{u}) :
    @CoqPropDeduction (Model_L M) (Model2Truep M) (Model2CoqProp M)
      (Model2Derivable1 M) := by
  letI : TrueLanguage (Model_L M) := Model2Truep M
  letI : CoqPropLanguage (Model_L M) := Model2CoqProp M
  exact {
    derivable1s_coq_prop_r := by
      intro P x hP m _hx
      exact hP
    derivable1s_coq_prop_l := by
      intro P x h m hP
      exact h hP m trivial
  }

end ModelLanguageMetaLogic
end ShallowEmbedded
end MetaLogicInj
end Unifysl
