import Unifysl.MinimumLogic.Semantics.Kripke
import Unifysl.MinimumLogic.Semantics.Trivial

/-!
Coq inventory from `MinimumLogic/Semantics/SemanticEquiv.v`:

Imports:
- Coq.Logic.Classical_Prop
- Coq.Classes.RelationClasses
- Coq.Relations.Relation_Definitions
- Logic.lib.Ensembles_ext
- Logic.GeneralLogic.Base
- Logic.GeneralLogic.KripkeModel
- Logic.MinimumLogic.Syntax
- Logic.MinimumLogic.Semantics.Kripke
- Logic.MinimumLogic.Semantics.Trivial

Local scopes/imports:
- logic_base
- syntax
- kripke_model
- KripkeModelFamilyNotation
- KripkeModelNotation_Intuitionistic

Section `SemanticEquiv`:
- Lemma `eqR_KripkeIntuitionistic`
- Lemma `Trivial2Kripke`
-/

universe u v

namespace Unifysl

instance eqR_KripkeIntuitionistic {L : Language.{u}}
    {MD : Model.{v}} [SM : Semantics L MD] :
    @KripkeIntuitionisticSemantics L MD (unit_kMD MD) Unit.unit
      ({ Krelation := fun m n => m = n } : Relation (@Model.model MD)) SM :=
  @KripkeIntuitionisticSemantics.mk L MD (unit_kMD MD) Unit.unit
    ({ Krelation := fun m n => m = n } : Relation (@Model.model MD)) SM
    (by
      intro x m n hmn hm
      subst hmn
      exact hm)

instance Trivial2Kripke {L : Language.{u}} [MinimumLanguage L]
    {MD : Model.{v}} [SM : Semantics L MD]
    [tpSM : TrivialMinimumSemantics L MD SM] :
    @KripkeMinimumSemantics L (inferInstance : MinimumLanguage L)
      MD (unit_kMD MD) Unit.unit
      ({ Krelation := fun m n => m = n } : Relation (@Model.model MD)) SM :=
  @KripkeMinimumSemantics.mk L (inferInstance : MinimumLanguage L)
    MD (unit_kMD MD) Unit.unit
    ({ Krelation := fun m n => m = n } : Relation (@Model.model MD)) SM
    (by
      intro x y
      have h :=
        TrivialMinimumSemantics.denote_impp (L := L) (MD := MD) (SM := SM) x y
      constructor
      · intro m hm n hmn hx
        subst hmn
        exact h.left m hm hx
      · intro m hm
        exact h.right m (hm m rfl))

end Unifysl
