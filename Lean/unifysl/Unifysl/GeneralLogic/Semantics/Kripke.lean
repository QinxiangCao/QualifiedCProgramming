/-
Coq inventory from `unifysl-prp/GeneralLogic/Semantics/Kripke.v`.

Imports:
- Coq.Classes.RelationClasses
- Coq.Relations.Relation_Definitions
- Logic.GeneralLogic.Base
- Logic.GeneralLogic.KripkeModel

Local scopes/imports:
- logic_base
- kripke_model
- KripkeModelFamilyNotation
- KripkeModelNotation_Intuitionistic

Definitions/classes:
- class `KripkeIntuitionisticSemantics`
  - field `denote_closed`

Lemmas:
- `sat_mono`
-/

import Unifysl.GeneralLogic.KripkeModel

universe u v w z

namespace Unifysl

class KripkeIntuitionisticSemantics (L : Language.{u}) (MD : Model.{v})
    [kMD : KripkeModel.{v, w, z} MD] (M : kMD.Kmodel)
    [R : Relation (kMD.Kworlds M)] (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_closed :
    forall x : @Language.expr L, upwards_closed_Kdenote (Kdenotation M x)

export KripkeIntuitionisticSemantics (denote_closed)

theorem sat_mono {L : Language.{u}} {MD : Model.{v}}
    [kMD : KripkeModel.{v, w, z} MD] {M : kMD.Kmodel}
    [R : Relation (kMD.Kworlds M)] [SM : Semantics L MD]
    [kiSM : KripkeIntuitionisticSemantics L MD M SM] :
    forall (m n : kMD.Kworlds M) (x : @Language.expr L),
      Krelation m n ->
        satisfies (KripkeModel.build_model M m) x ->
          satisfies (KripkeModel.build_model M n) x := by
  intro m n x hmn hm
  exact denote_closed x m n hmn hm

end Unifysl
