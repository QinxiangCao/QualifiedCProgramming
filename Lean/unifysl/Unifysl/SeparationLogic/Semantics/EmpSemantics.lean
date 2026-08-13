/-
Coq inventory from `unifysl-prp/SeparationLogic/Semantics/EmpSemantics.v`.

Module `EmpSemantics`:
- `emp`
- `emp_closed`

Module `EmpSemanticsMono`:
- `emp`
-/

import Unifysl.SeparationLogic.Model.OrderedSA

universe u

namespace Unifysl

namespace EmpSemantics

def emp {worlds : Type u} [Unit worlds] : Ensemble worlds :=
  is_unit

theorem emp_closed {worlds : Type u}
    [R : Relation worlds] [_po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] [U : Unit worlds]
    [_SA : SeparationAlgebra worlds]
    [_dSA : DownwardsClosedSeparationAlgebra worlds]
    [UJORel : UnitJoinOrderRelation worlds] :
    upwards_closed_Kdenote (emp (worlds := worlds)) := by
  intro n m hnm hn
  exact mono_unit n m hn hnm

end EmpSemantics

namespace EmpSemanticsMono

def emp {worlds : Type u}
    [R : Relation worlds] [_po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] [U : Unit worlds]
    [_SA : SeparationAlgebra worlds]
    [_dSA : DownwardsClosedSeparationAlgebra worlds]
    [UJORel : UnitJoinOrderRelation worlds] :
    MonoEnsemble worlds :=
  ⟨EmpSemantics.emp, EmpSemantics.emp_closed⟩

end EmpSemanticsMono

end Unifysl
