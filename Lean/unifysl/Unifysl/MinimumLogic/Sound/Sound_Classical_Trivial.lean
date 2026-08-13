/-
Coq inventory from `unifysl-prp/MinimumLogic/Sound/Sound_Classical_Trivial.v`.

Imports:
- Coq.Logic.Classical_Prop
- Logic.lib.Ensembles_ext
- Logic.GeneralLogic.Base
- Logic.MinimumLogic.Syntax
- Logic.MinimumLogic.Semantics.Trivial

Section `Sound` lemmas:
- `sound_modus_ponens`
- `sound_axiom1`
- `sound_axiom2`
-/

import Unifysl.MinimumLogic.Semantics.Trivial

universe u v

namespace Unifysl

theorem sound_modus_ponens {L : Language.{u}} [MinimumLanguage L]
    {MD : Model.{v}} [SM : Semantics L MD]
    [tminSM : TrivialMinimumSemantics L MD SM] :
    forall (x y : @Language.expr L) (m : @Model.model MD),
      satisfies m (x ⟶ y) -> satisfies m x -> satisfies m y := by
  intro x y m hxy hx
  exact (sat_impp (m := m) x y).mp hxy hx

theorem sound_axiom1 {L : Language.{u}} [MinimumLanguage L]
    {MD : Model.{v}} [SM : Semantics L MD]
    [tminSM : TrivialMinimumSemantics L MD SM] :
    forall (x y : @Language.expr L) (m : @Model.model MD),
      satisfies m (x ⟶ y ⟶ x) := by
  intro x y m
  exact (sat_impp (m := m) x (y ⟶ x)).mpr
    (fun hx => (sat_impp (m := m) y x).mpr (fun _ => hx))

theorem sound_axiom2 {L : Language.{u}} [MinimumLanguage L]
    {MD : Model.{v}} [SM : Semantics L MD]
    [tminSM : TrivialMinimumSemantics L MD SM] :
    forall (x y z : @Language.expr L) (m : @Model.model MD),
      satisfies m ((x ⟶ y ⟶ z) ⟶ (x ⟶ y) ⟶ (x ⟶ z)) := by
  intro x y z m
  refine (sat_impp (m := m) (x ⟶ y ⟶ z) ((x ⟶ y) ⟶ (x ⟶ z))).mpr ?_
  intro hxyz
  refine (sat_impp (m := m) (x ⟶ y) (x ⟶ z)).mpr ?_
  intro hxy
  refine (sat_impp (m := m) x z).mpr ?_
  intro hx
  have hyz : satisfies m (y ⟶ z) :=
    (sat_impp (m := m) x (y ⟶ z)).mp hxyz hx
  have hy : satisfies m y :=
    (sat_impp (m := m) x y).mp hxy hx
  exact (sat_impp (m := m) y z).mp hyz hy

end Unifysl
