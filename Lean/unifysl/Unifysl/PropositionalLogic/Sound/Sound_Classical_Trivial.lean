/-
Coq inventory from
`unifysl-prp/PropositionalLogic/Sound/Sound_Classical_Trivial.v`.

Imports:
- Coq.Logic.Classical_Prop
- Logic.lib.Ensembles_ext
- Logic.GeneralLogic.Base
- Logic.MinimumLogic.Syntax
- Logic.MinimumLogic.Semantics.Trivial
- Logic.PropositionalLogic.Syntax
- Logic.PropositionalLogic.Semantics.Trivial

Lemmas:
- `sound_andp_intros`
- `sound_provable_andp_elim1`
- `sound_provable_andp_elim2`
- `sound_provable_orp_intros1`
- `sound_provable_orp_intros2`
- `sound_provable_orp_elim`
- `sound_provable_falsep_elim`
- `sound_excluded_middle`
- `sound_by_contradiction`
- `sound_provable_peirce_law`
-/

import Unifysl.MinimumLogic.Semantics.Trivial
import Unifysl.PropositionalLogic.Semantics.Trivial

universe u v

namespace Unifysl

set_option linter.unusedSectionVars false

open PropositionalLanguageNotation

section Sound

variable {L : Language.{u}}
variable [MinimumLanguage L]
variable [AndLanguage L] [OrLanguage L] [FalseLanguage L]
variable [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable {MD : Model.{v}} [SM : Semantics L MD]
variable [tminSM : TrivialMinimumSemantics L MD SM]
variable [andpSM : AndSemantics L MD SM]
variable [orpSM : OrSemantics L MD SM]
variable [falsepSM : FalseSemantics L MD SM]
variable [negpSM : NegSemantics L MD SM]
variable [iffpSM : IffSemantics L MD SM]
variable [truepSM : TrueSemantics L MD SM]

theorem sound_andp_intros :
    forall (x y : @Language.expr L) (m : @Model.model MD),
      m |= x ⟶ (y ⟶ (x && y)) := by
  intro x y m
  rw [sat_impp, sat_impp, sat_andp]
  intro hx hy
  exact ⟨hx, hy⟩

theorem sound_provable_andp_elim1 :
    forall (x y : @Language.expr L) (m : @Model.model MD),
      m |= (x && y) ⟶ x := by
  intro x y m
  rw [sat_impp, sat_andp]
  intro hxy
  exact hxy.left

theorem sound_provable_andp_elim2 :
    forall (x y : @Language.expr L) (m : @Model.model MD),
      m |= (x && y) ⟶ y := by
  intro x y m
  rw [sat_impp, sat_andp]
  intro hxy
  exact hxy.right

theorem sound_provable_orp_intros1 :
    forall (x y : @Language.expr L) (m : @Model.model MD),
      m |= x ⟶ (x || y) := by
  intro x y m
  rw [sat_impp, sat_orp]
  intro hx
  exact Or.inl hx

theorem sound_provable_orp_intros2 :
    forall (x y : @Language.expr L) (m : @Model.model MD),
      m |= y ⟶ (x || y) := by
  intro x y m
  rw [sat_impp, sat_orp]
  intro hy
  exact Or.inr hy

theorem sound_provable_orp_elim :
    forall (x y z : @Language.expr L) (m : @Model.model MD),
      m |= (x ⟶ z) ⟶ ((y ⟶ z) ⟶ ((x || y) ⟶ z)) := by
  intro x y z m
  rw [sat_impp, sat_impp, sat_impp, sat_impp, sat_impp, sat_orp]
  intro hxz hyz hxy
  cases hxy with
  | inl hx => exact hxz hx
  | inr hy => exact hyz hy

theorem sound_provable_falsep_elim :
    forall (x : @Language.expr L) (m : @Model.model MD),
      m |= FF ⟶ x := by
  intro x m
  rw [sat_impp, sat_falsep]
  intro hfalse
  cases hfalse

theorem sound_excluded_middle :
    forall (x : @Language.expr L) (m : @Model.model MD),
      m |= x || (~~ x) := by
  intro x m
  classical
  rw [sat_orp, sat_negp]
  exact Classical.em (m |= x)

theorem sound_by_contradiction :
    forall (x y : @Language.expr L) (m : @Model.model MD),
      m |= ((~~ x) ⟶ y) ⟶ (((~~ x) ⟶ (~~ y)) ⟶ x) := by
  intro x y m
  classical
  rw [sat_impp, sat_impp, sat_impp, sat_impp, sat_negp, sat_negp]
  intro hny hnny
  exact Classical.byContradiction (fun hnx => hnny hnx (hny hnx))

theorem sound_provable_peirce_law :
    forall (x y : @Language.expr L) (m : @Model.model MD),
      m |= ((x ⟶ y) ⟶ x) ⟶ x := by
  intro x y m
  classical
  rw [sat_impp]
  intro h
  exact Classical.byContradiction
    (fun hnx =>
      let hfun := (sat_impp (m := m) (x ⟶ y) x).mp h
      hnx (hfun ((sat_impp (m := m) x y).mpr (fun hx => False.elim (hnx hx)))))

end Sound

end Unifysl
