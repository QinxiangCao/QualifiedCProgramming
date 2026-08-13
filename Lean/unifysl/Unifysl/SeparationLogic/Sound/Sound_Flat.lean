/-
Coq inventory from `unifysl-prp/SeparationLogic/Sound/Sound_Flat.v`.

Imports:
- Logic.lib.Coqlib
- Logic.GeneralLogic.Base
- Logic.GeneralLogic.KripkeModel
- Logic.GeneralLogic.Semantics.Kripke
- Logic.MinimumLogic.Syntax
- Logic.MinimumLogic.Semantics.Kripke
- Logic.PropositionalLogic.Syntax
- Logic.PropositionalLogic.Semantics.Kripke
- Logic.SeparationLogic.Syntax
- Logic.SeparationLogic.Model.SeparationAlgebra
- Logic.SeparationLogic.Model.OrderedSA
- Logic.SeparationLogic.Semantics.FlatSemantics

Local scopes/imports:
- logic_base
- syntax
- kripke_model
- PropositionalLanguageNotation
- SeparationLogicNotation
- KripkeModelFamilyNotation
- KripkeModelNotation_Intuitionistic

Active lemmas:
- `sound_sepcon_comm`
- `sound_provable_sepcon_assoc1`
- `sound_provables_wand_sepcon_adjoint`
- `sound_provable_sepcon_mono`
- `sound_provable_sepcon_elim1`
- `sound_provable_sepcon_emp_derives`
- `sound_provable_derives_sepcon_emp`
- `sound_provable_sepcon_andp_emp_derives`
- `sound_provable_emp_dup`
-/

import Unifysl.MinimumLogic.Semantics.Kripke
import Unifysl.PropositionalLogic.Semantics.Kripke
import Unifysl.SeparationLogic.Semantics.FlatSemantics

universe u v w z

namespace Unifysl

set_option linter.unusedSectionVars false

open PropositionalLanguageNotation
open SeparationLogicNotation

section Sound_Flat

variable {L : Language.{u}}
variable [_minL : MinimumLanguage L]
variable [_andpL : AndLanguage L]
variable [_iffpL : IffLanguage L]
variable [_sepconL : SepconLanguage L]
variable [_wandL : WandLanguage L]
variable {MD : Model.{v}}
variable [_kMD : KripkeModel.{v, w, z} MD]
variable (M : _kMD.Kmodel)
variable [_R : Relation (_kMD.Kworlds M)]
variable [_po_R : PreOrder (@Krelation (_kMD.Kworlds M) _R)]
variable [_J : Join (_kMD.Kworlds M)]
variable [_U : Unit (_kMD.Kworlds M)]
variable [_SA : SeparationAlgebra (_kMD.Kworlds M)]
variable [_dSA : DownwardsClosedSeparationAlgebra (_kMD.Kworlds M)]
variable [_SM : Semantics L MD]
variable [_kiSM : KripkeIntuitionisticSemantics L MD M _SM]
variable [_kminSM : KripkeMinimumSemantics L MD M _SM]
variable [_kandpSM : KripkeAndSemantics L MD M _SM]
variable [_kiffpSM : KripkeIffSemantics L MD M _SM]
variable [_fsepconSM : SepconSemantics L MD M _SM]
variable [_fwandSM : WandSemantics L MD M _SM]

theorem sound_sepcon_comm :
    forall (x y : @Language.expr L) (m : _kMD.Kworlds M),
      satisfies (_kMD.build_model M m) ((x * y) ⟶ (y * x)) := by
  intro x y m
  rw [KripkeMinimumSemantics.sat_impp]
  intro n _hmn hxy
  rw [sat_sepcon] at hxy
  rw [sat_sepcon]
  rcases hxy with ⟨m1, m2, hj, hx, hy⟩
  exact ⟨m2, m1, join_comm m1 m2 n hj, hy, hx⟩

theorem sound_provable_sepcon_assoc1 :
    forall (x y z : @Language.expr L) (m : _kMD.Kworlds M),
      satisfies (_kMD.build_model M m) ((x * (y * z)) ⟶ ((x * y) * z)) := by
  intro x y z m
  rw [KripkeMinimumSemantics.sat_impp]
  intro n _hmn hxyz
  rw [sat_sepcon] at hxyz
  rcases hxyz with ⟨mx, myz, hxyzn, hx, hyz⟩
  rw [sat_sepcon] at hyz
  rcases hyz with ⟨my, mz, hyzj, hy, hz⟩
  have hmzyz : join mz my myz := join_comm my mz myz hyzj
  have hyzxn : join myz mx n := join_comm mx myz n hxyzn
  rcases join_assoc mz my mx myz n hmzyz hyzxn with ⟨mxy, hmyx, hzmxy⟩
  have hmxyz : join mxy mz n := join_comm mz mxy n hzmxy
  have hxyj : join mx my mxy := join_comm my mx mxy hmyx
  rw [sat_sepcon]
  refine ⟨mxy, mz, hmxyz, ?_, hz⟩
  rw [sat_sepcon]
  exact ⟨mx, my, hxyj, hx, hy⟩

theorem sound_provables_wand_sepcon_adjoint :
    forall x y z : @Language.expr L,
      (forall m : _kMD.Kworlds M,
        satisfies (_kMD.build_model M m) ((x * y) ⟶ z)) <->
      (forall m : _kMD.Kworlds M,
        satisfies (_kMD.build_model M m) (x ⟶ (y -* z))) := by
  intro x y z
  constructor
  · intro h m
    rw [KripkeMinimumSemantics.sat_impp]
    intro n _hmn hx
    rw [sat_wand]
    intro m1 m2 hj hy
    have hz :=
      (KripkeMinimumSemantics.sat_impp (M := M) m2 (x * y) z).mp (h m2)
    exact hz m2 (PreOrder.refl m2)
      ((sat_sepcon (M := M) m2 x y).mpr ⟨n, m1, hj, hx, hy⟩)
  · intro h m
    rw [KripkeMinimumSemantics.sat_impp]
    intro n _hmn hxy
    rw [sat_sepcon] at hxy
    rcases hxy with ⟨m1, m2, hj, hx, hy⟩
    have hwand_imp :=
      (KripkeMinimumSemantics.sat_impp (M := M) m1 x (y -* z)).mp (h m1)
    have hwand : satisfies (_kMD.build_model M m1) (y -* z) :=
      hwand_imp m1 (PreOrder.refl m1) hx
    exact ((sat_wand (M := M) m1 y z).mp hwand) m2 n hj hy

theorem sound_provable_sepcon_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      (forall m : _kMD.Kworlds M,
        satisfies (_kMD.build_model M m) (x1 ⟶ x2)) ->
      (forall m : _kMD.Kworlds M,
        satisfies (_kMD.build_model M m) (y1 ⟶ y2)) ->
      (forall m : _kMD.Kworlds M,
        satisfies (_kMD.build_model M m) ((x1 * y1) ⟶ (x2 * y2))) := by
  intro x1 x2 y1 y2 hxmono hymono m
  rw [KripkeMinimumSemantics.sat_impp]
  intro n _hmn hsep
  rw [sat_sepcon] at hsep
  rw [sat_sepcon]
  rcases hsep with ⟨m1, m2, hj, hx1, hy1⟩
  have hx12 :=
    (KripkeMinimumSemantics.sat_impp (M := M) m1 x1 x2).mp (hxmono m1)
  have hy12 :=
    (KripkeMinimumSemantics.sat_impp (M := M) m2 y1 y2).mp (hymono m2)
  exact ⟨m1, m2, hj,
    hx12 m1 (PreOrder.refl m1) hx1,
    hy12 m2 (PreOrder.refl m2) hy1⟩

theorem sound_provable_sepcon_elim1
    [_incrSA : IncreasingSeparationAlgebra (_kMD.Kworlds M)] :
    forall (x y : @Language.expr L) (m : _kMD.Kworlds M),
      satisfies (_kMD.build_model M m) ((x * y) ⟶ x) := by
  intro x y m
  rw [KripkeMinimumSemantics.sat_impp]
  intro n _hmn hsep
  rw [sat_sepcon] at hsep
  rcases hsep with ⟨m1, m2, hj, hx, _hy⟩
  have hm1n : Krelation m1 n :=
    all_increasing m2 m1 n (join_comm m1 m2 n hj)
  exact sat_mono m1 n x hm1n hx

variable [_empL : EmpLanguage L]
variable [_eSM : EmpSemantics L MD M _SM]

theorem sound_provable_sepcon_emp_derives
    [_UJO_Rel : UnitJoinOrderRelation (_kMD.Kworlds M)] :
    forall (x : @Language.expr L) (m : _kMD.Kworlds M),
      satisfies (_kMD.build_model M m) ((x * emp) ⟶ x) := by
  intro x m
  rw [KripkeMinimumSemantics.sat_impp]
  intro n _hmn hsep
  rw [sat_sepcon] at hsep
  rcases hsep with ⟨m1, m2, hj, hx, hemp⟩
  have hum2 : is_unit m2 := (sat_emp (M := M) m2).mp hemp
  have hm1n : Krelation m1 n := unit_join_order_min_2 m2 m1 n hum2 hj
  exact sat_mono m1 n x hm1n hx

theorem sound_provable_derives_sepcon_emp
    [_UJO_Rel : UnitJoinOrderRelation (_kMD.Kworlds M)] :
    forall (x : @Language.expr L) (m : _kMD.Kworlds M),
      satisfies (_kMD.build_model M m) (x ⟶ (x * emp)) := by
  intro x m
  rw [KripkeMinimumSemantics.sat_impp]
  intro n _hmn hx
  rw [sat_sepcon]
  rcases unit_join_order_min_1 n with ⟨m1, m2, hj, hnm1, hum2⟩
  exact ⟨m1, m2, hj, sat_mono n m1 x hnm1 hx,
    (sat_emp (M := M) m2).mpr hum2⟩

theorem sound_provable_sepcon_andp_emp_derives
    [_ISSSA : IncreasingSplitSmallerSeparationAlgebra (_kMD.Kworlds M)] :
    forall (x y : @Language.expr L) (m : _kMD.Kworlds M),
      satisfies (_kMD.build_model M m) (((x * y) && emp) ⟶ x) := by
  intro x y m
  rw [KripkeMinimumSemantics.sat_impp]
  intro n _hmn h
  rw [KripkePropositionalSemantics.sat_andp] at h
  rcases h with ⟨hsep, hemp⟩
  rw [sat_sepcon] at hsep
  rcases hsep with ⟨n1, n2, hj, hx, _hy⟩
  have hun : is_unit n := (sat_emp (M := M) n).mp hemp
  have hn1n : Krelation n1 n := incr_split_smaller n1 n2 n hun hj
  exact sat_mono n1 n x hn1n hx

theorem sound_provable_emp_dup
    [_IJSSA : IncreasingJoinSelfSeparationAlgebra (_kMD.Kworlds M)] :
    forall (x _y : @Language.expr L) (m : _kMD.Kworlds M),
      satisfies (_kMD.build_model M m) ((x && emp) ⟶ (x * x)) := by
  intro x _y m
  rw [KripkeMinimumSemantics.sat_impp]
  intro n _hmn h
  rw [KripkePropositionalSemantics.sat_andp] at h
  rcases h with ⟨hx, hemp⟩
  have hun : is_unit n := (sat_emp (M := M) n).mp hemp
  rw [sat_sepcon]
  exact ⟨n, n, incr_join_self n hun, hx, hx⟩

end Sound_Flat

end Unifysl
