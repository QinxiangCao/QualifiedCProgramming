/-
Coq inventory from
`unifysl-prp-8.20/SeparationLogic/ShallowEmbedded/ModelLanguageSeparationLogic.v`.

Active declarations:
- `Model_sepconL`
- `SepconDefinition_Join`, field `join2sepcon`
- `Join2Sepcon`
- `Join2Sepcon_Normal`
- `Model_wandL`
- `WandDefinition_Join`, field `join2wand`
- `Join2Wand`
- `Join2Wand_Normal`
- `SeparationAlgebra2SepconAxiomatization`
- `Unit2Emp`
- `EmpDefinition_Unit`, field `unit2emp`
- `Unit2Emp_Normal`
- `SeparationAlgebra2SepconDeduction`
- `SeparationAlgebra2WandDeduction`
- `Model2EmpDeduction`

The declarations are kept under
`Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic`
and use the L4/L7 model-language modules.
-/

import Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage
import Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic
import Unifysl.SeparationLogic.Semantics.WeakSemantics
import Unifysl.SeparationLogic.Semantics.EmpSemantics
import Unifysl.SeparationLogic.ProofTheory.SeparationLogic

set_option linter.unusedSectionVars false

universe u

namespace Unifysl
namespace SeparationLogic
namespace ShallowEmbedded
namespace ModelLanguageSeparationLogic

abbrev Model_L (M : Model.{u}) : Language.{u} :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model_L M

abbrev Model2Provable (M : Model.{u}) : Provable (Model_L M) :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model2Provable M

abbrev Model2Derivable1 (M : Model.{u}) : Derivable1 (Model_L M) :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model2Derivable1 M

abbrev Model2Impp (M : Model.{u}) : MinimumLanguage (Model_L M) :=
  Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.Model2Impp M

def Model_sepconL (M : Model.{u}) [Join (@Model.model M)] :
    SepconLanguage (Model_L M) where
  sepcon := WeakSemantics.sepcon

class SepconDefinition_Join {M : Model.{u}} [Join (@Model.model M)]
    (SepconL : SepconLanguage (Model_L M)) : Prop where
  join2sepcon :
    forall x y : @Language.expr (Model_L M),
      @sepcon (Model_L M) SepconL x y =
        fun m => exists m1 m2, join m1 m2 m /\ x m1 /\ y m2

def Join2Sepcon (M : Model.{u}) [Join (@Model.model M)] :
    SepconLanguage (Model_L M) where
  sepcon := fun x y m => exists m1 m2, join m1 m2 m /\ x m1 /\ y m2

theorem Join2Sepcon_Normal (M : Model.{u}) [Join (@Model.model M)] :
    SepconDefinition_Join (M := M) (Join2Sepcon M) := by
  constructor
  intro x y
  rfl

def Model_wandL (M : Model.{u}) [Join (@Model.model M)] :
    WandLanguage (Model_L M) where
  wand := WeakSemantics.wand

class WandDefinition_Join {M : Model.{u}} [Join (@Model.model M)]
    (WandL : WandLanguage (Model_L M)) : Prop where
  join2wand :
    forall x y : @Language.expr (Model_L M),
      @wand (Model_L M) WandL x y =
        fun m => forall m1 m2, join m m1 m2 -> x m1 -> y m2

def Join2Wand (M : Model.{u}) [Join (@Model.model M)] :
    WandLanguage (Model_L M) where
  wand := fun x y m => forall m1 m2, join m m1 m2 -> x m1 -> y m2

theorem Join2Wand_Normal (M : Model.{u}) [Join (@Model.model M)] :
    WandDefinition_Join (M := M) (Join2Wand M) := by
  constructor
  intro x y
  rfl

private theorem sepcon_comm_pointwise {A : Type u} [Join A]
    [SeparationAlgebra A] :
    forall x y : A -> Prop,
      forall m, WeakSemantics.sepcon x y m -> WeakSemantics.sepcon y x m := by
  intro x y m hxy
  rcases hxy with ⟨m1, m2, hj, hx, hy⟩
  exact ⟨m2, m1, join_comm m1 m2 m hj, hy, hx⟩

private theorem sepcon_assoc1_pointwise {A : Type u} [Join A]
    [SeparationAlgebra A] :
    forall x y z : A -> Prop,
      forall m,
        WeakSemantics.sepcon x (WeakSemantics.sepcon y z) m ->
        WeakSemantics.sepcon (WeakSemantics.sepcon x y) z m := by
  intro x y z m hxyz
  rcases hxyz with ⟨mx, myz, hxm, hx, hyz⟩
  rcases hyz with ⟨my, mz, hymz, hy, hz⟩
  have hmzyz : join mz my myz := join_comm my mz myz hymz
  have hyzxm : join myz mx m := join_comm mx myz m hxm
  rcases join_assoc mz my mx myz m hmzyz hyzxm with ⟨myx, hmyx, hmzmyx⟩
  have hmxmyx : join mx my myx := join_comm my mx myx hmyx
  have hmyxzm : join myx mz m := join_comm mz myx m hmzmyx
  exact ⟨myx, mz, hmyxzm, ⟨mx, my, hmxmyx, hx, hy⟩, hz⟩

private theorem sepcon_mono_pointwise {A : Type u} [Join A] :
    forall x1 x2 y1 y2 : A -> Prop,
      (forall m, x1 m -> x2 m) ->
      (forall m, y1 m -> y2 m) ->
      forall m,
        WeakSemantics.sepcon x1 y1 m ->
        WeakSemantics.sepcon x2 y2 m := by
  intro x1 x2 y1 y2 hx hy m hsep
  rcases hsep with ⟨m1, m2, hj, hx1, hy1⟩
  exact ⟨m1, m2, hj, hx m1 hx1, hy m2 hy1⟩

theorem SeparationAlgebra2SepconAxiomatization (M : Model.{u})
    [Join (@Model.model M)] [Unit (@Model.model M)]
    [SeparationAlgebra (@Model.model M)] :
    @SepconAxiomatization (Model_L M) (Model2Impp M)
      (Model_sepconL M) (Model2Provable M) := by
  letI : MinimumLanguage (Model_L M) := Model2Impp M
  letI : SepconLanguage (Model_L M) := Model_sepconL M
  letI : Provable (Model_L M) := Model2Provable M
  exact {
    provable_sepcon_comm_impp := by
      intro x y
      exact sepcon_comm_pointwise x y
    provable_sepcon_assoc1 := by
      intro x y z
      exact sepcon_assoc1_pointwise x y z
    provable_sepcon_mono := by
      intro x1 x2 y1 y2
      exact sepcon_mono_pointwise x1 x2 y1 y2 }

def Unit2Emp (M : Model.{u}) [Unit (@Model.model M)] :
    EmpLanguage (Model_L M) where
  emp := EmpSemantics.emp

class EmpDefinition_Unit {M : Model.{u}} [Unit (@Model.model M)]
    (empL : EmpLanguage (Model_L M)) : Prop where
  unit2emp :
    forall m : @Model.model M,
      @emp (Model_L M) empL m = is_unit m

theorem Unit2Emp_Normal (M : Model.{u}) [Unit (@Model.model M)] :
    EmpDefinition_Unit (M := M) (Unit2Emp M) := by
  constructor
  intro m
  rfl

theorem SeparationAlgebra2SepconDeduction (M : Model.{u})
    [Join (@Model.model M)] [SeparationAlgebra (@Model.model M)] :
    @SepconDeduction (Model_L M) (Model_sepconL M) (Model2Derivable1 M) := by
  letI : SepconLanguage (Model_L M) := Model_sepconL M
  letI : Derivable1 (Model_L M) := Model2Derivable1 M
  exact {
    derivable1_sepcon_comm := by
      intro x y
      exact sepcon_comm_pointwise x y
    derivable1_sepcon_assoc1 := by
      intro x y z
      exact sepcon_assoc1_pointwise x y z
    derivable1_sepcon_mono := by
      intro x1 x2 y1 y2
      exact sepcon_mono_pointwise x1 x2 y1 y2 }

theorem SeparationAlgebra2WandDeduction (M : Model.{u})
    [Join (@Model.model M)] [SeparationAlgebra (@Model.model M)] :
    @WandDeduction (Model_L M) (Model_sepconL M) (Join2Wand M)
      (Model2Derivable1 M) := by
  letI : SepconLanguage (Model_L M) := Model_sepconL M
  letI : WandLanguage (Model_L M) := Join2Wand M
  letI : Derivable1 (Model_L M) := Model2Derivable1 M
  exact {
    derivable1s_wand_sepcon_adjoint := by
      intro x y z
      constructor
      · intro h m hx m1 m2 hj hy
        exact h m2 ⟨m, m1, hj, hx, hy⟩
      · intro h m hsep
        rcases hsep with ⟨m1, m2, hj, hx, hy⟩
        exact h m1 hx m2 m hj hy }

theorem Model2EmpDeduction (M : Model.{u}) [Unit (@Model.model M)]
    [Join (@Model.model M)] [UnitJoinRelation (@Model.model M)] :
    @EmpDeduction (Model_L M) (Model_sepconL M) (Unit2Emp M)
      (Model2Derivable1 M) := by
  letI : SepconLanguage (Model_L M) := Model_sepconL M
  letI : EmpLanguage (Model_L M) := Unit2Emp M
  letI : Derivable1 (Model_L M) := Model2Derivable1 M
  exact {
    derivable1_sepcon_emp_l := by
      intro x m h
      rcases h with ⟨m1, m2, hj, hx, hu⟩
      have hm1 : m1 = m :=
        UnitJoinRelation.unit_spec m1 m m2 hu hj
      simpa [hm1] using hx
    derivable1_sepcon_emp_r := by
      intro x m hx
      rcases UnitJoinRelation.unit_join m with ⟨u, hu, hj⟩
      exact ⟨m, u, hj, hx, hu⟩ }

end ModelLanguageSeparationLogic
end ShallowEmbedded
end SeparationLogic
end Unifysl
