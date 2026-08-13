/-
Coq inventory from `unifysl-prp/SeparationLogic/Semantics/FlatSemantics.v`.

Imports:
- Coq.Logic.Classical_Prop
- Coq.Classes.RelationClasses
- Coq.Relations.Relation_Definitions
- Logic.lib.Coqlib
- Logic.GeneralLogic.Base
- Logic.SeparationLogic.Syntax
- Logic.GeneralLogic.KripkeModel
- Logic.SeparationLogic.Model.SeparationAlgebra
- Logic.SeparationLogic.Semantics.EmpSemantics
- Logic.SeparationLogic.Model.OrderedSA
- Logic.SeparationLogic.Semantics.WeakSemantics
- Logic.SeparationLogic.Semantics.StrongSemantics

Classes/fields:
- `SepconSemantics.denote_sepcon`
- `WandSemantics.denote_wand`
- `EmpSemantics.denote_emp`

Lemmas:
- `sat_sepcon`
- `sat_wand`
- `sat_emp`
-/

import Unifysl.SeparationLogic.Syntax
import Unifysl.SeparationLogic.Semantics.EmpSemantics
import Unifysl.SeparationLogic.Semantics.WeakSemantics

universe u v w z

namespace Unifysl

open SeparationLogicNotation

class SepconSemantics (L : Language.{u}) [SepconLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) [R : Relation (kMD.Kworlds M)]
    [J : Join (kMD.Kworlds M)]
    (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_sepcon :
    forall x y : @Language.expr L,
      Same_set (kMD.Kworlds M)
        (Kdenotation M (x * y))
        (WeakSemantics.sepcon (Kdenotation M x) (Kdenotation M y))

export SepconSemantics (denote_sepcon)

class WandSemantics (L : Language.{u}) [WandLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) [R : Relation (kMD.Kworlds M)]
    [J : Join (kMD.Kworlds M)]
    (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_wand :
    forall x y : @Language.expr L,
      Same_set (kMD.Kworlds M)
        (Kdenotation M (x -* y))
        (WeakSemantics.wand (Kdenotation M x) (Kdenotation M y))

export WandSemantics (denote_wand)

class EmpSemantics (L : Language.{u}) [EmpLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) [U : Unit (kMD.Kworlds M)]
    (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_emp :
    Same_set (kMD.Kworlds M)
      (Kdenotation M (@emp L _))
      (EmpSemantics.emp (worlds := kMD.Kworlds M))

export EmpSemantics (denote_emp)

theorem sat_sepcon {L : Language.{u}} [SepconLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [R : Relation (kMD.Kworlds M)]
    [J : Join (kMD.Kworlds M)] [SM : Semantics L MD]
    [fsepconSM : SepconSemantics L MD M SM] :
    forall (m : kMD.Kworlds M) (x y : @Language.expr L),
      satisfies (KripkeModel.build_model M m) (x * y) <->
        exists m1 m2, join m1 m2 m /\
          satisfies (KripkeModel.build_model M m1) x /\
          satisfies (KripkeModel.build_model M m2) y := by
  intro m x y
  have h :=
    SepconSemantics.denote_sepcon
      (L := L) (MD := MD) (M := M) (SM := SM) x y
  exact ⟨h.left m, h.right m⟩

theorem sat_wand {L : Language.{u}} [WandLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [R : Relation (kMD.Kworlds M)]
    [J : Join (kMD.Kworlds M)] [SM : Semantics L MD]
    [fwandSM : WandSemantics L MD M SM] :
    forall (m : kMD.Kworlds M) (x y : @Language.expr L),
      satisfies (KripkeModel.build_model M m) (x -* y) <->
        forall m1 m2, join m m1 m2 ->
          satisfies (KripkeModel.build_model M m1) x ->
          satisfies (KripkeModel.build_model M m2) y := by
  intro m x y
  have h :=
    WandSemantics.denote_wand
      (L := L) (MD := MD) (M := M) (SM := SM) x y
  exact ⟨h.left m, h.right m⟩

theorem sat_emp {L : Language.{u}} [EmpLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [U : Unit (kMD.Kworlds M)]
    [SM : Semantics L MD] [empSM : EmpSemantics L MD M SM] :
    forall m : kMD.Kworlds M,
      satisfies (KripkeModel.build_model M m) (@emp L _) <-> is_unit m := by
  intro m
  have h :=
    EmpSemantics.denote_emp
      (L := L) (MD := MD) (M := M) (SM := SM)
  exact ⟨h.left m, h.right m⟩

end Unifysl
