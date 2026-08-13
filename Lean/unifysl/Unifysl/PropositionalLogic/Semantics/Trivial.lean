/-
Coq inventory from `unifysl-prp/PropositionalLogic/Semantics/Trivial.v`.

Imports:
- Logic.GeneralLogic.Base
- Logic.MinimumLogic.Syntax
- Logic.MinimumLogic.Semantics.Trivial
- Logic.PropositionalLogic.Syntax

Module `Semantics` definitions:
- `andp`
- `orp`
- `falsep`
- `truep`
- `iffp`
- `negp`

Classes/fields:
- `AndSemantics.denote_andp`
- `OrSemantics.denote_orp`
- `FalseSemantics.denote_falsep`
- `TrueSemantics.denote_truep`
- `IffSemantics.denote_iffp`
- `NegSemantics.denote_negp`

Lemmas:
- `sat_andp`
- `sat_orp`
- `sat_falsep`
- `sat_truep`
- `sat_iffp`
- `sat_negp`

Lean note: Coq `<-->` is represented by Lean `⟷`.
-/

import Unifysl.MinimumLogic.Semantics.Trivial
import Unifysl.PropositionalLogic.Syntax

universe u v

namespace Unifysl

namespace Semantics

def andp {M : Type u} (X Y : Ensemble M) : Ensemble M :=
  fun m => X m /\ Y m

def orp {M : Type u} (X Y : Ensemble M) : Ensemble M :=
  fun m => X m \/ Y m

def falsep {M : Type u} : Ensemble M :=
  fun _ => False

def truep {M : Type u} : Ensemble M :=
  fun _ => True

def iffp {M : Type u} (X Y : Ensemble M) : Ensemble M :=
  fun m => X m <-> Y m

def negp {M : Type u} (X : Ensemble M) : Ensemble M :=
  fun m => ¬ X m

end Semantics

open PropositionalLanguageNotation

class AndSemantics (L : Language.{u}) [AndLanguage L]
    (MD : Model.{v}) (SM : Semantics L MD) :
    Type (max (u + 1) (v + 1)) where
  denote_andp :
    forall x y : @Language.expr L,
      Same_set (@Model.model MD)
        (SM.denotation (x && y))
        (Semantics.andp (SM.denotation x) (SM.denotation y))

class OrSemantics (L : Language.{u}) [OrLanguage L]
    (MD : Model.{v}) (SM : Semantics L MD) :
    Type (max (u + 1) (v + 1)) where
  denote_orp :
    forall x y : @Language.expr L,
      Same_set (@Model.model MD)
        (SM.denotation (x || y))
        (Semantics.orp (SM.denotation x) (SM.denotation y))

class FalseSemantics (L : Language.{u}) [FalseLanguage L]
    (MD : Model.{v}) (SM : Semantics L MD) :
    Type (max (u + 1) (v + 1)) where
  denote_falsep :
    Same_set (@Model.model MD)
      (SM.denotation FF)
      Semantics.falsep

class TrueSemantics (L : Language.{u}) [TrueLanguage L]
    (MD : Model.{v}) (SM : Semantics L MD) :
    Type (max (u + 1) (v + 1)) where
  denote_truep :
    Same_set (@Model.model MD)
      (SM.denotation TT)
      Semantics.truep

class IffSemantics (L : Language.{u}) [IffLanguage L]
    (MD : Model.{v}) (SM : Semantics L MD) :
    Type (max (u + 1) (v + 1)) where
  denote_iffp :
    forall x y : @Language.expr L,
      Same_set (@Model.model MD)
        (SM.denotation (x ⟷ y))
        (Semantics.iffp (SM.denotation x) (SM.denotation y))

class NegSemantics (L : Language.{u}) [NegLanguage L]
    (MD : Model.{v}) (SM : Semantics L MD) :
    Type (max (u + 1) (v + 1)) where
  denote_negp :
    forall x : @Language.expr L,
      Same_set (@Model.model MD)
        (SM.denotation (~~ x))
        (Semantics.negp (SM.denotation x))

theorem sat_andp {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD]
    [AndLanguage L] [andpSM : AndSemantics L MD SM] :
    forall (m : @Model.model MD) (x y : @Language.expr L),
      satisfies m (x && y) <-> (satisfies m x /\ satisfies m y) := by
  intro m x y
  have h := AndSemantics.denote_andp (L := L) (MD := MD) (SM := SM) x y
  exact ⟨h.left m, h.right m⟩

theorem sat_orp {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD]
    [OrLanguage L] [orpSM : OrSemantics L MD SM] :
    forall (m : @Model.model MD) (x y : @Language.expr L),
      satisfies m (x || y) <-> (satisfies m x \/ satisfies m y) := by
  intro m x y
  have h := OrSemantics.denote_orp (L := L) (MD := MD) (SM := SM) x y
  exact ⟨h.left m, h.right m⟩

theorem sat_falsep {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD]
    [FalseLanguage L] [falsepSM : FalseSemantics L MD SM] :
    forall m : @Model.model MD, satisfies m (@falsep L _) <-> False := by
  intro m
  have h := FalseSemantics.denote_falsep (L := L) (MD := MD) (SM := SM)
  exact ⟨h.left m, h.right m⟩

theorem sat_truep {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD]
    [TrueLanguage L] [truepSM : TrueSemantics L MD SM] :
    forall m : @Model.model MD, satisfies m (@truep L _) <-> True := by
  intro m
  have h := TrueSemantics.denote_truep (L := L) (MD := MD) (SM := SM)
  exact ⟨h.left m, h.right m⟩

theorem sat_iffp {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD]
    [IffLanguage L] [iffpSM : IffSemantics L MD SM] :
    forall (m : @Model.model MD) (x y : @Language.expr L),
      satisfies m (x ⟷ y) <-> (satisfies m x <-> satisfies m y) := by
  intro m x y
  have h := IffSemantics.denote_iffp (L := L) (MD := MD) (SM := SM) x y
  exact ⟨h.left m, h.right m⟩

theorem sat_negp {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD]
    [NegLanguage L] [negpSM : NegSemantics L MD SM] :
    forall (m : @Model.model MD) (x : @Language.expr L),
      satisfies m (~~ x) <-> ¬ satisfies m x := by
  intro m x
  have h := NegSemantics.denote_negp (L := L) (MD := MD) (SM := SM) x
  exact ⟨h.left m, h.right m⟩

end Unifysl
