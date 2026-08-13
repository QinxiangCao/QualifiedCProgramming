/-
Coq inventory from `unifysl-prp/PropositionalLogic/Semantics/Kripke.v`.

Imports:
- Coq.Classes.RelationClasses
- Coq.Relations.Relation_Definitions
- Logic.GeneralLogic.Base
- Logic.GeneralLogic.KripkeModel
- Logic.GeneralLogic.Semantics.Kripke
- Logic.MinimumLogic.Syntax
- Logic.MinimumLogic.Semantics.Kripke
- Logic.PropositionalLogic.Syntax

Module `Semantics` definitions:
- `andp`
- `orp`
- `falsep`
- `truep`
- `iffp`
- `negp`

Closedness lemmas:
- `andp_closed`
- `orp_closed`
- `falsep_closed`
- `truep_closed`

Module `SemanticsMono` definitions:
- `andp`
- `orp`
- `falsep`

Classes/fields:
- `KripkeAndSemantics.denote_andp`
- `KripkeOrSemantics.denote_orp`
- `KripkeFalseSemantics.denote_falsep`
- `KripkeTrueSemantics.denote_truep`
- `KripkeIffSemantics.denote_iffp`
- `KripkeNegSemantics.denote_negp`

Lemmas:
- `sat_andp`
- `sat_orp`
- `sat_falsep`
- `sat_truep`
- `sat_iffp`
- `sat_negp`
- `valid_iffp`

Lean note:
- Kripke propositional connectives live under
  `Semantics.KripkePropositional` to avoid the already migrated trivial
  propositional semantics.
- Mono variants live under `Semantics.KripkePropositionalMono`.
- The Coq lemma names are exposed under `KripkePropositionalSemantics`.
- Coq `<-->` is represented by Lean `⟷`; the Kripke order is the explicit
  `Krelation`.
-/

import Unifysl.MinimumLogic.Semantics.Kripke
import Unifysl.PropositionalLogic.Syntax

universe u v w z

namespace Unifysl

namespace Semantics.KripkePropositional

def andp {worlds : Type u} (X Y : Ensemble worlds) : Ensemble worlds :=
  fun m => X m /\ Y m

def orp {worlds : Type u} (X Y : Ensemble worlds) : Ensemble worlds :=
  fun m => X m \/ Y m

def falsep {worlds : Type u} : Ensemble worlds :=
  fun _ => False

def truep {worlds : Type u} : Ensemble worlds :=
  fun _ => True

def iffp {worlds : Type u} [Relation worlds]
    (X Y : Ensemble worlds) : Ensemble worlds :=
  andp (Semantics.Kripke.impp X Y) (Semantics.Kripke.impp Y X)

def negp {worlds : Type u} [Relation worlds]
    (X : Ensemble worlds) : Ensemble worlds :=
  Semantics.Kripke.impp X falsep

theorem andp_closed {worlds : Type u} [R : Relation worlds]
    [_po_R : PreOrder (@Krelation worlds R)] :
    forall (X Y : Ensemble worlds),
      upwards_closed_Kdenote X ->
        upwards_closed_Kdenote Y ->
          upwards_closed_Kdenote (andp X Y) := by
  intro X Y hX hY n m hnm hn
  exact ⟨hX n m hnm hn.left, hY n m hnm hn.right⟩

theorem orp_closed {worlds : Type u} [R : Relation worlds]
    [_po_R : PreOrder (@Krelation worlds R)] :
    forall (X Y : Ensemble worlds),
      upwards_closed_Kdenote X ->
        upwards_closed_Kdenote Y ->
          upwards_closed_Kdenote (orp X Y) := by
  intro X Y hX hY n m hnm hn
  cases hn with
  | inl hx => exact Or.inl (hX n m hnm hx)
  | inr hy => exact Or.inr (hY n m hnm hy)

theorem falsep_closed {worlds : Type u} [Relation worlds] :
    upwards_closed_Kdenote (falsep (worlds := worlds)) := by
  intro _ _ _ h
  exact False.elim h

theorem truep_closed {worlds : Type u} [Relation worlds] :
    upwards_closed_Kdenote (truep (worlds := worlds)) := by
  intro _ _ _ _
  trivial

end Semantics.KripkePropositional

namespace Semantics.KripkePropositionalMono

def andp {worlds : Type u}
    [R : Relation worlds] [po_R : PreOrder (@Krelation worlds R)]
    (X Y : MonoEnsemble worlds) : MonoEnsemble worlds :=
  ⟨Semantics.KripkePropositional.andp X.1 Y.1,
    Semantics.KripkePropositional.andp_closed X.1 Y.1 X.2 Y.2⟩

def orp {worlds : Type u}
    [R : Relation worlds] [po_R : PreOrder (@Krelation worlds R)]
    (X Y : MonoEnsemble worlds) : MonoEnsemble worlds :=
  ⟨Semantics.KripkePropositional.orp X.1 Y.1,
    Semantics.KripkePropositional.orp_closed X.1 Y.1 X.2 Y.2⟩

def falsep {worlds : Type u} [Relation worlds] : MonoEnsemble worlds :=
  ⟨Semantics.KripkePropositional.falsep,
    Semantics.KripkePropositional.falsep_closed⟩

end Semantics.KripkePropositionalMono

open PropositionalLanguageNotation

class KripkeAndSemantics (L : Language.{u}) [AndLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_andp :
    forall x y : @Language.expr L,
      Same_set (kMD.Kworlds M)
        (Kdenotation M (x && y))
        (Semantics.KripkePropositional.andp
          (Kdenotation M x) (Kdenotation M y))

class KripkeOrSemantics (L : Language.{u}) [OrLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_orp :
    forall x y : @Language.expr L,
      Same_set (kMD.Kworlds M)
        (Kdenotation M (x || y))
        (Semantics.KripkePropositional.orp
          (Kdenotation M x) (Kdenotation M y))

class KripkeFalseSemantics (L : Language.{u}) [FalseLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_falsep :
    Same_set (kMD.Kworlds M)
      (Kdenotation M (@falsep L _))
      Semantics.KripkePropositional.falsep

class KripkeTrueSemantics (L : Language.{u}) [TrueLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_truep :
    Same_set (kMD.Kworlds M)
      (Kdenotation M (@truep L _))
      Semantics.KripkePropositional.truep

class KripkeIffSemantics (L : Language.{u}) [IffLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) [Relation (kMD.Kworlds M)]
    (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_iffp :
    forall x y : @Language.expr L,
      Same_set (kMD.Kworlds M)
        (Kdenotation M (x ⟷ y))
        (Semantics.KripkePropositional.iffp
          (Kdenotation M x) (Kdenotation M y))

class KripkeNegSemantics (L : Language.{u}) [NegLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) [Relation (kMD.Kworlds M)]
    (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_negp :
    forall x : @Language.expr L,
      Same_set (kMD.Kworlds M)
        (Kdenotation M (~~ x))
        (Semantics.KripkePropositional.negp (Kdenotation M x))

export KripkeAndSemantics (denote_andp)
export KripkeOrSemantics (denote_orp)
export KripkeFalseSemantics (denote_falsep)
export KripkeTrueSemantics (denote_truep)
export KripkeIffSemantics (denote_iffp)
export KripkeNegSemantics (denote_negp)

namespace KripkePropositionalSemantics

theorem sat_andp {L : Language.{u}} [AndLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [SM : Semantics L MD]
    [andpSM : KripkeAndSemantics L MD M SM] :
    forall (m : kMD.Kworlds M) (x y : @Language.expr L),
      satisfies (KripkeModel.build_model M m) (x && y) <->
        (satisfies (KripkeModel.build_model M m) x /\
          satisfies (KripkeModel.build_model M m) y) := by
  intro m x y
  have h :=
    KripkeAndSemantics.denote_andp (L := L) (MD := MD) (M := M) (SM := SM) x y
  exact ⟨h.left m, h.right m⟩

theorem sat_orp {L : Language.{u}} [OrLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [SM : Semantics L MD]
    [orpSM : KripkeOrSemantics L MD M SM] :
    forall (m : kMD.Kworlds M) (x y : @Language.expr L),
      satisfies (KripkeModel.build_model M m) (x || y) <->
        (satisfies (KripkeModel.build_model M m) x \/
          satisfies (KripkeModel.build_model M m) y) := by
  intro m x y
  have h :=
    KripkeOrSemantics.denote_orp (L := L) (MD := MD) (M := M) (SM := SM) x y
  exact ⟨h.left m, h.right m⟩

theorem sat_falsep {L : Language.{u}} [FalseLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [SM : Semantics L MD]
    [falsepSM : KripkeFalseSemantics L MD M SM] :
    forall m : kMD.Kworlds M,
      satisfies (KripkeModel.build_model M m) (@falsep L _) <-> False := by
  intro m
  have h :=
    KripkeFalseSemantics.denote_falsep (L := L) (MD := MD) (M := M) (SM := SM)
  exact ⟨h.left m, h.right m⟩

theorem sat_truep {L : Language.{u}} [TrueLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [SM : Semantics L MD]
    [truepSM : KripkeTrueSemantics L MD M SM] :
    forall m : kMD.Kworlds M,
      satisfies (KripkeModel.build_model M m) (@truep L _) <-> True := by
  intro m
  have h :=
    KripkeTrueSemantics.denote_truep (L := L) (MD := MD) (M := M) (SM := SM)
  exact ⟨h.left m, h.right m⟩

theorem sat_iffp {L : Language.{u}} [IffLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [R : Relation (kMD.Kworlds M)]
    [SM : Semantics L MD]
    [iffpSM : KripkeIffSemantics L MD M SM] :
    forall (m : kMD.Kworlds M) (x y : @Language.expr L),
      satisfies (KripkeModel.build_model M m) (x ⟷ y) <->
        (forall n : kMD.Kworlds M,
          Krelation m n ->
            (satisfies (KripkeModel.build_model M n) x <->
              satisfies (KripkeModel.build_model M n) y)) := by
  intro m x y
  have h :=
    KripkeIffSemantics.denote_iffp (L := L) (MD := MD) (M := M) (SM := SM) x y
  constructor
  · intro hm n hmn
    have hiff := h.left m hm
    exact ⟨hiff.left n hmn, hiff.right n hmn⟩
  · intro hm
    apply h.right m
    constructor
    · intro n hmn hx
      exact (hm n hmn).mp hx
    · intro n hmn hy
      exact (hm n hmn).mpr hy

theorem sat_negp {L : Language.{u}} [NegLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [R : Relation (kMD.Kworlds M)]
    [SM : Semantics L MD]
    [negpSM : KripkeNegSemantics L MD M SM] :
    forall (m : kMD.Kworlds M) (x : @Language.expr L),
      satisfies (KripkeModel.build_model M m) (~~ x) <->
        (forall n : kMD.Kworlds M,
          Krelation m n -> ¬ satisfies (KripkeModel.build_model M n) x) := by
  intro m x
  have h :=
    KripkeNegSemantics.denote_negp (L := L) (MD := MD) (M := M) (SM := SM) x
  constructor
  · intro hm n hmn hx
    exact h.left m hm n hmn hx
  · intro hm
    apply h.right m
    intro n hmn hx
    exact hm n hmn hx

theorem valid_iffp {L : Language.{u}} [IffLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [R : Relation (kMD.Kworlds M)]
    [po_R : PreOrder (@Krelation (kMD.Kworlds M) R)]
    [SM : Semantics L MD]
    [iffpSM : KripkeIffSemantics L MD M SM] :
    forall x y : @Language.expr L,
      (forall m : kMD.Kworlds M,
        satisfies (KripkeModel.build_model M m) (x ⟷ y)) ->
      (forall m : kMD.Kworlds M,
        satisfies (KripkeModel.build_model M m) x <->
          satisfies (KripkeModel.build_model M m) y) := by
  intro x y hvalid m
  have hs :=
    (sat_iffp (L := L) (MD := MD) (M := M) m x y).mp (hvalid m)
  exact hs m (po_R.refl m)

end KripkePropositionalSemantics

end Unifysl
