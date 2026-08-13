import Unifysl.GeneralLogic.Semantics.Kripke
import Unifysl.MinimumLogic.Syntax

/-!
Coq inventory from `MinimumLogic/Semantics/Kripke.v`:
- Module `Semantics`:
  - definition `impp`
  - lemma `impp_closed`
- Module `SemanticsMono`:
  - definition `impp`
- Class `KripkeMinimumSemantics` with field `denote_impp`.
- Lemma `sat_impp`.

Lean note:
- The Kripke connective is placed at `Semantics.Kripke.impp` to avoid
  colliding with the already migrated trivial semantics `Semantics.impp`.
- The Mono variant is placed at `Semantics.KripkeMono.impp` for the same
  reason.
- The Coq lemma `sat_impp` is exposed as
  `KripkeMinimumSemantics.sat_impp`, while root `sat_impp` remains the
  trivial semantics lemma.
- The order relation is always the explicit `Krelation`; no global `<=`
  notation is introduced.
-/

universe u v w z

namespace Unifysl

namespace Semantics
namespace Kripke

def impp {worlds : Type u} [R : Relation worlds]
    (X Y : Ensemble worlds) : Ensemble worlds :=
  fun m => forall n, Krelation m n -> X n -> Y n

theorem impp_closed {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)] :
    forall (X Y : Ensemble worlds),
      upwards_closed_Kdenote X ->
        upwards_closed_Kdenote Y ->
          upwards_closed_Kdenote (impp X Y) := by
  intro X Y _hX _hY m n hmn hm p hnp hp
  have hmp : Krelation m p :=
    @PreOrder.trans worlds (@Krelation worlds R) po_R m n p hmn hnp
  exact hm p hmp hp

end Kripke
end Semantics

namespace Semantics.KripkeMono

def impp {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)]
    (X Y : MonoEnsemble worlds) : MonoEnsemble worlds :=
  ⟨Semantics.Kripke.impp X.1 Y.1,
    by
      exact Semantics.Kripke.impp_closed X.1 Y.1 X.2 Y.2⟩

end Semantics.KripkeMono

class KripkeMinimumSemantics (L : Language.{u}) [MinimumLanguage L]
    (MD : Model.{v}) [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) [R : Relation (kMD.Kworlds M)]
    (SM : Semantics L MD) :
    Type (max (u + 1) (max (v + 1) (max (w + 1) (z + 1)))) where
  denote_impp :
    forall x y : @Language.expr L,
      Same_set (kMD.Kworlds M)
        (Kdenotation M (x ⟶ y))
        (Semantics.Kripke.impp (Kdenotation M x) (Kdenotation M y))

export KripkeMinimumSemantics (denote_impp)

namespace KripkeMinimumSemantics

theorem sat_impp {L : Language.{u}} [MinimumLanguage L]
    {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    {M : kMD.Kmodel} [R : Relation (kMD.Kworlds M)]
    [SM : Semantics L MD]
    [kminSM : KripkeMinimumSemantics L MD M SM] :
    forall (m : kMD.Kworlds M) (x y : @Language.expr L),
      satisfies (KripkeModel.build_model M m) (x ⟶ y) <->
        (forall n : kMD.Kworlds M,
          Krelation m n ->
            satisfies (KripkeModel.build_model M n) x ->
              satisfies (KripkeModel.build_model M n) y) := by
  intro m x y
  have h :=
    KripkeMinimumSemantics.denote_impp (L := L) (MD := MD) (M := M) (SM := SM) x y
  constructor
  · intro hm n hmn hx
    exact h.left m hm n hmn hx
  · intro hm
    exact h.right m hm

end KripkeMinimumSemantics

end Unifysl
