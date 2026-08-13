/-
Coq inventory from `unifysl-prp/SeparationLogic/Semantics/WeakSemantics.v`.

Module `WeakSemantics`:
- `sepcon`
- `wand`
- `sepcon_closed`
- `wand_closed`

Module `WeakSemanticsMono`:
- `sepcon`
- `wand`
-/

import Unifysl.SeparationLogic.Model.OrderedSA

universe u

namespace Unifysl

namespace WeakSemantics

def sepcon {worlds : Type u} [Join worlds]
    (X Y : Ensemble worlds) : Ensemble worlds :=
  fun m => exists m1 m2, join m1 m2 m /\ X m1 /\ Y m2

def wand {worlds : Type u} [Join worlds]
    (X Y : Ensemble worlds) : Ensemble worlds :=
  fun m => forall m1 m2, join m m1 m2 -> X m1 -> Y m2

theorem sepcon_closed {worlds : Type u}
    [R : Relation worlds] [_po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] [_SA : SeparationAlgebra worlds]
    [uSA : UpwardsClosedSeparationAlgebra worlds] :
    forall (X Y : Ensemble worlds),
      upwards_closed_Kdenote X ->
      upwards_closed_Kdenote Y ->
      upwards_closed_Kdenote (sepcon X Y) := by
  intro X Y hX hY n m hnm hn
  rcases hn with ⟨n1, n2, hj, hx, hy⟩
  rcases join_Korder_up n m n1 n2 hj hnm with
    ⟨m1, m2, hjm, hn1m1, hn2m2⟩
  exact ⟨m1, m2, hjm, hX n1 m1 hn1m1 hx, hY n2 m2 hn2m2 hy⟩

theorem wand_closed {worlds : Type u}
    [R : Relation worlds] [po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] [_SA : SeparationAlgebra worlds]
    [dSA : DownwardsClosedSeparationAlgebra worlds] :
    forall (X Y : Ensemble worlds),
      upwards_closed_Kdenote X ->
      upwards_closed_Kdenote Y ->
      upwards_closed_Kdenote (wand X Y) := by
  intro X Y _hX hY m n hmn hm n1 n2 hj hx
  rcases join_Korder_down n n1 n2 m n1 hj hmn (po_R.refl n1) with
    ⟨m2', hjm, hm2'n2⟩
  exact hY m2' n2 hm2'n2 (hm n1 m2' hjm hx)

end WeakSemantics

namespace WeakSemanticsMono

def sepcon {worlds : Type u}
    [R : Relation worlds] [po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] [SA : SeparationAlgebra worlds]
    [uSA : UpwardsClosedSeparationAlgebra worlds]
    (X Y : MonoEnsemble worlds) : MonoEnsemble worlds :=
  ⟨WeakSemantics.sepcon X.1 Y.1,
    WeakSemantics.sepcon_closed X.1 Y.1 X.2 Y.2⟩

def wand {worlds : Type u}
    [R : Relation worlds] [po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] [SA : SeparationAlgebra worlds]
    [dSA : DownwardsClosedSeparationAlgebra worlds]
    (X Y : MonoEnsemble worlds) : MonoEnsemble worlds :=
  ⟨WeakSemantics.wand X.1 Y.1,
    WeakSemantics.wand_closed X.1 Y.1 X.2 Y.2⟩

end WeakSemanticsMono

end Unifysl
