/-
Coq inventory from `unifysl-prp/SeparationLogic/Semantics/StrongSemantics.v`.

Module `StrongSemantics`:
- `sepcon`
- `wand`
- `sepcon_closed`
- `wand_closed`

Module `StrongSemanticsMono`:
- `sepcon`
- `wand`
-/

import Unifysl.SeparationLogic.Model.OrderedSA

universe u

namespace Unifysl

namespace StrongSemantics

def sepcon {worlds : Type u} [Relation worlds] [Join worlds]
    (X Y : Ensemble worlds) : Ensemble worlds :=
  fun m => exists m0 m1 m2, Krelation m0 m /\ join m1 m2 m0 /\ X m1 /\ Y m2

def wand {worlds : Type u} [Relation worlds] [Join worlds]
    (X Y : Ensemble worlds) : Ensemble worlds :=
  fun m => forall m0 m1 m2, Krelation m m0 -> join m0 m1 m2 -> X m1 -> Y m2

theorem sepcon_closed {worlds : Type u}
    [R : Relation worlds] [po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] :
    forall (X Y : Ensemble worlds),
      upwards_closed_Kdenote X ->
      upwards_closed_Kdenote Y ->
      upwards_closed_Kdenote (sepcon X Y) := by
  intro X Y _hX _hY n m hnm hn
  rcases hn with ⟨n0, n1, n2, hn0n, hj, hx, hy⟩
  exact ⟨n0, n1, n2, po_R.trans n0 n m hn0n hnm, hj, hx, hy⟩

theorem wand_closed {worlds : Type u}
    [R : Relation worlds] [po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] :
    forall (X Y : Ensemble worlds),
      upwards_closed_Kdenote X ->
      upwards_closed_Kdenote Y ->
      upwards_closed_Kdenote (wand X Y) := by
  intro X Y _hX _hY m n hmn hm n0 n1 n2 hn0 hj hx
  exact hm n0 n1 n2 (po_R.trans m n n0 hmn hn0) hj hx

end StrongSemantics

namespace StrongSemanticsMono

def sepcon {worlds : Type u}
    [R : Relation worlds] [po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] (X Y : MonoEnsemble worlds) : MonoEnsemble worlds :=
  ⟨StrongSemantics.sepcon X.1 Y.1,
    StrongSemantics.sepcon_closed X.1 Y.1 X.2 Y.2⟩

def wand {worlds : Type u}
    [R : Relation worlds] [po_R : PreOrder (@Krelation worlds R)]
    [J : Join worlds] (X Y : MonoEnsemble worlds) : MonoEnsemble worlds :=
  ⟨StrongSemantics.wand X.1 Y.1,
    StrongSemantics.wand_closed X.1 Y.1 X.2 Y.2⟩

end StrongSemanticsMono

end Unifysl
