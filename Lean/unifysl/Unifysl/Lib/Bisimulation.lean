import Unifysl.Lib.Relation_ext

namespace Unifysl

open Relation_ext

def bisimulation {A : Type u} (bis : relation A) (R : relation A) : Prop :=
  forall m n, bis m n ->
    (forall m', R m m' -> exists n', R n n' /\ bis m' n') /\
    (forall n', R n n' -> exists m', R m m' /\ bis m' n')

class Bisimulation {A : Type u} (bis : relation A) (R : relation A) : Prop where
  bis_l : forall m n, bis m n ->
    forall m', R m m' -> exists n', R n n' /\ bis m' n'
  bis_r : forall m n, bis m n ->
    forall n', R n n' -> exists m', R m m' /\ bis m' n'

export Bisimulation (bis_l bis_r)

theorem eq_bis {A : Type u} (R : relation A) : Bisimulation Eq R := by
  constructor
  · intro m n hmn m' hm'
    cases hmn
    exact ⟨m', hm', rfl⟩
  · intro m n hmn n' hn'
    cases hmn
    exact ⟨n', hn', rfl⟩

theorem full_bis {A : Type u} (R : relation A) [SR : Serial R] :
    Bisimulation full_relation R := by
  constructor
  · intro m n _ m' _
    rcases SR.seriality n with ⟨n', hn'⟩
    exact ⟨n', hn', trivial⟩
  · intro m n _ n' _
    rcases SR.seriality m with ⟨m', hm'⟩
    exact ⟨m', hm', trivial⟩

end Unifysl
