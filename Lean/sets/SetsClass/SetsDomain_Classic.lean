import SetsClass.SetsDomain

universe u

class SETS_Classical_Properties (T : Type u) [Sets.SETS T] : Prop where
  union_complement_self : forall x : T,
    Sets.equiv (Sets.union x (Sets.complement x)) Sets.full

noncomputable instance Prop_SETS_Classical_Properties : SETS_Classical_Properties Prop where
  union_complement_self := by
    intro P
    constructor
    · intro
      trivial
    · intro
      exact Classical.em P

noncomputable instance lift_SETS_Classical_Properties (A B : Type u)
    [Sets.SETS B] [SETS_Classical_Properties B] :
    SETS_Classical_Properties (A -> B) where
  union_complement_self := by
    intro x a
    exact SETS_Classical_Properties.union_complement_self (x a)

theorem Sets_union_complement_self {T : Type u} [Sets.SETS T]
    [SETS_Classical_Properties T] (x : T) :
    Sets.equiv (Sets.union x (Sets.complement x)) Sets.full :=
  SETS_Classical_Properties.union_complement_self x

theorem Sets_complement_self_union {T : Type u} [Sets.SETS T]
    [SETS_Properties T] [SETS_Classical_Properties T] (x : T) :
    Sets.equiv (Sets.union (Sets.complement x) x) Sets.full := by
  exact Sets_equiv_trans (Sets_union_comm (Sets.complement x) x)
    (Sets_union_complement_self x)
