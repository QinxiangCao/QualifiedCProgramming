namespace Unifysl

class Join (worlds : Type u) : Type u where
  join : worlds -> worlds -> worlds -> Prop

export Join (join)

class SeparationAlgebra (worlds : Type u) [Join worlds] : Type u where
  join_comm : forall m1 m2 m : worlds,
    join m1 m2 m ->
    join m2 m1 m
  join_assoc : forall mx my mz mxy mxyz : worlds,
    join mx my mxy ->
    join mxy mz mxyz ->
    exists myz, join my mz myz /\ join mx myz mxyz

export SeparationAlgebra (join_comm join_assoc)

def unit_element {worlds : Type u} [Join worlds] : worlds -> Prop :=
  fun e => forall n n', join e n n' -> n = n'

class Unit (worlds : Type u) : Type u where
  is_unit : worlds -> Prop

export Unit (is_unit)

class UnitJoinRelation (worlds : Type u) [Unit worlds] [Join worlds] : Type u where
  unit_join : forall n : worlds, exists u : worlds, is_unit u /\ join n u n
  unit_spec : forall n m u : worlds, is_unit u -> join n u m -> n = m

export UnitJoinRelation (unit_join unit_spec)

end Unifysl
