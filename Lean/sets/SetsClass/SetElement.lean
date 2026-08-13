universe u v w x

namespace SetsEle

class PRE_SETS_ELE (S : Type u) (RES : Type v) (E : Type w) where
  In_aux : E -> S -> RES
  set_transfer_aux : (E -> RES) -> S

class SETS_ELE (S : Type u) (E : Type v) where
  In : E -> S -> Prop
  set_transfer : S -> S

abbrev In_aux {S : Type u} {RES : Type v} {E : Type w}
    [se : PRE_SETS_ELE S RES E] : E -> S -> RES := se.In_aux

abbrev set_transfer_aux {S : Type u} {RES : Type v} {E : Type w}
    [se : PRE_SETS_ELE S RES E] : (E -> RES) -> S := se.set_transfer_aux

abbrev In {S : Type u} {E : Type v} [se : SETS_ELE S E] : E -> S -> Prop := se.In

abbrev set_transfer {S : Type u} {E : Type v} [se : SETS_ELE S E] : S -> S :=
  se.set_transfer

def lift_In_aux {A : Type x} {S : Type u} {RES : Type v} {E : Type w}
    [PRE_SETS_ELE S (A -> RES) E] : E × A -> S -> RES :=
  fun a X => @In_aux S (A -> RES) E _ a.1 X a.2

def lift_set_transfer_aux {A : Type x} {S : Type u} {RES : Type v} {E : Type w}
    [PRE_SETS_ELE S (A -> RES) E] : (E × A -> RES) -> S :=
  fun F => set_transfer_aux (fun a1 a2 => F (a1, a2))

end SetsEle

instance Prop_PRE_SETS_ELE (A : Type u) (S : Type v) :
    SetsEle.PRE_SETS_ELE (A -> S) S A where
  In_aux := fun a X => X a
  set_transfer_aux := fun F => F

instance lift_PRE_SETS_ELE {A : Type x} {S : Type u} {RES : Type v} {E : Type w}
    [SetsEle.PRE_SETS_ELE S (A -> RES) E] :
    SetsEle.PRE_SETS_ELE S RES (E × A) where
  In_aux := SetsEle.lift_In_aux
  set_transfer_aux := SetsEle.lift_set_transfer_aux

instance Derived_SETS_ELE {S : Type u} {E : Type v}
    [SetsEle.PRE_SETS_ELE S Prop E] : SetsEle.SETS_ELE S E where
  In := @SetsEle.In_aux S Prop E _
  set_transfer := fun X => @SetsEle.set_transfer_aux S Prop E _
    (fun a => @SetsEle.In_aux S Prop E _ a X)

macro "unfold_In" : tactic =>
  `(tactic| simp only [SetsEle.In, SetsEle.In_aux, SetsEle.lift_In_aux,
      Derived_SETS_ELE, lift_PRE_SETS_ELE, Prop_PRE_SETS_ELE])

syntax "unfold_In" " at " ident : tactic
macro_rules
  | `(tactic| unfold_In at $h:ident) => do
      let location <- `(Lean.Parser.Tactic.location| at $h:ident)
      `(tactic| simp only [SetsEle.In, SetsEle.In_aux, SetsEle.lift_In_aux,
          Derived_SETS_ELE, lift_PRE_SETS_ELE, Prop_PRE_SETS_ELE] $location)
