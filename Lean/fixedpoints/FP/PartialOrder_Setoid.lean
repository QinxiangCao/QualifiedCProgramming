import AUXLib.Morphisms
import FP.LiftConstructors
import SetsClass.SetsDomain

universe u v

namespace FP

open AUXLib

class Order (A : Type u) where
  order_rel : A -> A -> Prop

class Equiv (A : Type u) where
  equiv : A -> A -> Prop

abbrev order_rel {A : Type u} [r : Order A] : A -> A -> Prop := r.order_rel
abbrev equiv {A : Type u} [e : Equiv A] : A -> A -> Prop := e.equiv

scoped infix:50 " <=o " => order_rel
scoped infix:50 " ==o " => equiv

class AntiSymmetric_Setoid (A : Type u) [Order A] [Equiv A] : Prop where
  antisymmetricity_setoid : forall a b : A,
    order_rel a b -> order_rel b a -> equiv a b

class PartialOrder_Setoid (A : Type u) [Order A] [Equiv A] : Prop where
  PO_AntiSymmetric_Setoid : AntiSymmetric_Setoid A
  PO_Reflexive_Setoid : forall x y : A, equiv x y -> order_rel x y
  PO_Transitive : Transitive (@order_rel A _)

instance partialOrderAntiSymmetric (A : Type u) [Order A] [Equiv A]
    [p : PartialOrder_Setoid A] : AntiSymmetric_Setoid A :=
  p.PO_AntiSymmetric_Setoid

instance partialOrderTransitive (A : Type u) [Order A] [Equiv A]
    [p : PartialOrder_Setoid A] : Transitive (@order_rel A _) := p.PO_Transitive

instance PartialOrder_Setoid_Reflexive (A : Type u) [Order A] [Equiv A]
    [e : AUXLib.Equivalence (@equiv A _)] [p : PartialOrder_Setoid A] :
    Reflexive (@order_rel A _) where
  refl x := p.PO_Reflexive_Setoid x x (e.refl x)

instance PartialOrder_Setoid_Proper (A : Type u) [Order A] [Equiv A]
    [e : AUXLib.Equivalence (@equiv A _)] [p : PartialOrder_Setoid A] :
    Proper (@equiv A _ ==> @equiv A _ ==> Iff) (@order_rel A _) where
  proper x x' hxx y y' hyy := by
    constructor
    · intro hxy
      exact p.PO_Transitive.trans _ x _
        (p.PO_Reflexive_Setoid x' x (e.symm _ _ hxx))
        (p.PO_Transitive.trans _ y _ hxy (p.PO_Reflexive_Setoid y y' hyy))
    · intro hxy
      exact p.PO_Transitive.trans _ x' _
        (p.PO_Reflexive_Setoid x x' hxx)
        (p.PO_Transitive.trans _ y' _ hxy
          (p.PO_Reflexive_Setoid y' y (e.symm _ _ hyy)))

def fixpoint {A : Type u} [Equiv A] (f : A -> A) (a : A) : Prop :=
  equiv a (f a)

def least_fixpoint {A : Type u} [Order A] [Equiv A]
    (f : A -> A) (a : A) : Prop :=
  fixpoint f a /\ forall a', fixpoint f a' -> order_rel a a'

def greatest_fixpoint {A : Type u} [Order A] [Equiv A]
    (f : A -> A) (a : A) : Prop :=
  fixpoint f a /\ forall a', fixpoint f a' -> order_rel a' a

theorem ProperR_ProperR' {A : Type u} [Order A] [Equiv A]
    [e : AUXLib.Equivalence (@equiv A _)] [p : PartialOrder_Setoid A]
    (f : A -> A) [hf : Proper (@order_rel A _ ==> @order_rel A _) f] :
    Proper (@equiv A _ ==> @equiv A _) f where
  proper x y hxy := by
    apply p.PO_AntiSymmetric_Setoid.antisymmetricity_setoid
    · exact hf.proper x y (p.PO_Reflexive_Setoid x y hxy)
    · exact hf.proper y x (p.PO_Reflexive_Setoid y x (e.symm _ _ hxy))

namespace PO_sets

instance R_sets {T : Type u} [Sets.SETS T] : Order T where
  order_rel := Sets.included

instance Equiv_sets {T : Type u} [Sets.SETS T] : Equiv T where
  equiv := Sets.equiv

instance PO_sets {T : Type u} [Sets.SETS T] [SETS_Properties T] :
    PartialOrder_Setoid T where
  PO_AntiSymmetric_Setoid := ⟨by
    intro x y hxy hyx
    exact (Sets_equiv_Sets_included x y).mpr ⟨hxy, hyx⟩⟩
  PO_Reflexive_Setoid := by
    intro x y hxy
    exact (Sets_equiv_Sets_included x y).mp hxy |>.1
  PO_Transitive := ⟨by
    intro x y z hxy hyz
    exact Sets_included_trans.trans _ _ _ hxy hyz⟩

instance Equiv_equiv_sets {T : Type u} [Sets.SETS T] [SETS_Properties T] :
    AUXLib.Equivalence (@equiv T (Equiv_sets (T := T))) := Sets_equiv_equiv

end PO_sets

namespace PO_lift

instance R_lift (A : Type u) {B : Type v} [Order B] : Order (A -> B) where
  order_rel := lift_rel2 order_rel

instance Equiv_lift (A : Type u) {B : Type v} [Equiv B] : Equiv (A -> B) where
  equiv := lift_rel2 equiv

instance PO_lift (A : Type u) {B : Type v} [Order B] [Equiv B]
    [p : PartialOrder_Setoid B] :
    PartialOrder_Setoid (A -> B) where
  PO_AntiSymmetric_Setoid := ⟨by
    intro x y hxy hyx a
    exact p.PO_AntiSymmetric_Setoid.antisymmetricity_setoid _ _ (hxy a) (hyx a)⟩
  PO_Reflexive_Setoid := by intro x y hxy a; exact p.PO_Reflexive_Setoid _ _ (hxy a)
  PO_Transitive := ⟨by intro x y z hxy hyz a; exact p.PO_Transitive.trans _ _ _ (hxy a) (hyz a)⟩

instance Equiv_equiv_lift (A : Type u) {B : Type v} [Equiv B]
    [e : AUXLib.Equivalence (@equiv B _)] :
    AUXLib.Equivalence (@equiv (A -> B) (Equiv_lift A)) where
  refl f a := e.refl (f a)
  symm f g h a := e.symm _ _ (h a)
  trans f g h hfg hgh a := e.trans _ _ _ (hfg a) (hgh a)

end PO_lift

macro "unfold_PO_defs" : tactic =>
  `(tactic| simp only [order_rel, equiv, PO_sets.R_sets, PO_sets.Equiv_sets,
      PO_lift.R_lift, PO_lift.Equiv_lift, lift_rel2])

end FP

export FP (Order Equiv order_rel equiv AntiSymmetric_Setoid PartialOrder_Setoid
  fixpoint least_fixpoint greatest_fixpoint ProperR_ProperR')
