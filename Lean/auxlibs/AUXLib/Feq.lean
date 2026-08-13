import AUXLib.Morphisms

universe u v w

namespace AUXLib

def f_eq_dep {A : Type u} {B : A -> Type v}
    (f g : (x : A) -> B x) : Prop :=
  forall x, f x = g x

instance f_eq_dep_refl (A : Type u) (B : A -> Type v) :
    Reflexive (@f_eq_dep A B) where
  refl := by
    intro f x
    rfl

instance f_eq_dep_symm (A : Type u) (B : A -> Type v) :
    Symmetric (@f_eq_dep A B) where
  symm := by
    intro f g h x
    exact (h x).symm

instance f_eq_dep_trans (A : Type u) (B : A -> Type v) :
    Transitive (@f_eq_dep A B) where
  trans := by
    intro f g h hfg hgh x
    exact (hfg x).trans (hgh x)

instance f_eq_dep_equiv (A : Type u) (B : A -> Type v) :
    Equivalence (@f_eq_dep A B) where
  refl := by
    intro f
    exact (f_eq_dep_refl A B).refl f
  symm := by
    intro f g h
    exact (f_eq_dep_symm A B).symm f g h
  trans := by
    intro f g h hfg hgh
    exact (f_eq_dep_trans A B).trans f g h hfg hgh

def f_eq {A : Type u} {B : Type v} (f g : A -> B) : Prop :=
  forall x, f x = g x

instance f_eq_refl (A : Type u) (B : Type v) : Reflexive (@f_eq A B) where
  refl := by
    intro f x
    rfl

instance f_eq_symm (A : Type u) (B : Type v) : Symmetric (@f_eq A B) where
  symm := by
    intro f g h x
    exact (h x).symm

instance f_eq_trans (A : Type u) (B : Type v) : Transitive (@f_eq A B) where
  trans := by
    intro f g h hfg hgh x
    exact (hfg x).trans (hgh x)

instance f_eq_equiv (A : Type u) (B : Type v) : Equivalence (@f_eq A B) where
  refl := by
    intro f
    exact (f_eq_refl A B).refl f
  symm := by
    intro f g h
    exact (f_eq_symm A B).symm f g h
  trans := by
    intro f g h hfg hgh
    exact (f_eq_trans A B).trans f g h hfg hgh

def f_eq2 {A1 : Type u} {A2 : Type v} {B : Type w}
    (f g : A1 -> A2 -> B) : Prop :=
  forall x y, f x y = g x y

instance f_eq2_refl (A1 : Type u) (A2 : Type v) (B : Type w) :
    Reflexive (@f_eq2 A1 A2 B) where
  refl := by
    intro f x y
    rfl

instance f_eq2_symm (A1 : Type u) (A2 : Type v) (B : Type w) :
    Symmetric (@f_eq2 A1 A2 B) where
  symm := by
    intro f g h x y
    exact (h x y).symm

instance f_eq2_trans (A1 : Type u) (A2 : Type v) (B : Type w) :
    Transitive (@f_eq2 A1 A2 B) where
  trans := by
    intro f g h hfg hgh x y
    exact (hfg x y).trans (hgh x y)

instance f_eq2_equiv (A1 : Type u) (A2 : Type v) (B : Type w) :
    Equivalence (@f_eq2 A1 A2 B) where
  refl := by
    intro f
    exact (f_eq2_refl A1 A2 B).refl f
  symm := by
    intro f g h
    exact (f_eq2_symm A1 A2 B).symm f g h
  trans := by
    intro f g h hfg hgh
    exact (f_eq2_trans A1 A2 B).trans f g h hfg hgh

end AUXLib
