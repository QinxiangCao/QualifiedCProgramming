universe u v w x y

namespace AUXLib

theorem functional_extensionality
    (A : Type u) (B : A -> Type v) (f g : (a : A) -> B a)
    (h : forall a, f a = g a) : f = g := by
  funext a
  exact h a

theorem propositional_extensionality (P Q : Prop) (h : P <-> Q) : P = Q :=
  propext h

theorem fun_ext1 (A : Type u) (B : Type v) (f g : A -> B)
    (h : forall a, f a = g a) : f = g := by
  funext a
  exact h a

theorem fun_ext2 (A : Type u) (B : Type v) (C : Type w) (f g : A -> B -> C)
    (h : forall a b, f a b = g a b) : f = g := by
  funext a b
  exact h a b

theorem fun_ext3 (A : Type u) (B : Type v) (C : Type w) (D : Type x)
    (f g : A -> B -> C -> D) (h : forall a b c, f a b c = g a b c) : f = g := by
  funext a b c
  exact h a b c

theorem fun_ext4 (A : Type u) (B : Type v) (C : Type w) (D : Type x) (E : Type y)
    (f g : A -> B -> C -> D -> E) (h : forall a b c d, f a b c d = g a b c d) : f = g := by
  funext a b c d
  exact h a b c d

theorem pred_ext1 (A : Type u) (P Q : A -> Prop)
    (h : forall a, P a <-> Q a) : P = Q := by
  funext a
  exact propext (h a)

theorem pred_ext2 (A : Type u) (B : Type v) (P Q : A -> B -> Prop)
    (h : forall a b, P a b <-> Q a b) : P = Q := by
  funext a b
  exact propext (h a b)

theorem pred_ext3 (A : Type u) (B : Type v) (C : Type w) (P Q : A -> B -> C -> Prop)
    (h : forall a b c, P a b c <-> Q a b c) : P = Q := by
  funext a b c
  exact propext (h a b c)

theorem pred_ext4 (A : Type u) (B : Type v) (C : Type w) (D : Type x)
    (P Q : A -> B -> C -> D -> Prop)
    (h : forall a b c d, P a b c d <-> Q a b c d) : P = Q := by
  funext a b c d
  exact propext (h a b c d)

end AUXLib
