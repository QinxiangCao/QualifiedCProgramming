universe u v

namespace Unifysl
namespace Relation_ext

def Reflexive {A : Sort u} (R : A -> A -> Prop) : Prop :=
  forall x, R x x

def Symmetric {A : Sort u} (R : A -> A -> Prop) : Prop :=
  forall x y, R x y -> R y x

def Transitive {A : Sort u} (R : A -> A -> Prop) : Prop :=
  forall x y z, R x y -> R y z -> R x z

def relation (A : Type u) : Type u :=
  A -> A -> Prop

def inclusion (A : Type u) (R1 R2 : relation A) : Prop :=
  forall x y, R1 x y -> R2 x y

def same_relation (A : Type u) (R1 R2 : relation A) : Prop :=
  inclusion A R1 R2 /\ inclusion A R2 R1

def relation_conjunction {A : Type u} (R1 R2 : relation A) : relation A :=
  fun x y => R1 x y /\ R2 x y

def relation_disjunction {A : Type u} (R1 R2 : relation A) : relation A :=
  fun x y => R1 x y \/ R2 x y

def pointwise_relation (A : Type u) {B : Sort v} (R : B -> B -> Prop) (f g : A -> B) : Prop :=
  forall a, R (f a) (g a)

def full_relation {A : Type u} : relation A :=
  fun _ _ => True

def respectful {A : Sort u} {B : Sort v}
    (RA : A -> A -> Prop) (RB : B -> B -> Prop) : (A -> B) -> (A -> B) -> Prop :=
  fun f g => forall x y, RA x y -> RB (f x) (g y)

infixr:55 " ==> " => respectful

class Proper {A : Sort u} (R : A -> A -> Prop) (x : A) : Prop where
  proper : R x x

theorem inclusion_full_relation :
    forall {A : Type u} (P : relation A), inclusion A P full_relation := by
  intro A P x y h
  trivial

theorem same_relation_spec :
    forall {A : Type u} (a1 a2 : relation A),
      same_relation A a1 a2 <->
        pointwise_relation A (pointwise_relation A Iff) a1 a2 := by
  intro A a1 a2
  constructor
  · intro h x y
    exact ⟨h.left x y, h.right x y⟩
  · intro h
    constructor
    · intro x y hx
      exact (h x y).mp hx
    · intro x y hx
      exact (h x y).mpr hx

theorem same_relation_Reflexive {A : Type u} : Reflexive (same_relation A) := by
  intro R
  constructor <;> intro x y h <;> exact h

theorem same_relation_Symmetric {A : Type u} : Symmetric (same_relation A) := by
  intro R S h
  exact ⟨h.right, h.left⟩

theorem same_relation_Transitive {A : Type u} : Transitive (same_relation A) := by
  intro R S T hRS hST
  constructor
  · intro x y hxy
    exact hST.left x y (hRS.left x y hxy)
  · intro x y hxy
    exact hRS.right x y (hST.right x y hxy)

instance same_relation_Equivalence {A : Type u} : Equivalence (same_relation A) where
  refl := same_relation_Reflexive
  symm := by
    intro R S h
    exact same_relation_Symmetric R S h
  trans := by
    intro R S T hRS hST
    exact same_relation_Transitive R S T hRS hST

instance inclusion_proper {A : Type u} :
    Proper (same_relation A ==> same_relation A ==> Iff) (inclusion A) where
  proper := by
    intro R1 R2 hR S1 S2 hS
    constructor
    · intro h x y hx
      exact hS.left x y (h x y (hR.right x y hx))
    · intro h x y hx
      exact hS.right x y (h x y (hR.left x y hx))

theorem app_same_relation :
    forall {A : Type u} (R1 R2 : relation A) (a1 a2 : A),
      same_relation A R1 R2 ->
      (R1 a1 a2 <-> R2 a1 a2) := by
  intro A R1 R2 a1 a2 h
  exact ⟨h.left a1 a2, h.right a1 a2⟩

inductive compond_relation {A : Type u} (R1 R2 : relation A) : relation A where
  | compond_intro : forall x y z, R1 x y -> R2 y z -> compond_relation R1 R2 x z

export compond_relation (compond_intro)

theorem compond_relation_spec :
    forall {A : Type u} (R1 R2 : relation A) x z,
      compond_relation R1 R2 x z ->
      exists y, R1 x y /\ R2 y z := by
  intro A R1 R2 x z h
  cases h with
  | compond_intro x y z h1 h2 =>
      exact ⟨y, h1, h2⟩

theorem compond_relation_inclusion :
    forall {A : Type u} (R1 R2 R3 R4 : relation A),
      inclusion A R1 R2 ->
      inclusion A R3 R4 ->
      inclusion A (compond_relation R1 R3) (compond_relation R2 R4) := by
  intro A R1 R2 R3 R4 h12 h34 x z h
  cases h with
  | compond_intro x y z h1 h3 =>
      exact compond_intro x y z (h12 x y h1) (h34 y z h3)

instance compond_relation_proper {A : Type u} :
    Proper (same_relation A ==> same_relation A ==> same_relation A) (compond_relation (A := A)) where
  proper := by
    intro R1 R2 hR S1 S2 hS
    constructor
    · exact compond_relation_inclusion R1 R2 S1 S2 hR.left hS.left
    · exact compond_relation_inclusion R2 R1 S2 S1 hR.right hS.right

theorem compond_assoc :
    forall {A : Type u} (R1 R2 R3 : relation A),
      same_relation A
        (compond_relation (compond_relation R1 R2) R3)
        (compond_relation R1 (compond_relation R2 R3)) := by
  intro A R1 R2 R3
  constructor
  · intro x z h
    cases h with
    | compond_intro x yz z h12 h3 =>
        cases h12 with
        | compond_intro x y yz h1 h2 =>
            exact compond_intro x y z h1 (compond_intro y yz z h2 h3)
  · intro x z h
    cases h with
    | compond_intro x y z h1 h23 =>
        cases h23 with
        | compond_intro y yz z h2 h3 =>
            exact compond_intro x yz z (compond_intro x y yz h1 h2) h3

theorem compond_eq_right :
    forall {A : Type u} (R : relation A),
      same_relation A (compond_relation R Eq) R := by
  intro A R
  constructor
  · intro x z h
    cases h with
    | compond_intro x y z hR hEq =>
        cases hEq
        exact hR
  · intro x z h
    exact compond_intro x z z h rfl

theorem compond_eq_left :
    forall {A : Type u} (R : relation A),
      same_relation A (compond_relation Eq R) R := by
  intro A R
  constructor
  · intro x z h
    cases h with
    | compond_intro x y z hEq hR =>
        cases hEq
        exact hR
  · intro x z h
    exact compond_intro x x z rfl h

theorem relation_conjunction_inclusion :
    forall {A : Type u} (R1 R2 R3 R4 : relation A),
      inclusion A R1 R2 ->
      inclusion A R3 R4 ->
      inclusion A (relation_conjunction R1 R3) (relation_conjunction R2 R4) := by
  intro A R1 R2 R3 R4 h12 h34 x y h
  exact ⟨h12 x y h.left, h34 x y h.right⟩

instance relation_conjunction_proper {A : Type u} :
    Proper (same_relation A ==> same_relation A ==> same_relation A) (relation_conjunction (A := A)) where
  proper := by
    intro R1 R2 hR S1 S2 hS
    constructor
    · exact relation_conjunction_inclusion R1 R2 S1 S2 hR.left hS.left
    · exact relation_conjunction_inclusion R2 R1 S2 S1 hR.right hS.right

theorem relation_conjunction_iff :
    forall {A : Type u} (R R' : relation A) x y,
      relation_conjunction R R' x y <-> R x y /\ R' x y := by
  intros
  rfl

theorem relation_disjunction_iff :
    forall {A : Type u} (R R' : relation A) x y,
      relation_disjunction R R' x y <-> R x y \/ R' x y := by
  intros
  rfl

theorem relation_disjunction_inclusion_left :
    forall {A : Type u} (R R' : relation A),
      inclusion A R (relation_disjunction R R') := by
  intro A R R' x y h
  exact Or.inl h

theorem relation_disjunction_inclusion_right :
    forall {A : Type u} (R R' : relation A),
      inclusion A R' (relation_disjunction R R') := by
  intro A R R' x y h
  exact Or.inr h

def respectful_relation {A : Type u} {B : Type v} (f : A -> B) (R : relation B) : relation A :=
  fun x y => R (f x) (f y)

def fst_relation {A : Type u} {B : Type v} (R : relation A) : relation (A × B) :=
  respectful_relation (fun p : A × B => p.1) R

def snd_relation {A : Type u} {B : Type v} (R : relation B) : relation (A × B) :=
  respectful_relation (fun p : A × B => p.2) R

instance respectful_relation_proper {A : Type u} {B : Type v} (f : A -> B) :
    Proper (same_relation B ==> same_relation A) (respectful_relation f) where
  proper := by
    intro R1 R2 hR
    constructor
    · intro x y h
      exact hR.left (f x) (f y) h
    · intro x y h
      exact hR.right (f x) (f y) h

theorem respectful_compond_relation :
    forall {A : Type u} {B : Type v} (f : A -> B) (R1 R2 : relation B),
      inclusion A
        (compond_relation (respectful_relation f R1) (respectful_relation f R2))
        (respectful_relation f (compond_relation R1 R2)) := by
  intro A B f R1 R2 a1 a2 h
  rcases compond_relation_spec
      (respectful_relation f R1) (respectful_relation f R2) a1 a2 h with
    ⟨a, h1, h2⟩
  exact compond_intro (f a1) (f a) (f a2) h1 h2

def partial_functional {A : Type u} (R : relation A) : Prop :=
  forall m n n', R m n -> R m n' -> n = n'

class PartialFunctional {A : Type u} (R : relation A) : Prop where
  partial_functionality : forall m n n', R m n -> R m n' -> n = n'

export PartialFunctional (partial_functionality)

def functional {A : Type u} (R : relation A) : Prop :=
  forall m, exists n, forall n', R m n' <-> n' = n

class Functional {A : Type u} (R : relation A) : Prop where
  functionality : forall m, exists n, forall n', R m n' <-> n' = n

export Functional (functionality)

def serial {A : Type u} (R : relation A) : Prop :=
  forall m, exists n, R m n

class Serial {A : Type u} (R : relation A) : Prop where
  seriality : forall m, exists n, R m n

export Serial (seriality)

theorem function_Functional {A : Type u} {f : A -> A} : Functional (fun a => Eq (f a)) := by
  constructor
  intro m
  exists f m
  intro n'
  constructor
  · intro h
    exact h.symm
  · intro h
    exact h.symm

theorem SerialPartialFunctional_Functional {A : Type u} {R : relation A} :
    Serial R -> PartialFunctional R -> Functional R := by
  intro hS hPF
  constructor
  intro m
  rcases hS.seriality m with ⟨n, hn⟩
  exists n
  intro n'
  constructor
  · intro h
    exact hPF.partial_functionality m n' n h hn
  · intro h
    cases h
    exact hn

instance Functional_PartialFunctional {A : Type u} {R : relation A} [Functional R] :
    PartialFunctional R := by
  constructor
  intro m n n' hmn hmn'
  let hF := inferInstanceAs (Functional R)
  rcases hF.functionality m with ⟨n0, hn0⟩
  have hn : n = n0 := (hn0 n).mp hmn
  have hn' : n' = n0 := (hn0 n').mp hmn'
  exact hn.trans hn'.symm

instance Functional_Serial {A : Type u} {R : relation A} [Functional R] :
    Serial R := by
  constructor
  intro m
  let hF := inferInstanceAs (Functional R)
  rcases hF.functionality m with ⟨n, hn⟩
  exists n
  exact (hn n).mpr rfl

class Inclusion {A : Type u} (R1 R2 : relation A) : Prop where
  including : forall a b, R1 a b -> R2 a b

export Inclusion (including)

end Relation_ext
end Unifysl
