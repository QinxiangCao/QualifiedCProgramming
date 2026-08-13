import AUXLib.SetoidRewrite

open AUXLib

namespace AUXLibSetoidRewriteTests

inductive Box where
  | wrap (value : Nat)

def BoxRel : Box -> Box -> Prop
  | .wrap x, .wrap y => x = y

theorem BoxRel_equiv : AUXLib.Equivalence BoxRel where
  refl := by intro ⟨x⟩; exact Eq.refl x
  symm := by intro ⟨x⟩ ⟨y⟩ h; exact h.symm
  trans := by intro ⟨x⟩ ⟨y⟩ ⟨z⟩ hxy hyz; exact hxy.trans hyz

attribute [instance] BoxRel_equiv

theorem wrap_congr : Proper (Eq ==> BoxRel) Box.wrap where
  proper := by intro x y h; exact h

attribute [instance] wrap_congr

def unbox : Box -> Nat
  | .wrap value => value

theorem unbox_congr : Proper (BoxRel ==> Eq) unbox where
  proper := by intro ⟨x⟩ ⟨y⟩ h; exact h

attribute [instance] unbox_congr

example (a : Nat) : Proper (Eq ==> Iff) ((@Eq Nat) (unbox (.wrap a))) := inferInstance

example (a b : Nat) (h : a = b) : unbox (.wrap a) = unbox (.wrap b) := by
  rel_rw [h]
  rfl

example (a b : Nat) (h : a = b) : unbox (.wrap b) = unbox (.wrap a) := by
  rel_rw [← h]
  rfl

example (a b : Nat) (h : a = b) (H : unbox (.wrap a) = 0) :
    unbox (.wrap b) = 0 := by
  rel_rw [h] at H
  exact H

example (a b : Nat) (h : a = b) : unbox (.wrap a) = unbox (.wrap a) := by
  rel_rw (occs := 2) [h]
  rel_rw [h]
  rfl

example (a b : Nat) (h : a = b) : unbox (.wrap a) = unbox (.wrap a) := by
  rel_rw! [h]
  rfl

opaque observe : Box -> Nat := fun
  | .wrap n => n

example (a b : Nat) (_h : a = b) : observe (.wrap a) = observe (.wrap a) := by
  fail_if_success rel_rw [_h]
  rfl

abbrev ImplRel (P Q : Prop) : Prop :=
  P -> Q

instance natLeRight_congr (k : Nat) : Proper (Nat.le ==> ImplRel) (Nat.le k) where
  proper := by
    intro a b hab hka
    exact Nat.le_trans hka hab

example : ForwardTransport ImplRel := inferInstance

example (k a b : Nat) (hab : Nat.le a b) (hka : Nat.le k a) : Nat.le k b := by
  rel_rw [hab] at hka
  exact hka

example (k a b : Nat) (hab : Nat.le a b) (hka : Nat.le k a) : Nat.le k b := by
  rel_rw [← hab]
  exact hka

example (k a b : Nat) (_hab : Nat.le a b) (hka : Nat.le k a) : Nat.le k a := by
  fail_if_success rel_rw [_hab]
  exact hka

example (k a b : Nat) (_hab : Nat.le a b) (hkb : Nat.le k b) : Nat.le k b := by
  fail_if_success rel_rw [← _hab] at hkb
  exact hkb

example (a b : Nat) (h : a = b) :
    (forall x : Nat, x = a -> x = a) := by
  rel_rw! [h]
  intro x
  exact fun hx => hx

example (a b : Nat) (h : a = b) :
    (forall x : Nat, x = a -> x = a) := by
  rel_rw (occs := 2) [h]
  rel_rw [h]
  intro x
  exact fun hx => hx

example (a b : Nat) (h : a = b) :
    (Exists fun x : Nat => x = a) <-> Exists fun x : Nat => x = b := by
  rel_rw [h]
  rfl

example (a b : Nat) (h : a = b) :
    (forall _x : Nat, Exists fun y : Nat => y = a) <->
      (forall _x : Nat, Exists fun y : Nat => y = b) := by
  rel_rw [h]
  rfl

example (f g : Nat -> Nat) (h : forall x, f x = g x) :
    forall x, f x = g x := by
  rel_rw [h]
  intro x
  rfl

example (P Q : Prop) (h : implication P Q) : P -> Q := by
  rel_rw [h]
  exact fun hQ => hQ

example (P Q R : Prop) (h : implication P Q) :
    (Q -> R) -> (P -> R) := by
  rel_rw [h]
  exact fun hPR => hPR

example (P Q R : Prop) (h : P <-> Q) : (P ∧ R) <-> (Q ∧ R) := by
  rel_rw [h]
  rfl

example (P Q R : Prop) (h : P <-> Q) : (Q ∨ R) <-> (P ∨ R) := by
  rel_rw [← h]
  rfl

example {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop)
    (f : A -> B) [ProperFunction RA f RB] :
    ProperFunction (flipRel (flipRel RA)) f (flipRel (flipRel RB)) :=
  inferInstance

example {A B C : Type} (R : B -> B -> Prop) (S : C -> C -> Prop)
    (f : (A -> B) -> C) [ProperFunction (pointwise_relation A R) f S] :
    ProperFunction
      (flipRel (dependentPointwise (fun _ : A => flipRel R))) f S :=
  inferInstance

inductive DepTag where
  | nat
  | bool

def DepCarrier : DepTag -> Type
  | .nat => Nat
  | .bool => Bool

example {C : Type} (S : C -> C -> Prop)
    (f : (forall tag, DepCarrier tag) -> C)
    [ProperFunction
      (dependentPointwise (fun tag => @Eq (DepCarrier tag))) f S] :
    ProperFunction
      (flipRel (dependentPointwise
        (fun tag => flipRel (@Eq (DepCarrier tag))))) f S :=
  inferInstance

example (P Q : Prop) (h : P <-> Q) : (P ∧ P) <-> (Q ∧ Q) := by
  rel_rw [h]
  rel_rw [h]
  rfl

example (P Q R : Prop) (h : implication P Q) (hRP : R -> P) : R -> Q := by
  rel_rw [h] at hRP
  exact hRP

example (P Q R : Prop) (_h : implication P Q) (_hQR : Q -> R) : True := by
  fail_if_success rel_rw [_h] at _hQR
  trivial

example (P Q Side : Prop) (h : Side -> (P <-> Q)) (hs : Side) (hq : Q) : P := by
  rel_rw [h]
  · exact hq
  · exact hs

example (P Q Side : Prop) (h : Side -> (P <-> Q)) (hs : Side) (hp : P) : Q := by
  rel_rw [h] at hp
  · exact hp
  · exact hs

example (P Q Side₁ Side₂ : Prop) (h : Side₁ -> Side₂ -> (P <-> Q))
    (hs₁ : Side₁) (hs₂ : Side₂) (hq : Q) : P := by
  rel_rw [h]
  · exact hq
  · exact hs₁
  · exact hs₂

example (f g : Nat -> Nat) (a b : Nat) (Side : Nat -> Prop)
    (h : forall x, Side x -> f x = g x)
    (ha : Side a) (hb : Side b) (hg : g a = g b) : f a = f b := by
  rel_rw! [h]
  · exact hg
  · exact hb
  · exact ha

example (f g : Nat -> Nat) (a : Nat) (h : forall x, f x = g x)
    (hout : g (g a) = g (g a)) :
    f (f a) = f (f a) := by
  rel_rw! [h]
  exact hout

example (P : Prop) (_h : P <-> P) : P <-> P := by
  fail_if_success rel_rw! [_h]
  rfl

example (P Q : Prop) (_h : P <-> Q) : True := by
  fail_if_success rel_rw! [_h]
  trivial

end AUXLibSetoidRewriteTests
