import SetsClass.SetsClass

open scoped SetsNotation

-- Candidate SetTest1c: unary set membership must not create a recursive In shape.
example {A : Type} (X Y : A -> Prop) :
    Sets.included (Sets.union X Y) (Sets.union (Sets.union Y X) Y) := by
  Sets_unfold
  guard_target =ₛ forall a : A, X a ∨ Y a -> (Y a ∨ X a) ∨ Y a
  intro a h
  rcases h with hx | hy
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hy

-- Candidate SetTest1d: the same normalization must terminate for binary sets.
example {A B : Type} (X Y : A -> B -> Prop) (a : A) (b : B) :
    SetsEle.In (a, b) (Sets.union X Y) ->
      SetsEle.In (a, b) (Sets.union (Sets.union Y X) Y) := by
  Sets_unfold
  guard_target =ₛ X a b ∨ Y a b -> (Y a b ∨ X a b) ∨ Y a b
  intro h
  rcases h with hx | hy
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hy

-- Candidate SetTest10: Prop is already its own membership predicate.
example (X Y : Prop) (hYX : Y -> X) : Sets.included X Y -> Sets.equiv X Y := by
  Sets_unfold
  guard_target =ₛ (X -> Y) -> (X <-> Y)
  intro hXY
  exact ⟨hXY, hYX⟩

-- Candidate RelTest9a: Rels.test must be found below relation composition.
example {A : Type} (X Y : A -> A -> Prop) (Z : A -> Prop)
    (hY : forall a b, X a b -> Y a b) (hZ : forall a b, X a b -> Z b) :
    Sets.included X
      (Rels.concat Y (Rels.test Z : A -> A -> Prop) : A -> A -> Prop) := by
  Sets_unfold
  guard_target =ₛ forall a b : A,
    X a b -> exists i : A, Y a i ∧ Z i ∧ i = b
  intro a b hab
  exact ⟨b, hY a b hab, hZ a b hab, rfl⟩

-- Candidate RelTest9b: a standalone test relation unfolds to membership and equality.
example {A : Type} (X : A -> Prop) (a b : A) (hX : X a) (hab : a = b) :
    (Rels.test X : A -> A -> Prop) a b := by
  Sets_unfold
  guard_target =ₛ X a ∧ a = b
  exact ⟨hX, hab⟩

-- Candidate RelTest9c: test also unfolds in the right side of composition.
example {A : Type} (X : A -> Prop) (Y : A -> A -> Prop) (a b : A)
    (hY : Y a b) (hX : X b) :
    (Rels.concat Y (Rels.test X : A -> A -> Prop) : A -> A -> Prop) a b := by
  Sets_unfold
  guard_target =ₛ exists i : A, Y a i ∧ X i ∧ i = b
  exact ⟨b, hY, hX, rfl⟩

-- Goal and selected-hypothesis forms share the same relation extension.
example {A : Type} (X : A -> Prop) (a b : A)
    (h : (Rels.test X : A -> A -> Prop) a b) :
    X a ∧ a = b := by
  Sets_unfold at h
  Sets_unfold at h
  guard_hyp h :ₛ X a ∧ a = b
  exact h

-- Repeated normalization is a successful no-op and cannot reintroduce In.
example {A : Type} (X : A -> Prop) (a : A) (h : SetsEle.In a X) : X a := by
  sets_unfold at h
  sets_unfold at h
  guard_hyp h :ₛ X a
  exact h

example {A B C : Type} (X : A -> B -> C -> Prop) (a : A) (b : B) (c : C)
    (h : SetsEle.In ((a, b), c) X) : X a b c := by
  sets_unfold at h
  guard_hyp h :ₛ X a b c
  exact h

-- Exercise unfold_In directly: Sets_unfold must not be needed to expose membership.
example {A : Type} (X : A -> Prop) (a : A) : SetsEle.In a X -> X a := by
  unfold_In
  unfold_In
  guard_target =ₛ X a -> X a
  intro h
  exact h

example {A B C D : Type} (X : A -> B -> C -> D -> Prop)
    (a : A) (b : B) (c : C) (d : D)
    (h : SetsEle.In (((a, b), c), d) X) : X a b c d := by
  unfold_In at h
  unfold_In at h
  guard_hyp h :ₛ X a b c d
  exact h

-- Direct unfold_In remains a successful no-op at both supported locations.
example (P : Prop) (h : P) : P := by
  unfold_In
  unfold_In at h
  guard_target =ₛ P
  guard_hyp h :ₛ P
  exact h

-- Sets_unfold only unfolds Sets infrastructure, not unrelated uses of Lean's id.
example (P : Prop) (h : id P) : id P := by
  Sets_unfold
  guard_target =ₛ id P
  exact h

example (P : Prop) (hP : P) : P := by
  Sets_unfold
  exact hP
