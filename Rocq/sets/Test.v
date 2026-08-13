Require Import SetsClass.SetsClass.
Import SetsNotation.

Local Open Scope sets.

Module SetEleTest0.

Goal forall (A: Type) (X Y: A -> Prop) (a: A),
  X ⊆ Y ->
  a ∈ X ->
  a ∈ Y.
Proof.
  idtac "SetEle Test 0.".
  intros.
  rewrite H in H0.
  match type of H0 with
  | a ∈ Y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetEleTest0.

Module SetEleTest1.

Goal forall (A B: Type) (X Y: A -> B -> Prop) (a: A) (b: B),
  X ⊆ Y ->
  (a, b) ∈ X ->
  (a, b) ∈ Y.
Proof.
  idtac "SetEle Test 1".
  intros.
  rewrite <- H.
  match goal with
  | |- (a, b) ∈ X => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetEleTest1.

Module SetTest0a.

Goal forall (A: Type) (X Y: A -> Prop) (P: Prop),
  X ∩ Y == Y ∩ Sets.prop_inj P.
Proof.
  idtac "Set Test 0a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a : A, X a /\ Y a <-> Y a /\ P => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest0a.

Module SetTest0b.

Goal forall (A: Type) (X Y: A -> Prop) (P: Prop),
  X ∩ Y == Y ∩ Sets.prop_inj P.
Proof.
  idtac "Set Test 0b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall a : A, a ∈ X /\ a ∈ Y <-> a ∈ Y /\ P => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest0b.

Module SetTest0c.

Goal forall (A: Type) (X Y: A -> Prop) (P: Prop),
  X ∩ Y == Y ∩ Sets.prop_inj P.
Proof.
  idtac "Set Test 0c.".
  intros.
  Sets_unfold.
  sets_unfold.
  match goal with
  | |- forall a : A, X a /\ Y a <-> Y a /\ P => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest0c.

Module SetTest1a.

Goal forall (A B: Type) (X Y: A -> B -> Prop),
  X ∪ Y == Y ∪ X ∪ Y.
Proof.
  idtac "Set Test 1a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a b, X a b \/ Y a b <->
                   (Y a b \/ X a b) \/ Y a b => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest1a.

Module SetTest1b.

Goal forall (A B: Type) (X Y: A -> B -> Prop),
  X ∪ Y == Y ∪ X ∪ Y.
Proof.
  idtac "Set Test 1b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall (a : A) (a0 : B),
          (a, a0) ∈ X \/ (a, a0) ∈ Y <->
          ((a, a0) ∈ Y \/ (a, a0) ∈ X) \/ (a, a0) ∈ Y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest1b.

Module SetTest2a.

Goal forall (A: Type) (X: nat * bool -> A -> Prop) (Y: A -> Prop),
  ∅ ∪ ⋃ X ⊆ Y ∪ ∅.
Proof.
  idtac "Set Test 2a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a : A, False \/ (exists i : nat * bool, X i a) -> Y a \/ False => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest2a.

Module SetTest2b.

Goal forall (A: Type) (X: nat * bool -> A -> Prop) (Y: A -> Prop),
  ∅ ∪ ⋃ X ⊆ Y ∪ ∅.
Proof.
  idtac "Set Test 2b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall a : A, False \/ (exists i : nat * bool, a ∈ X i) -> a ∈ Y \/ False => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest2b.

Module SetTest2c.

Goal forall (A: Type) (X: nat * bool -> A -> Prop) (Y: A -> Prop),
  ∅ ∪ ⋃ X ⊆ Y ∪ ∅.
Proof.
  idtac "Set Test 2c.".
  intros.
  Sets_unfold1.
  match goal with
  | |- forall a : A, a ∈ ∅ ∪ ⋃ X -> a ∈ Y ∪ ∅ => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest2c.

Module SetTest2d.

Goal forall (A: Type) (X: nat * bool -> A -> Prop) (Y: A -> Prop),
  ∅ ∪ ⋃ X ⊆ Y ∪ ∅.
Proof.
  idtac "Set Test 2d.".
  intros.
  Sets_unfold1.
  intros a.
  Sets_unfold1.
  match goal with
  | |- a ∈ ∅ \/ a ∈ ⋃ X -> a ∈ Y ∪ ∅ => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest2d.

Module SetTest2e.

Goal forall (A: Type) (X: nat * bool -> A -> Prop) (Y: A -> Prop),
  ∅ ∪ ⋃ X ⊆ Y ∪ ∅.
Proof.
  idtac "Set Test 2e.".
  intros.
  sets_unfold1.
  match goal with
  | |- forall a : A, (∅ ∪ ⋃ X) a -> (Y ∪ ∅) a => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest2e.

Module SetTest2f.

Goal forall (A: Type) (X: nat * bool -> A -> Prop) (Y: A -> Prop),
  ∅ ∪ ⋃ X ⊆ Y ∪ ∅.
Proof.
  idtac "Set Test 2f.".
  intros.
  sets_unfold1.
  sets_unfold1.
  match goal with
  | |- forall a : A, ∅ a \/ (⋃ X) a -> (Y ∪ ∅) a => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest2f.

Module SetTest3a.

Goal forall (A: Type) (X: A -> A -> Prop) (Y: A -> Prop),
  ⋂ X ⊆ Y ∪ Sets.full.
Proof.
  idtac "Set Test 3a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a : A, (forall i : A, X i a) -> Y a \/ True => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest3a.

Module SetTest3b.

Goal forall (A: Type) (X: A -> A -> Prop) (Y: A -> Prop),
  ⋂ X ⊆ Y ∪ Sets.full.
Proof.
  idtac "Set Test 3b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall a : A, (forall i : A, a ∈ X i) -> a ∈ Y \/ True => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest3b.

Module SetTest4a.

Goal forall (A: Type) (X: nat -> A -> Prop) (Y: (A -> Prop) -> Prop),
  Sets.indexed_union X == Sets.general_union Y.
Proof.
  idtac "Set Test 4a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a : A, (exists i : nat, X i a) <-> (exists x : A -> Prop, Y x /\ x a) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest4a.

Module SetTest4b.

Goal forall (A: Type) (X: nat -> A -> Prop) (Y: (A -> Prop) -> Prop),
  Sets.indexed_union X == Sets.general_union Y.
Proof.
  idtac "Set Test 4b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall a : A, (exists i : nat, a ∈ X i) <-> (exists x : A -> Prop, Y x /\ a ∈ x) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest4b.

Module SetTest5a.

Goal forall (A B: Type) (X: nat -> A -> B -> Prop) (Y: (A -> B -> Prop) -> Prop),
  Sets.indexed_intersect X == Sets.general_intersect Y.
Proof.
  idtac "Set Test 5a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall (a : A) (b: B),
      (forall i : nat, X i a b) <->
      (forall x : A -> B -> Prop, Y x -> x a b) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest5a.

Module SetTest5b.

Goal forall (A B: Type) (X: nat -> A -> B -> Prop) (Y: (A -> B -> Prop) -> Prop),
  Sets.indexed_intersect X == Sets.general_intersect Y.
Proof.
  idtac "Set Test 5b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall (a : A) (b: B),
      (forall i : nat, (a, b) ∈ X i) <->
      (forall x : A -> B -> Prop, Y x -> (a, b) ∈ x) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest5b.

Module SetTest6.

Goal forall (X: nat -> nat -> Prop) (n m: nat),
  (n, m) ∈ X ->
  (n, m) ∈ X.
Proof.
  idtac "Set Test 6.".
  intros.
  sets_unfold.
  sets_unfold in H.
  match goal with
  | H: X n m  |- X n m => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest6.

Module SetTest7.

Goal forall (X: nat -> Prop) (Y: nat -> bool -> Prop) n m,
  Sets.filter1 X Y n m.
Proof.
  idtac "Set Test 7.".
  intros.
  sets_unfold.
  match goal with
  | |- X n /\ Y n m => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest7.

Module SetTest8a.

Goal forall (Y: nat -> bool -> Prop) n m,
  Sets.complement Y (S n) m ->
  Sets.complement Y n m.
Proof.
  idtac "Set Test 8a.".
  intros.
  sets_unfold.
  sets_unfold in H.
  match goal with
  | H: ~ Y (S n) m |- ~ Y n m => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest8a.

Module SetTest8b.

Goal forall (Y: nat -> bool -> Prop) n m,
  Sets.complement Y (S n) m ->
  Sets.complement Y n m.
Proof.
  idtac "Set Test 8b.".
  intros.
  Sets_unfold.
  Sets_unfold in H.
  match goal with
  | H: ~ (S n, m) ∈ Y |- ~ (n, m) ∈ Y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest8b.

Module SetTest9a.

Goal forall (Y: nat -> Prop) n m,
  (Y × nat) (S n) m ->
  (Y × nat) m n.
Proof.
  idtac "Set Test 9a.".
  intros.
  sets_unfold.
  sets_unfold in H.
  match goal with
  | H: Y (S n) /\ True |- Y m /\ True => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest9a.

Module SetTest9b.

Goal forall (Y: nat -> Prop) n m,
  (nat × Y) (S n) m ->
  (Y × nat) m n.
Proof.
  idtac "Set Test 9b.".
  intros.
  Sets_unfold.
  Sets_unfold in H.
  match goal with
  | H: True /\ m ∈ Y |- m ∈ Y /\ True => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest9b.

Module RelTest0.

Goal forall (A: Type) (X: A -> A -> Prop) (x y: A),
  Rels.concat X X x y: Prop.
Proof.
  idtac "Rel Test 0.".
  intros.
  sets_unfold.
  match goal with
  | |- exists x' : A, X x x' /\ X x' y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest0.

Module RelTest1.

Goal forall (A: Type) (X: A -> Prop) (x y: A),
  Rels.test X x y: Prop.
Proof.
  idtac "Rel Test 1.".
  intros.
  sets_unfold.
  match goal with
  | |- X x /\ x = y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest1.

Module RelTest2.

Goal forall (A: Type) (X: A -> A -> Prop) (x y: A) (H: Rels.concat X X x y: Prop),
  Rels.concat X X x y: Prop.
Proof.
  idtac "Rel Test 2.".
  intros.
  sets_unfold.
  sets_unfold in H.
  match goal with
  | H : exists x' : A, X x x' /\ X x' y |- exists x' : A, X x x' /\ X x' y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest2.

Module RelTest3.

Goal forall (A: Type) (X: A -> Prop) (x y: A) (H : Rels.test X x y: Prop),
  Rels.test X x y: Prop.
Proof.
  idtac "Rel Test 3.".
  intros.
  sets_unfold.
  sets_unfold in H.
  match goal with
  | H : X x /\ x = y |- X x /\ x = y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest3.

Module RelTest4a.

Goal forall (A B: Type) (X: A -> B -> Prop) (Y: B -> Prop) (x: A),
  (X ∘ Y) x <-> exists y, X x y /\ Y y.
Proof.
  idtac "Rel Test 4a.".
  intros.
  sets_unfold.
  match goal with
  | |- (exists b : B, X x b /\ Y b) <-> (exists y : B, X x y /\ Y y) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
  reflexivity.
Qed.

End RelTest4a.

Module RelTest4b.

Goal forall (A B: Type) (X: A -> B -> Prop) (Y: B -> Prop) (x: A),
  (X ∘ Y) x <-> True.
Proof.
  idtac "Rel Test 4b.".
  intros.
  Sets_unfold.
  match goal with
  | |- (exists b : B, (x, b) ∈ X /\ b ∈ Y) <-> True => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest4b.

Module RelTest5.

Goal forall (A B: Type) (X: A -> B -> Prop) (x: A) (y: B),
  (X ∘ Rels.id) x y <-> False.
Proof.
  idtac "Rel Test 5.".
  intros.
  Sets_unfold.
  match goal with
  | |- (exists i : B, (x, i) ∈ X /\ i = y) <-> False => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest5.

Module RelTest6.

Import List ListConn.

Goal forall (A: Type) (Y: A -> Prop) (x y: A) (l: list nat),
  Rels.test Y x l y: Prop.
Proof.
  idtac "Rel Test 6.".
  intros.
  sets_unfold.
  match goal with
  | |- Y x /\ l = nil /\ x = y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest6.

Module RelTest7.

Goal forall (A B: Type) (X: A -> B -> Prop) (Y: A -> Prop),
  (Y × A) ∘ X ⊆ Y × B.
Proof.
  idtac "Rel Test 7.".
  intros.
  Sets_unfold.
  intros a b.
  match goal with
  | |- (exists a': A,
           (a ∈ Y /\ True) /\ (a', b) ∈ X) ->
       (a ∈ Y /\ True) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
  intros [a' ?].
  tauto.
Qed.

End RelTest7.

Module RelTest8a.

Goal forall (A: Type) (X Y: A -> A -> Prop),
  X ∘ Y ⊆ Y ∘ Rels.id.
Proof.
  idtac "Rel Test 8a.".
  intros.
  Sets_unfold1.
  match goal with
  | |- forall a1 a2 : A, (a1, a2) ∈ X ∘ Y -> (a1, a2) ∈ Y ∘ Rels.id => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest8a.

Module RelTest8b.

Goal forall (A: Type) (X Y: A -> A -> Prop),
  X ∘ Y ⊆ Y ∘ Rels.id.
Proof.
  idtac "Rel Test 8b.".
  intros.
  Sets_unfold1.
  intros a1 a2.
  Sets_unfold1.
  match goal with
  | |- (exists i : A, (a1, i) ∈ X /\ (i, a2) ∈ Y) -> (a1, a2) ∈ Y ∘ Rels.id => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest8b.

Module RelTest8c.

Goal forall (A: Type) (X Y: A -> A -> Prop),
  X ∘ Y ⊆ Y ∘ Rels.id.
Proof.
  idtac "Rel Test 8c.".
  intros.
  Sets_unfold1.
  intros a1 a2 H.
  Sets_unfold1 in H.
  match goal with
  | H : exists i : A, (a1, i) ∈ X /\ (i, a2) ∈ Y |- (a1, a2) ∈ Y ∘ Rels.id => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest8c.

Module RelTest8d.

Goal forall (A: Type) (X Y: A -> A -> Prop),
  X ∘ Y ⊆ Y ∘ Rels.id.
Proof.
  idtac "Rel Test 8d.".
  intros.
  Sets_unfold1.
  intros a1 a3.
  Sets_unfold1.
  Sets_unfold1.
  intros [a2 [? ?]].
  exists a2.
  Sets_unfold1.
  match goal with
  | H : (a1, a2) ∈ X |- (a1, a2) ∈ Y /\ a2 = a3 => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest8d.

Goal forall (A: Type) (X Y: A -> A -> Prop),
  X ⊆ Y ∪ X.
Proof.
  intros.
  sets_unfold.
  intros.
  right.
  exact H.
Qed.

Print Unnamed_thm.

Goal forall {A B C: Type} (x : A -> B -> Prop) (y: B -> C -> Prop), x == ∅ -> x ∘ y == ∅.
  intros.
  rewrite H.
  apply Rels_concat_empty_l.
Qed.

Goal forall {A B: Type} (x: A -> B -> Prop), x ∘ ∅ == ∅.
  intros.
  apply Rels_concat_empty_r.
Qed.
