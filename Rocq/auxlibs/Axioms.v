Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Theorem functional_extensionality :
    forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g.
Proof.
  intros.
  apply functional_extensionality_dep; auto.
Qed.

Theorem propositional_extensionality : forall (P Q : Prop),
  P <-> Q -> P = Q.
Proof.
  apply PropExtensionality.propositional_extensionality.
Qed.

Theorem fun_ext1 : forall (A B : Type) (f g : A -> B),
  (forall a, f a = g a) ->
  f = g.
Proof.
  intros. apply functional_extensionality. auto.
Qed.

Theorem fun_ext2 : forall (A B C : Type) (f g : A -> B -> C),
  (forall a b, f a b = g a b) ->
  f = g.
Proof.
  intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  auto.
Qed.

Theorem fun_ext3 : forall (A B C D : Type) (f g : A -> B -> C -> D),
  (forall a b c, f a b c = g a b c) ->
  f = g.
Proof.
  intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  auto.
Qed.

Theorem fun_ext4 : forall (A B C D E : Type) (f g : A -> B -> C -> D -> E),
  (forall a b c d, f a b c d = g a b c d) ->
  f = g.
Proof.
  intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  auto.
Qed.

Theorem pred_ext1 : forall (A : Type) (P Q : A -> Prop),
  (forall a, P a <-> Q a) ->
  P = Q.
Proof.
  intros.
  apply functional_extensionality. intros.
  apply propositional_extensionality.
  auto.
Qed.

Theorem pred_ext2 : forall (A B : Type) (P Q : A -> B -> Prop),
  (forall a b, P a b <-> Q a b) ->
  P = Q.
Proof.
  intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply propositional_extensionality.
  auto.
Qed.

Theorem pred_ext3 : forall (A B C : Type) (P Q : A -> B -> C -> Prop),
  (forall a b c, P a b c <-> Q a b c) ->
  P = Q.
Proof.
  intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply propositional_extensionality.
  auto.
Qed.

Theorem pred_ext4 : forall (A B C D : Type) (P Q : A -> B -> C -> D -> Prop),
  (forall a b c d, P a b c d <-> Q a b c d) ->
  P = Q.
Proof.
  intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply propositional_extensionality.
  auto.
Qed.
