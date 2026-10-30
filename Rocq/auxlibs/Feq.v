Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

(* Dependent functions *)
Definition f_eq_dep {A: Type} {B: A -> Type} (f g: forall x: A, B x) : Prop :=
  forall x, f x = g x.

#[export] Instance f_eq_dep_refl (A: Type) (B: A -> Type) :
  Reflexive (@f_eq_dep A B).
Proof.
  unfold Reflexive, f_eq_dep.
  intros. reflexivity.
Qed.

#[export] Instance f_eq_dep_symm (A: Type) (B: A -> Type) :
  Symmetric (@f_eq_dep A B).
Proof.
  unfold Symmetric, f_eq_dep.
  intros. symmetry. apply H.
Qed.

#[export] Instance f_eq_dep_trans (A: Type) (B: A -> Type) :
  Transitive (@f_eq_dep A B).
Proof.
  unfold Transitive, f_eq_dep.
  intros x y z H1 H2 a. transitivity (y a); [apply H1 | apply H2].
Qed.

#[export] Instance f_eq_dep_equiv (A: Type) (B: A -> Type) :
  Equivalence (@f_eq_dep A B).
Proof.
  intros. split.
  - apply f_eq_dep_refl.
  - apply f_eq_dep_symm.
  - apply f_eq_dep_trans.
Qed.

(* Allows rewriting [H: f_eq_dep f g] in the goal of the form [f x = ...].
The number is the priority. Bigger number means lower priority.
This lower priority allows other instances to be applied first.
From https://rocq-prover.org/doc/V8.20.1/refman/addendum/type-classes.html#coq:cmd.Instance :
If the priority is not specified, the default is the number of non-dependent binders of the instance. *)
#[export] Instance f_eq_dep_app_proper {A: Type} {B: A -> Type} (x: A) :
  Proper (@f_eq_dep A B ==> eq) (fun f => f x) | 1000.
Proof.
  intros f g H_feq.
  unfold f_eq_dep in H_feq.
  apply H_feq.
Qed.


(* Non-dependent functions *)
Definition f_eq {A B : Type} (f g : A -> B) : Prop := Eval compute in f_eq_dep f g.

#[export] Instance f_eq_refl (A B : Type) : Reflexive (@f_eq A B) := f_eq_dep_refl _ _.

#[export] Instance f_eq_symm (A B : Type) : Symmetric (@f_eq A B) := f_eq_dep_symm _ _.

#[export] Instance f_eq_trans (A B : Type) : Transitive (@f_eq A B) := f_eq_dep_trans _ _.

#[export] Instance f_eq_equiv (A B : Type) : Equivalence (@f_eq A B) := f_eq_dep_equiv _ _.

(* Allows rewriting [H: f_eq f g] in the goal of the form [f x = ...] *)
#[export] Instance feq_app_proper {A B} :
  Proper (f_eq ==> eq ==> eq) (fun (f : A -> B) (x : A) => f x) | 1000.
Proof.
  intros f g Hf x y <-.
  apply Hf.
Qed.

Definition f_eq2 {A1 A2 B : Type} (f g : A1 -> A2 -> B) : Prop :=
  forall x y, f x y = g x y.

#[export] Instance f_eq2_refl (A1 A2 B : Type) :
  Reflexive (@f_eq2 A1 A2 B).
Proof.
  unfold Reflexive, f_eq2.
  intros. reflexivity.
Qed.

#[export] Instance f_eq2_symm (A1 A2 B : Type) :
  Symmetric (@f_eq2 A1 A2 B).
Proof.
  unfold Symmetric, f_eq2.
  intros. symmetry. apply H.
Qed.

#[export] Instance f_eq2_trans (A1 A2 B : Type) :
  Transitive (@f_eq2 A1 A2 B).
Proof.
  unfold Transitive, f_eq2.
  intros f g h. intros. transitivity (g x y); auto.
Qed.

#[export] Instance f_eq2_equiv (A1 A2 B : Type) :
  Equivalence (@f_eq2 A1 A2 B).
Proof.
  intros. split.
  - apply f_eq2_refl.
  - apply f_eq2_symm.
  - apply f_eq2_trans.
Qed.


Definition f_eq3 {A1 A2 A3 B : Type} (f g : A1 -> A2 -> A3 -> B) : Prop :=
  forall x y z, f x y z = g x y z.

#[export] Instance f_eq3_refl (A1 A2 A3 B : Type) :
  Reflexive (@f_eq3 A1 A2 A3 B).
Proof.
  unfold Reflexive, f_eq3.
  intros. reflexivity.
Qed.
#[export] Instance f_eq3_symm (A1 A2 A3 B : Type) :
  Symmetric (@f_eq3 A1 A2 A3 B).
Proof.
  unfold Symmetric, f_eq3.
  intros. symmetry. apply H.
Qed.
#[export] Instance f_eq3_trans (A1 A2 A3 B : Type) :
  Transitive (@f_eq3 A1 A2 A3 B).
Proof.
  unfold Transitive, f_eq3.
  intros f g h. intros. transitivity (g x y z); auto.
Qed.
#[export] Instance f_eq3_equiv (A1 A2 A3 B : Type) :
  Equivalence (@f_eq3 A1 A2 A3 B).
Proof.
  intros. split.
  - apply f_eq3_refl.
  - apply f_eq3_symm.
  - apply f_eq3_trans.
Qed.
