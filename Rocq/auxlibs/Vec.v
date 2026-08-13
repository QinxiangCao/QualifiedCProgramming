(* Reference: https://gitlab.mpi-sws.org/iris/stdpp/-/blob/6e560df6564ceefda86ddfae12368c1ba3711ef5/stdpp/vector.v *)
(* Notations for Coq.Vectors.Vector from stdpp. *)

(** This file collects general purpose definitions and theorems on vectors
(lists of fixed length). It uses the definitions from the standard library, but
renames or changes their notations, so that it becomes more consistent with the
naming conventions in this development. *)
(* From stdpp Require Import countable.
From stdpp Require Export fin list.
From stdpp Require Import options. *)

Require Import Bool.
Set Warnings "-warn-library-file-stdlib-vector".
From Coq.Vectors Require Import Vector.
Global Open Scope vector_scope.

(** The type [vec n] represents lists of consisting of exactly [n] elements.
Whereas the standard library declares exactly the same notations for vectors as
used for lists, we use slightly different notations so it becomes easier to use
lists and vectors together. *)
Notation vec := Vector.t.
Notation vnil := Vector.nil.
Global Arguments vnil {_}.
Notation vcons := Vector.cons.
Notation vapp := Vector.append.
Global Arguments vcons {_} _ {_} _.
Notation vmap := Vector.map.

Infix ":::" := vcons (at level 60, right associativity) : vector_scope.
Notation "(:::)" := vcons (only parsing) : vector_scope.
Notation "( x :::.)" := (vcons x) (only parsing) : vector_scope.
Notation "(.::: v )" := (fun x => vcons x v) (only parsing) : vector_scope.
Notation "[# ] " := vnil : vector_scope.
Notation "[# x ] " := (vcons x vnil) : vector_scope.
Notation "[# x ; .. ; y ] " := (vcons x .. (vcons y vnil) ..) : vector_scope.
Infix "+++" := vapp (at level 60, right associativity) : vector_scope.
Notation "(+++)" := vapp (only parsing) : vector_scope.
Notation "( v +++.)" := (vapp v) (only parsing) : vector_scope.
Notation "(.+++ w )" := (fun v => vapp v w) (only parsing) : vector_scope.

(** Similar to [fin], we provide an inversion principle that keeps the length
fixed. We define a tactic [inv_vec v] to perform case analysis on [v], using
this inversion principle. *)
Notation vec_0_inv := Vector.case0.
Definition vec_S_inv {A n} (P : vec A (S n) -> Type)
  (Hcons : forall x v, P (x ::: v)) v : P v.
Proof.
  revert P Hcons.
  refine match v with [#] => tt | x ::: v => fun P Hcons => Hcons x v end.
Defined.

(* Global Instance vector_lookup_total A : forall m, LookupTotal (fin m) A (vec A m) :=
  fix go m i {struct i} := let _ : forall m, LookupTotal _ _ _ := @go in
  match i in fin m return vec A m -> A with
  | 0%fin => vec_S_inv (fun _ => A) (fun x _ => x)
  | FS j => vec_S_inv (fun _ => A) (fun _ v => v !!! j)
  end. *)

(** The tactic [vec_double_ind v1 v2] performs double induction on [v1] and [v2]
provided that they have the same length. *)
Notation vec_rect2 := Vector.rect2.
(* Ltac vec_double_ind v1 v2 :=
  match type of v1 with
  | vec _ ?n =>
    repeat match goal with
    | H' : context [ n ] |- _ => var_neq v1 H'; var_neq v2 H'; revert H'
    end;
    revert n v1 v2;
    match goal with |- forall n v1 v2, @?P n v1 v2 => apply (vec_rect2 P) end
  end. *)

Notation vcons_inj := VectorSpec.cons_inj.
Lemma vcons_inj_1 {A n} x y (v w : vec A n) : x ::: v = y ::: w -> x = y.
Proof. apply vcons_inj. Qed.
Lemma vcons_inj_2 {A n} x y (v w : vec A n) : x ::: v = y ::: w -> v = w.
Proof. apply vcons_inj. Qed.

(* Lemma vec_eq {A n} (v w : vec A n) : (forall i, v !!! i = w !!! i) -> v = w.
Proof.
  vec_double_ind v w; [done|]. intros n v w IH x y Hi. f_equal.
  - apply (Hi 0%fin).
  - apply IH. intros i. apply (Hi (FS i)).
Qed. *)

(* Global Instance vec_dec {A} {dec : EqDecision A} {n} : EqDecision (vec A n).
Proof.
 refine (vec_rect2
  (fun n (v w : vec A n) => { v = w } + { v ≠ w })
  (left _)
  (fun _ _ _ H x y => cast_if_and (dec x y) H));
  f_equal; eauto using vcons_inj_1, vcons_inj_2.
Defined. *)

Ltac inv_vec v :=
  let T := type of v in
  match eval hnf in T with
  | vec _ ?n =>
    match eval hnf in n with
    | 0 => generalize dependent v; match goal with |- forall v, @?P v => apply (vec_0_inv P) end
    | S ?n =>
      generalize dependent v; match goal with |- forall v, @?P v => apply (vec_S_inv P) end;
      (* Try going on recursively. *)
      try (let x := fresh "x" in intros x v; inv_vec v; revert x)
    end
  end.





(* EqDec for vec *)
From AUXLib Require Import EqDec.

#[export] Instance vec_eqdec {A} {dec : EqDec A eq} {n} : EqDec (vec A n) eq.
Proof.
  induction n; hnf; intros x y.
  - inv_vec x; inv_vec y; left; reflexivity.
  - inv_vec x; intros a x. inv_vec y; intros b y.
    destruct (dec a b) as [Hab|Hab].
    2: {
      right; injection 1; intros; apply Hab; auto.
    }
    cbv in Hab. subst b.
    destruct (IHn x y) as [Hxy|Hxy].
    2: {
      right; injection 1; intros.
      apply inj_pair2_eqdec in H0. apply Hxy; auto.
    }
    cbv in Hxy. subst y.
    left. reflexivity.
Defined.


Lemma In_vnil {A} (x : A) :
  In x vnil -> False.
Proof.
  intros H. inversion H.
Qed.

Lemma In_vcons_inv {A n} (a : A) (v : vec A n) x :
  In x (a ::: v) -> x = a \/ In x v.
Proof.
  intros H. inversion H; subst; auto.
  apply inj_pair2_eqdec in H3. subst. right. auto.
Qed.


(** Boolean operations on vectors. *)

Section Bool.
  Context {A : Type} (f : A -> bool).

  Fixpoint vexistsb {n} (l: vec A n) : bool :=
    match l with
    | nil => false
    | a ::: l => f a || vexistsb l
    end.

  Lemma vexistsb_exists :
    forall {n} (l: vec A n), vexistsb l = true <-> exists x, In x l /\ f x = true.
  Proof.
    intros n l; induction l as [|a ? l IH]; split; simpl.
    - congruence.
    - intros [a [H _]]. inversion H.
    - destruct (f a) eqn:Hfa; simpl.
      + intros. exists a; split; auto. left.
      + intros H. apply IH in H. destruct H as [x [Hx Hfx]].
        exists x; split; auto. right; auto.
    - intros [x [Hx Hfx]]. apply In_vcons_inv in Hx.
      destruct Hx as [Hxa | Hxl].
      + subst x. rewrite Hfx; auto.
      + destruct (f a); simpl; auto. apply IH.
        exists x; split; auto.
  Qed.

  Lemma vexistsb_app {n1} (l1: vec A n1) {n2} (l2: vec A n2) :
    vexistsb (l1 +++ l2) = vexistsb l1 || vexistsb l2.
  Proof.
    revert n2 l2; induction l1 as [|a ? l1 IH].
    - intros n2 l2; simpl; auto.
    - intros n2 l2; simpl.
      destruct (f a) eqn:Hfa; simpl; auto.
  Qed.


  Fixpoint vforallb {n} (v : vec A n) : bool :=
    match v with
    | vnil => true
    | x ::: xs => f x && vforallb xs
    end.

  Lemma vforallb_forall :
    forall {n} (l: vec A n), vforallb l = true <-> (forall x, In x l -> f x = true).
  Proof.
    intros n l; induction l as [|a ? l IH]; split; simpl.
    - intros; exfalso; eapply In_vnil; eauto.
    - intros; auto.
    - intros H x Hin. rewrite andb_true_iff in H. destruct H as [Hfa H].
      apply In_vcons_inv in Hin. destruct Hin as [Hxa | Hxl].
      + subst x; auto.
      + apply IH; auto.
    - intros H. apply andb_true_iff. split; auto.
      + apply H. left.
      + apply IH; auto. intros. apply H. right; auto.
  Qed.

  Lemma vforallb_app :
    forall {n1} (l1: vec A n1) {n2} (l2: vec A n2),
      vforallb (l1 +++ l2) = vforallb l1 && vforallb l2.
  Proof.
    intros ? ?. induction l1 as [|a ? l1 IH]; intros n2 l2; simpl.
    - auto.
    - destruct (f a) eqn:Hfa; simpl; auto.
  Qed.


  Fixpoint find {n} (l: vec A n) : option A :=
    match l with
    | vnil => None
    | x ::: tl => if f x then Some x else find tl
    end.

  Lemma find_some {n} (l: vec A n) x : find l = Some x -> In x l /\ f x = true.
  Proof.
    induction l as [|a ? l IH]; simpl; intros Hfind.
    - discriminate Hfind.
    - destruct (f a) eqn:Hfa; simpl in Hfind.
      + injection Hfind as ?; subst. split; auto. left; auto.
      + split.
        * right. apply IH. auto.
        * apply IH. auto.
  Qed.

  Lemma find_none {n} (l: vec A n) : find l = None -> forall x, In x l -> f x = false.
  Proof.
    induction l as [|a ? l IH]; simpl; intros Hfind x Hin.
    - exfalso; eapply In_vnil; eauto.
    - destruct (f a) eqn:Hfa; simpl in Hfind.
      + congruence.
      + apply In_vcons_inv in Hin. destruct Hin as [Hxa | Hxl].
        * subst x. auto.
        * apply IH; auto.
  Qed.

End Bool.


(* Transparent version of Vector.nth_map *)
Lemma nth_map {A B} (f : A -> B) {n} (v : vec A n) (i : Fin.t n) :
  Vector.nth (Vector.map f v) i = f (Vector.nth v i).
Proof.
  induction v as [|a n v IH]; simpl; auto.
  - exfalso. apply (Fin.case0 (fun _ => False) i).
  - revert n i v IH.
    match goal with
    | |- forall n i, @?P n i => apply (Fin.caseS P)
    end; simpl.
    + reflexivity.
    + intros. apply IH.
Defined.
