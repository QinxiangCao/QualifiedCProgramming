Require Export Coq.Classes.EquivDec.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Numbers.BinNums.
Set Warnings "-warn-library-file-stdlib-vector".
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.

Require Import AUXLib.Idents.

Lemma equiv_decb_true_eq {A: Type} {eqd: EqDec A eq} (x y: A) : equiv_decb x y = true -> x = y.
Proof.
  unfold equiv_decb, equiv_dec.
  destruct (eqd x y) as [Heq | Hneq]; [|congruence].
  intros _. exact Heq.
Defined.

Lemma eq_equiv_decb_true {A: Type} {eqd: EqDec A eq} (x y: A) : x = y -> equiv_decb x y = true.
Proof.
  intros Heq. unfold equiv_decb, equiv_dec.
  destruct (eqd x y) as [Heq' | Hneq]; [|congruence]. reflexivity.
Defined.


Lemma equiv_decb_false_neq {A: Type} {eqd: EqDec A eq} (x y: A) : equiv_decb x y = false -> x <> y.
Proof.
  unfold equiv_decb, equiv_dec.
  destruct (eqd x y) as [Heq | Hneq]; congruence.
Defined.

Lemma neq_equiv_decb_false {A: Type} {eqd: EqDec A eq} (x y: A) : x <> y -> equiv_decb x y = false.
Proof.
  intros Hneq. unfold equiv_decb, equiv_dec.
  destruct (eqd x y) as [Heq | Hneq']; congruence.
Defined.

#[export] Instance option_eqdec {A: Type} {eqd: EqDec A eq} : EqDec (option A) eq.
refine (fun x y => match x, y with
  | Some x, Some y => match eqd x y with
    | left pf => left (f_equal Some pf)
    | right _ => right _
    end
  | None, None => left eq_refl
  | _, _ => right _
end); congruence.
Defined.

#[export] Instance Z_eqdec : EqDec Z eq := Z.eq_dec.

#[export] Instance Pos_eqdec : EqDec positive eq := Pos.eq_dec.

#[export] Instance ident_eqdec : EqDec ident eq := Pos.eq_dec.

(* #[export] Instance fin_eqdec {n: nat} : EqDec (Fin.t n) eq := Fin.eq_dec. *)

(* The eq_dec for [Fin.t] in the standard library is opaque.
   We need to define our own. *)
#[export] Instance fin_eqdec {n: nat} : EqDec (Fin.t n) eq.
  refine ((fix fin_eqdec {n} (x: Fin.t n) (y: Fin.t n) {struct x}
      : {x = y} + {x <> y} := _) n).
  (* subst n'. cbn. *)
  destruct x as [|? x'].
  - apply (Fin.caseS' y).
    + left. reflexivity.
    + intros. right. congruence.
  - apply (Fin.caseS' y).
    + intros. right. congruence.
    + intros y'. destruct (fin_eqdec n x' y') as [|ne].
      * left. f_equal. assumption.
      * right. intro. apply ne. apply Fin.FS_inj. auto.
Defined.

#[export] Instance vector_eqdec {A: Type} {eqd: EqDec A eq} {n: nat} : EqDec (Vector.t A n) eq.
  refine (Vector.eq_dec A equiv_decb _ n).
  intros x y. cbv. destruct (eqd x y); cbv in *; split; auto.
  inversion 1.
Defined.



(************************************************************************)
(** * Prove the Hedberg's theorem: Streicher's K holds on decidable types *)
(** The following proof is modified from the one in Coq's library
    (Logic/Eqdep_dec.v). The only change is to replace [Prop] with [Type]. *)

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

Section EqdepDec.

  Variable A : Type.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_rect _ (fun a => a = y') eq2 _ eq1.

  Remark trans_sym_eq (x y:A) (u:x = y) : comp u u = eq_refl y.
  Proof.
    case u; trivial.
  Defined.

  Variable x : A.

  Variable eq_dec : forall y : A, {x = y} + {x <> y}.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec y with
      | left eqxy => eqxy
      | right neqxy => False_ind _ (neqxy u)
    end.

  Let nu_constant (y:A) (u v:x = y) : nu u = nu v.
    unfold nu.
    destruct (eq_dec y) as [Heq|Hneq].
    - reflexivity.

    - case Hneq; trivial.
  Defined.


  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (eq_refl x)) v.


  Remark nu_left_inv_on (y:A) (u:x = y) : nu_inv (nu u) = u.
  Proof.
    case u; unfold nu_inv.
    apply trans_sym_eq.
  Defined.


  Theorem eq_proofs_unicity_on (y:A) (p1 p2:x = y) : p1 = p2.
  Proof.
    elim (nu_left_inv_on p1).
    elim (nu_left_inv_on p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Defined.

  Theorem K_dec_on (P:x = x -> Type) (H:P (eq_refl x)) (p:x = x) : P p.
  Proof.
    elim eq_proofs_unicity_on with x (eq_refl x) p.
    trivial.
  Defined.

End EqdepDec.


Theorem UIP_eqdec {A: Type} {eqd: EqDec A eq} (x y: A) (p1: x = y) (p2: x = y) :
  p1 = p2.
Proof. exact (eq_proofs_unicity_on (eqd x) p1 p2). Defined.

Lemma equiv_dec_refl {A: Type} {eqd: EqDec A eq} (x: A) :
  equiv_dec x x = left eq_refl.
Proof.
  unfold equiv_dec. destruct (eqd x x) as [e|ne].
  2: exfalso; apply (ne eq_refl).
  cbv in e. revert e. apply K_dec_on; auto.
  apply (eqd x).
Qed. 

(* Injectivity of dependent pair *)
Lemma inj_pair2_eqdec {A: Type} {eqd: EqDec A eq} {P: A -> Type} {p: A} {x y: P p}:
  existT P p x = existT P p y -> x = y.
Proof.
  intros H.
  pose (projT2_eq H). simpl in e.
  set (projT1_eq H) as Heq in e. simpl in Heq.
  cbv in eqd.
  refine (K_dec_on (eqd p) (fun Heq => eq_rect p P x p Heq = y -> x = y) _ Heq e).
  simpl. exact (fun x => x).
Defined.
