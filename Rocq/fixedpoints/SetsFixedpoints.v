
(*************************************************************)
(* This file defines fixedpoints and its properties on sets, *)
(* leveraging the general proof for BW and KT fixedpoints.   *)
(*************************************************************)


From SetsClass Require Import SetsClass.
From FP Require Import AllFramework.
Import SetsNotation.

Local Open Scope sets.

Section PRECLUDE.
  Context {A} {_SETS_A: Sets.SETS A} {_SETS_Properties_A: SETS_Properties A}.

  Definition lower_than_fx (F:A->A): A -> Prop :=
    fun x => x ⊆ (F x).

  Definition sseq_mono (T: nat -> A) := forall n, T n ⊆ T (S n).

  Definition sfixpoint (f: A -> A) (x0: A): Prop :=
    x0 == f x0.  

  Lemma sseq_mono_nat_le: forall (T: nat -> A),
    sseq_mono T -> forall n m, n <= m -> (T n) ⊆ (T m).
  Proof. apply seq_mono_nat_le. Qed.

  Definition sseq_continuous {B} {_SETS_B: Sets.SETS B} (f: A -> B):=
  forall T: nat -> A, sseq_mono T ->
    (f (⋃ T)) == (⋃ (fun n => f (T n))).

End PRECLUDE.


Section LfixPOINT.
  Context {A} {_SETS_A: Sets.SETS A} {_SETS_Properties_A: SETS_Properties A}.

  Definition Lfix (f: A -> A):= Sets.indexed_union (fun n => Nat.iter n f Sets.empty).

  (** changed to the current definition, the speed of VComp seems slower. *)

  Theorem Lfix_fixpoint: forall f,
    Proper (Sets.included ==> Sets.included) f ->
    sseq_continuous f -> Lfix f == f (Lfix f).
Proof. intros. pose proof @BourbakiWitt_fixpoint A
  PO_sets.R_sets PO_sets.Equiv_sets
  CPO_sets.oLub_sets CPO_sets.Bot_sets
  Sets_equiv_equiv CPO_sets.CPO_sets as BF. apply BF;auto.
Qed.

  Theorem Lfix_least_fixpoint: forall f x0,
  Proper (Sets.included ==> Sets.included) f ->
  sseq_continuous f -> sfixpoint f x0 ->
  Lfix f ⊆ x0.
Proof. intros; pose proof @BourbakiWitt_least_fixpoint A 
  PO_sets.R_sets PO_sets.Equiv_sets
  CPO_sets.oLub_sets CPO_sets.Bot_sets
  Sets_equiv_equiv CPO_sets.CPO_sets as BL.
  apply BL;tauto.
Qed.

  Theorem Lfix_fixpoint_relax: forall f g,
    Proper (Sets.included ==> Sets.included) f ->
    Proper (Sets.included ==> Sets.included) g ->
    sseq_continuous f -> sseq_continuous g ->
    (forall a b, a ⊆ b -> a ⊆ (f a) -> (f a) ⊆ (g b)) ->
    (forall b, (forall a, a ⊆ b -> (f a) ⊆ b) ->
       (forall a, a ⊆ b -> (g a) ⊆ b)) ->
    (Lfix f) == (Lfix g).
Proof. intros. pose proof @BourbakiWitt_fixpoint_relax A
  PO_sets.R_sets PO_sets.Equiv_sets
  CPO_sets.oLub_sets CPO_sets.Bot_sets
  Sets_equiv_equiv CPO_sets.CPO_sets as BR.
  apply BR;auto.
Qed.

End LfixPOINT.

Section KT_FIXPOINT.
  Context {A} {_SETS_A: Sets.SETS A} {_SETS_Properties_A: SETS_Properties A}.

  Definition Gfix f:= Sets.general_union (lower_than_fx f).

  Lemma Gfix_fixpoint_theorem_g: forall f,
    Proper (Sets.included ==> Sets.included) f ->
    (Gfix f) == (f (Gfix f)).
Proof.
  intros. pose proof @KnasterTarski_fixpoint_theorem_g A
  PO_sets.R_sets PO_sets.Equiv_sets
  CL_sets.Lub_sets CL_sets.Glb_sets CL_sets.CL_sets as KF.
  apply KF;tauto.
Qed.

Lemma Gfix_greatest_fixpoint: forall f x,
  Proper (Sets.included ==> Sets.included) f ->
  x == (f x) ->
  x ⊆ (Gfix f).
Proof. intros. pose proof @KnasterTarski_fixpoint_greatest_fixpoint A
  PO_sets.R_sets PO_sets.Equiv_sets
  CL_sets.Lub_sets CL_sets.Glb_sets Sets_equiv_equiv CL_sets.CL_sets as KG.
  apply KG;auto.
Qed.

End KT_FIXPOINT.

Local Existing Instance ListConn.list_ACC.

Definition rconcat {A B C T V}
  (X: A -> list T -> B -> Prop)
  (Y: V -> B -> list T -> C -> Prop):=
  fun v => X ∘ (Y v).

Notation "X '•' Y" := (rconcat X Y)
  (right associativity, at level 12): sets_scope.

#[export] Instance rconcat_mono {A T V}:
  Proper (Sets.included ==> Sets.included ==> Sets.included)
    (@rconcat A A A T V).
Proof.
  unfold Proper, respectful, rconcat;intros.
  intros v. rewrite H, (H0 v). reflexivity.
Qed.

(** interface for VComp *)

Arguments Lfix: simpl never.
Arguments Gfix: simpl never.

(************************************************)
(* General porperties about fixedpoints on sets *)
(************************************************)

Section SETS_FIXPOINT_PROP.
Context {A} {_SETS_A: Sets.SETS A} {_SETS_Properties_A: SETS_Properties A}.

Lemma Lfix_mono:
  forall (F G: A -> A) (Fmono: Proper (Sets.included ==> Sets.included) F),
  (forall a, F a ⊆ G a) ->
  Lfix F ⊆ Lfix G.
Proof. intros. pose proof @BourbakiWitt_fixpoint_mono' A
  PO_sets.R_sets PO_sets.Equiv_sets
  CPO_sets.oLub_sets CPO_sets.Bot_sets
  Sets_equiv_equiv CPO_sets.CPOs_sets as BM.
  apply BM;auto.
Qed.

(** orginal proofs seem no need for Fcongr *)
Lemma Lfix_congr:
  forall (F G: A -> A) (Fcongr: Proper (Sets.equiv ==> Sets.equiv) F),
  (forall a, F a == G a) ->
  Lfix F == Lfix G.
Proof. intros. pose proof @BourbakiWitt_fixpoint_congr' A
  PO_sets.R_sets PO_sets.Equiv_sets
  CPO_sets.oLub_sets CPO_sets.Bot_sets
  Sets_equiv_equiv CPO_sets.CPOs_sets as BC.
  apply BC;auto.
Qed.

Lemma Lfix_mono_weak:
  forall (F G: A -> A) (Fmono: Proper (Sets.included ==> Sets.included) F),
  (forall a b, a ⊆ b -> F a ⊆ G b) ->
  Lfix F ⊆ Lfix G.
Proof. intros. apply Lfix_mono;auto. intros; apply H. reflexivity. Qed.

Lemma Lfix_congr_weak:
  forall (F G: A -> A),
  (forall a b, a == b -> F a == G b) ->
  Lfix F == Lfix G.
Proof. intros. pose proof @BourbakiWitt_fixpoint_congr A
  PO_sets.R_sets PO_sets.Equiv_sets
  CPO_sets.oLub_sets CPO_sets.Bot_sets
  Sets_equiv_equiv CPO_sets.CPOs_sets as BC.
  apply BC;auto.
Qed.

Lemma Gfix_mono:
  forall (F G: A -> A),
   (forall x, F x ⊆ G x) -> Gfix F ⊆ Gfix G.
Proof.
  intros. pose proof @KT_fix_g_mono A
  PO_sets.R_sets PO_sets.Equiv_sets
  CL_sets.Lub_sets CL_sets.Glb_sets Sets_equiv_equiv CL_sets.CL_sets as KG.
  apply KG;auto.
Qed.

Lemma Gfix_congr:
  forall (F G: A -> A), (forall x, F x == G x) ->
  Gfix F == Gfix G.
Proof.
  intros. pose proof @KT_fix_g_congr A
  PO_sets.R_sets PO_sets.Equiv_sets
  CL_sets.Lub_sets CL_sets.Glb_sets Sets_equiv_equiv CL_sets.CL_sets as KG.
  apply KG;auto.
Qed.

End SETS_FIXPOINT_PROP.