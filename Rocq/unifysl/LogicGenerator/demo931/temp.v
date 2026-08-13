Require Import Logic.LogicGenerator.demo931.impl1.
Import T.

(*
1. coqprop P1 && coqprop P2 && ... coqprop Px && P 
  |-- coqprop Q1 && coqprop Q2 && ... coqprop Qx && Q
2. coqprop P1 && coqprop P2 && ... coqprop Px && P |-- Q
3. P |-- coqprop Q1 && coqprop Q2 && ... coqprop Qx && Q
*)

(*
(coq_prop P) && Q |-- (coq_prop P') && Q'
<== P -> (Q |-- (coq_prop P') && Q')
<== (P -> P') /\ (P -> (Q |-- Q'))
*)

Lemma cp_lem1 : forall (P :Prop) (Q Q' : expr),
  (P -> (derivable1 Q Q'))
  -> (derivable1 (andp (coq_prop P) Q) Q').
Proof.
  intros. hnf. intros.
  unfold impp, andp, coq_prop.
  unfold derivable1, provable, impp in H.
  intros. apply H; try tauto.
Qed.

Lemma cp_lem2 : forall (P P' : Prop) (Q Q' : expr),
  (P -> P') -> (P -> (derivable1 Q Q')) ->
  (P -> (derivable1 Q (andp (coq_prop P') Q'))).
Proof.
  intros.
  unfold derivable1, andp, coq_prop, provable, impp in *.
  intros. split; try tauto.
  apply H0; try tauto.
Qed.

Ltac pop_coq_prop :=
  repeat match goal with
  | |- derivable1 (andp (coq_prop ?P) _) _ => apply cp_lem1
  | |- (_ -> (derivable1 _ (andp (coq_prop ?P') _))) => apply cp_lem2
  | _ => idtac
  end.

Context {P : Prop} {P' : Prop} {Q : expr} {Q' : expr}.

Goal derivable1 (andp (coq_prop P) Q) Q'.
Proof. pop_coq_prop. Abort.

Goal (P -> (derivable1 Q (andp (coq_prop P') Q'))).
Proof. pop_coq_prop. Abort.

Goal (derivable1 (andp (coq_prop P) Q) (andp (coq_prop P') Q')).
Proof. pop_coq_prop. Abort.

(* Ltac entailer :=
  match goal with
  | |- _ |-- _ => idtac
  | _ => fail "The proof goal's conclusion is not an assertion derivation."
  end;
  assert_simpl;
  apply FOL_complete;
  let st := fresh "st" in
  intros st;
  cbv [Assertion_denote term_denote];
  repeat
    match goal with
    | |- context [aexp_denote st (Concrete_Pretty_Printing.AId ?X)] =>
           let X' := fresh X "'" in
           set (X' := aexp_denote st (Concrete_Pretty_Printing.AId X));
           clearbody X';
           revert X'
    end;
  first [ clear st | fail 1 "This is not a concrete derivation." ]. *)






(* Lemma lem1 : (P -> (derivable1 Q (andp (coq_prop P') Q')))
  -> (derivable1 (andp (coq_prop P) Q) (andp (coq_prop P') Q')).
Admitted.

Lemma lem2 : ((P -> P') /\ (P -> (derivable1 Q Q')))
  -> (P -> (derivable1 Q (andp (coq_prop P') Q'))).
Admitted.

Theorem thm : ((P -> P') /\ (P -> (derivable1 Q Q')))
  -> (derivable1 (andp (coq_prop P) Q) (andp (coq_prop P') Q')). *)
