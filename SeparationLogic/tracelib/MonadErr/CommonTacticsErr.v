From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare.
From FP Require Import BourbakiWitt.
Require Import Coq.Lists.List.

Import MonadNotation.
Local Open Scope monad.

Ltac my_destruct H :=
  match type of H with
  | exists (_ : ?A), _ => destruct H as [? H]; my_destruct H
  | _ /\ _ =>
      let H0 := fresh "H" in
      destruct H as [H H0];
      my_destruct H;
      my_destruct H0
  | _ \/ _ => destruct H as [H | H]; my_destruct H
  | _ => (discriminate || contradiction || idtac)
  end.

Lemma Hoare_false {Σ A: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    Hoare (fun _ => False) c Q.
Proof.
  unfold Hoare; intros; split; intros; tauto.
Qed.

Tactic Notation "hoare_cons_pre" uconstr(H) :=
  eapply Hoare_cons_pre; [| apply H]; simpl; try tauto.

Tactic Notation "hoare_cons_post" uconstr(H) :=
  eapply Hoare_cons_post; [| apply H]; simpl; try tauto.

Tactic Notation "hoare_cons" uconstr(H) :=
  eapply Hoare_cons_pre; [|eapply Hoare_cons_post; [| apply H] ]; simpl; try tauto.

Ltac hoare_fix_lv_auto_conj' A C c :=
  lazymatch goal with
  | |- @Hoare ?Sigma ?R ?P (Rec ?F ?a) ?Q =>
    unfold Rec; hoare_fix_lv_auto_conj' A C c
  | |- @Hoare ?Σ ?R ?P (BW_fix ?F ?a) ?Q =>
    let P1 := fresh "P" in evar (P1: A -> C -> Σ -> Prop);
    let Q1 := fresh "Q" in evar (Q1: A -> C -> R -> Σ -> Prop);
    let h := fresh "h" in assert (P1 = P1) as h;[
      let P0 := eval pattern (c) in P in
      match P0 with
      | ?P0' _ =>
        let P' := eval pattern (a) in P0' in
        match P' with
        | ?P'' _ => exact (Logic.eq_refl P'')
        end
      end|];
    clear h;
    let h := fresh "h" in assert (Q1 = Q1) as h;[
      let Q0 := eval pattern (c) in Q in
      match Q0 with
      | ?Q0' _ =>
        let Q' := eval pattern (a) in Q0' in
        match Q' with
        | ?Q'' _ => exact (Logic.eq_refl Q'')
        end
      end|];
    clear h;
    eapply (Hoare_BW_fix_logicv_conj' _ P1 Q1 a c);
    subst P1 Q1
  end.
