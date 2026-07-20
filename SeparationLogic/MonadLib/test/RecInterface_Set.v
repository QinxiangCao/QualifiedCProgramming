From SetsClass Require Import SetsClass.
From FP Require Import SetsFixedpoints.
From MonadLib.SetMonad Require Import SetMonad.

Import SetsNotation Monad MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section RecInterface.

Definition rec_body (W: nat -> program nat) (n: nat): program nat :=
  choice (ret n) (W n).

Lemma rec_body_mono_cont: mono_cont rec_body.
Proof. unfold rec_body; mono_cont_auto. Qed.

Lemma rec_unfold_test:
  Rec rec_body == rec_body (Rec rec_body).
Proof. apply Rec_unfold, rec_body_mono_cont. Qed.

Goal mono_cont (fun W: nat -> program nat => W).
Proof. mono_cont_auto. Qed.

Goal mono_cont (fun W: nat -> program nat => (ret 0: program nat)).
Proof. mono_cont_auto. Qed.

Goal mono_cont (fun W: nat -> program nat => W 0).
Proof. mono_cont_auto. Qed.

Goal mono_cont (fun W: nat -> program nat =>
  x <- W 0;; W x).
Proof. mono_cont_auto. Qed.

Goal mono_cont (fun W: nat -> program nat =>
  choice (W 0) (W 1)).
Proof. mono_cont_auto. Qed.

Goal mono_cont (fun W: nat -> program nat =>
  match true with true => W 0 | false => ret 0 end).
Proof. mono_cont_auto. Qed.

Definition nested_rec (W: nat -> program nat): nat -> program nat :=
  Rec (fun R n => choice (W n) (R n)).

Lemma nested_rec_mono_cont: mono_cont nested_rec.
Proof. unfold nested_rec; mono_cont_auto. Qed.

Lemma unfold_rec_goal_test:
  Rec rec_body == rec_body (Rec rec_body).
Proof. unfold_rec. reflexivity. Qed.

Lemma unfold_rec_hyp_test (X: nat -> program nat):
  Rec rec_body == X -> rec_body (Rec rec_body) == X.
Proof. intro H. unfold_rec in H. exact H. Qed.


Definition hoare_body (_: nat -> program nat) (n: nat): program nat := ret n.

Lemma Hoare_Rec_test (n: nat):
  Hoare (Rec hoare_body n) (fun r => r = n).
Proof.
  hoare_rec (fun _ => True) (fun n r => r = n).
  - intros W HW a _. unfold hoare_body. apply Hoare_ret. reflexivity.
  - exact I.
Qed.

End RecInterface.
