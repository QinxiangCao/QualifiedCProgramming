Require Import Setoid.
Require Import RelationClasses.
Require Import Morphisms.

Module TEST1.

Parameter P : nat -> Prop.
Parameter IFF : nat -> nat -> nat.

Instance provable_iffp_rewrite: RewriteRelation (fun x y => P (IFF x y)).
Qed.

Instance provable_iffp_provable: Proper ((fun x y => P (IFF x y)) ==> iff) P.
Proof.
Admitted.

Goal forall x y, P (IFF x y) -> P x -> P y.
  intros.
  rewrite H in H0.
  auto.
Qed.

End TEST1.


Module TEST2.

Class para: Type := {X : Type }.

Parameter P : forall `{para}, X -> Prop.
Parameter IFF : forall `{para}, X -> X -> X.
Section TEST2.
Context `{para}.

Instance provable_iffp_rewrite: RewriteRelation (fun x y => P (IFF x y)).
Qed.

Instance provable_iffp_provable: Proper ((fun x y => P (IFF x y)) ==> iff) P.
Proof.
Admitted.

Goal forall x y, P (IFF x y) -> P x -> P y.
  intros.
  Fail rewrite H in H0.
Abort.

End TEST2.

