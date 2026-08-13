Require Import ZArith.

Definition var := nat.

Inductive expr: Type :=
  | impp : expr -> expr -> expr
  | varp : var -> expr.

Declare Scope syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Local Open Scope syntax.

Inductive provable: expr -> Prop :=
| provables_modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| provable_axiom1: forall x y, provable (x --> (y --> x))
| provable_axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z)).

Module NaiveLang.
  Definition expr := expr.
  Definition impp := impp.
  Definition provable := provable.
End NaiveLang.

Require Import interface_2.

Module NaiveRule.
  Include DerivedNames (NaiveLang).
  Lemma provables_modus_ponens :
    forall x y : expr, provable (impp x y) -> provable x -> provable y.
  Proof. intros. eapply provables_modus_ponens; eauto. Qed.

  Lemma provable_axiom1 : forall x y : expr, provable (impp x (impp y x)).
  Proof. exact provable_axiom1. Qed.

  Lemma provable_axiom2 : forall x y z : expr,
      provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z))).
  Proof. exact provable_axiom2. Qed.

End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
Module Solver := IPSolver NaiveLang.
Import T.
Import Solver.

