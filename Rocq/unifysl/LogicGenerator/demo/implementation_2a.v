Require Import ZArith.

Module NaiveLang.
  Definition expr := (nat -> Z) -> Prop.
  Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.

  Definition provable (e : expr) : Prop := forall st, e st.
End NaiveLang.

Require Import interface_2.

Module NaiveRule.
  Include DerivedNames (NaiveLang).
  Lemma provables_modus_ponens :
    forall x y : expr, provable (impp x y) -> provable x -> provable y.
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_axiom1 : forall x y : expr, provable (impp x (impp y x)).
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_axiom2 : forall x y z : expr,
      provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z))).
  Proof. unfold provable, impp. auto. Qed.

End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
Module Solver := IPSolver NaiveLang.
Import T.
Import Solver.


