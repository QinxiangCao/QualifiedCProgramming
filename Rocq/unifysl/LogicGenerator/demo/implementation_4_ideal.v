Require Import ZArith.

Module NaiveLang.
  Definition expr := (nat -> option Z) -> Prop.
  Definition context := expr -> Prop.
  Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
  Definition orp  (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
  Definition falsep : expr := fun st => False.
  Definition truep : expr := fun st => True.

  Definition join : (nat -> option Z) -> (nat -> option Z) -> (nat -> option Z) -> Prop :=
    fun x y z =>
      forall p: nat,
       (exists v, x p = Some v /\ y p = None /\ z p = Some v) \/
       (exists v, x p = None /\ y p = Some v /\ z p = Some v) \/
       (x p = None /\ y p = None /\ z p = None).
  Definition sepcon (e1 e2 : expr) : expr := fun st =>
    exists st1 st2, join st1 st2 st /\ e1 st1 /\ e2 st2.
  Definition emp : expr := fun st =>
    forall p, st p = None.
  Definition derivable1 (e1 e2 : expr) : Prop := forall st, e1 st -> e2 st.
End NaiveLang.

Require Import interface_4.

Module NaiveRule.
  Include DerivedNames (NaiveLang).
  Axiom derivable1_falsep_sepcon_l : (forall x : expr, derivable1 (sepcon falsep x) falsep) .
  Axiom derivable1_orp_sepcon_l : (forall x y z : expr, derivable1 (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z))) .
  Axiom derivable1_sepcon_emp_l : (forall x : expr, derivable1 (sepcon x emp) x) .
  Axiom derivable1_sepcon_emp_r : (forall x : expr, derivable1 x (sepcon x emp)) .
  Axiom derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Axiom derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Axiom derivable1_truep_intros : (forall x : expr, derivable1 x truep) .
  Axiom derivable1_falsep_elim : (forall x : expr, derivable1 falsep x) .
  Axiom derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) .
  Axiom derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) .
  Axiom derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) .
  Axiom derivable1s_truep_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) .
  Axiom derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) .
  Axiom derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) .

End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
Module Solver := IPSolver NaiveLang.
Import T.
Import Solver.


