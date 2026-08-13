Require Import ZArith.
Require Import Ensembles.

Module NaiveLang.
  Definition expr := (nat -> Z) -> Prop.
  Definition context := expr -> Prop.
  Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
  Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
  Definition orp  (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
  Definition falsep : expr := fun st => False.

  Definition derivable (Phi: context) (e : expr) : Prop := forall st, (forall e0, Phi e0 -> e0 st) -> e st.
End NaiveLang.

Require Import interface_3.

Module NaiveRule.
  Include DerivedNames (NaiveLang).
  Axiom derivables_andp_intros : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi y -> derivable Phi (andp x y)) .
  Axiom derivables_andp_elim1 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi x) .
  Axiom derivables_andp_elim2 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi y) .
  Axiom derivables_orp_intros1 : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (orp x y)) .
  Axiom derivables_orp_intros2 : (forall (Phi : context) (x y : expr), derivable Phi y -> derivable Phi (orp x y)) .
  Axiom derivables_orp_elim : (forall (Phi : Ensemble expr) (x y z : expr), derivable (Union expr Phi (Singleton expr x)) z -> derivable (Union expr Phi (Singleton expr y)) z -> derivable (Union expr Phi (Singleton expr (orp x y))) z) .
  Axiom derivables_falsep_elim : (forall (Phi : context) (x : expr), derivable Phi falsep -> derivable Phi x) .
  Axiom derivables_modus_ponens : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (impp x y) -> derivable Phi y) .
  Axiom derivables_impp_intros : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y -> derivable Phi (impp x y)) .
  Axiom deduction_weaken : (forall (Phi Psi : Ensemble expr) (x : expr), Included expr Phi Psi -> derivable Phi x -> derivable Psi x) .
  Axiom derivable_assum : (forall (Phi : Ensemble expr) (x : expr), In expr Phi x -> derivable Phi x) .
  Axiom deduction_subst : (forall (Phi Psi : context) (y : expr), (forall x : expr, Psi x -> derivable Phi x) -> derivable (Union expr Phi Psi) y -> derivable Phi y) .
End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
(* Module Solver := IPSolver NaiveLang. *)
Import T.
(* Import Solver. *)


