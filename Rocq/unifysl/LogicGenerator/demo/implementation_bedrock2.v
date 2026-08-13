Require Import coqutil.Map.Interface.
Require Import bedrock2.Semantics.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.FE310CSemantics.
Require Import ZArith.
Require Import exportLogic.interface.


Module NaiveLang <: LanguageSig.
  Definition expr `{parameters} := mem -> Prop.
  Section NaiveLang.
  Context {p: parameters}.
  Definition impp (e1 e2 : mem -> Prop) : mem -> Prop := fun st => e1 st -> e2 st.
  Definition andp (e1 e2 : mem -> Prop) : mem -> Prop := fun st => e1 st /\ e2 st.
  Definition emp: mem -> Prop := bedrock2.Map.Separation.emp True.
  Definition sepcon := @bedrock2.Map.Separation.sep
          (@Interface.word.rep (@width (@semantics_parameters p))
             (@word (@semantics_parameters p)))
          (@Interface.word.rep (Zpos (xO (xO (xO xH))))
             (@byte (@semantics_parameters p))) (@mem (@semantics_parameters p)).
  Definition provable (e : mem -> Prop) := forall st, e st.
  End NaiveLang.
End NaiveLang.

Module NaiveRule.
  Include DerivedNames (NaiveLang).
  Section NaiveRule.
  Context `{parameters}.

  Lemma provables_modus_ponens :
    forall x y : expr, provable (impp x y) -> provable x -> provable y.
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_axiom1 : forall x y : expr, provable (impp x (impp y x)).
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_axiom2 : forall x y z : expr,
      provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z))).
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_andp_intros :
    forall x y : expr, provable (impp x (impp y (andp x y))).
  Proof. unfold provable, impp, andp. auto. Qed.

  Lemma provable_andp_elim1 : forall x y : expr, provable (impp (andp x y) x).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma provable_andp_elim2 : forall x y : expr, provable (impp (andp x y) y).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma provable_sepcon_impp_comm: forall x y, provable (iffp (sepcon x y) (sepcon y x)).
  Proof.
    intros.
    pose proof sep_comm x y.
    exact H0.
  Qed.
  
  Lemma provable_sepcon_assoc: forall x y z,
    provable (iffp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)).
  Proof.
    intros.
    pose proof sep_assoc x y z.
    hnf; intros.
    specialize (H0 st).
    unfold iffp, andp, impp.
    tauto.
  Qed.
    
  Lemma provable_sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Proof.
    intros.
    apply Proper_sep_impl1; auto.
  Qed.
  
  Lemma provable_sepcon_emp : (forall x : expr, provable (iffp (sepcon x emp) x)) .
  Proof.
    intros.
    apply sep_emp_True_r.
  Qed.
  
  End NaiveRule.
End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
Import T.


