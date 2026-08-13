Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.

Local Open Scope logic_base.

Class BasicDeduction (L:Language) (Gamma:Derivable1 L) := {
  derivable1_refl: forall x, x |-- x;
  derivable1_trans: forall x y z, x |-- y -> y |-- z -> x |-- z
}.

Section BDRewriteClass.

Context {L:Language}
        {Gamma:Derivable1 L}
        {BD:BasicDeduction L Gamma}.

#[export] Instance Derivable_impp_rewrite: RewriteRelation derivable1.
Qed.

#[export] Instance derivable1_refl_instance: Reflexive derivable1.
Proof.
  hnf; intros.
  apply derivable1_refl.
Qed.

#[export] Instance derivable1_trans_instance: Transitive derivable1.
Proof.
  hnf; intros.
  eapply derivable1_trans; eauto.
Qed.

#[export] Instance derivable1_proper_derivable1:
  Proper ( derivable1 --> derivable1 ==> Basics.impl) derivable1.
Proof.
  hnf;intros.
  hnf;intros.
  unfold Basics.flip in H.
  intro.
  pose proof derivable1_trans _ _ _ H1 H0.
  pose proof derivable1_trans _ _ _ H H2;tauto.
  Qed.

End BDRewriteClass.

#[export] Existing Instances Derivable_impp_rewrite
                             derivable1_refl_instance
                             derivable1_trans_instance
                             derivable1_proper_derivable1.

Module TestRewriteClass.
Section TestRewriteClass.

Goal forall {L: Language} {Gamma:Derivable1 L} {BD:BasicDeduction L Gamma} x1 x2 y1 y2,
  x1 |-- x2 ->
  y1 |-- y2 ->
  x2 |-- y1 -> x1 |-- y2.
Proof.
  intros.
  rewrite <- H0.
  rewrite <- H1.
  auto.
Qed.

End TestRewriteClass.
End TestRewriteClass.

