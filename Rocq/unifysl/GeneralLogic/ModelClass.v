Require Import Coq.Classes.Morphisms.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.

#[export] Instance proper_strongly_complete
         {L: Language}
         {GammaD: Derivable L}
         {MD: Model}
         {SM: Semantics L MD}:
  Proper (Same_set _ ==> iff) (strongly_complete GammaD SM).
Proof.
  hnf; intros MC1 MC2 ?.
  unfold strongly_complete.
  apply Morphisms_Prop.all_iff_morphism.
  intro Phi.
  apply Morphisms_Prop.all_iff_morphism.
  intro x.
  apply Morphisms_Prop.iff_iff_iff_impl_morphism; [| reflexivity].
  unfold consequence.
  rewrite Same_set_spec in H; hnf in H.
  firstorder.
Qed.

#[export] Instance proper_weakly_complete
         {L: Language}
         {GammaP: Provable L}
         {MD: Model}
         {SM: Semantics L MD}:
  Proper (Same_set _ ==> iff) (weakly_complete GammaP SM).
Proof.
  hnf; intros MC1 MC2 ?.
  unfold weakly_complete.
  apply Morphisms_Prop.all_iff_morphism.
  intro x.
  apply Morphisms_Prop.iff_iff_iff_impl_morphism; [| reflexivity].
  unfold valid.
  rewrite Same_set_spec in H; hnf in H.
  firstorder.
Qed.

#[export] Instance proper_KripkeModelClass
         {MD: Model}
         {kMD: KripkeModel MD}:
  Proper (Same_set _ ==> Same_set _) (KripkeModelClass MD).
Proof.
  hnf; intros.
  rewrite Same_set_spec in H |- *.
  hnf in H |- *.
  intros; split; intros; inversion H0; constructor; subst; firstorder.
Qed.

Lemma KripkeModelClass_ModelClass_Same_set_spec
      {MD: Model}
      {kMD: KripkeModel MD}:
  forall MC kMC,
    (forall m: model, MC m <-> exists M w, kMC M /\ m = build_model M w) ->
    Same_set _ MC (KripkeModelClass _ kMC).
Proof.
  intros.
  rewrite Same_set_spec.
  hnf; intros m; split; intros.
  + rewrite H in H0.
    destruct H0 as [M [w [? ?]]].
    subst m.
    constructor.
    auto.
  + inversion H0; subst.
    rewrite H.
    eauto.
Qed.
