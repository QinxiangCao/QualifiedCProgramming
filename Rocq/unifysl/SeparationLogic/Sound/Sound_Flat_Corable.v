Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Sound_Flat_Corable.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {sepconL: SepconLanguage L}
        {MD: Model}
        {kMD: KripkeModel MD}
        (M: Kmodel)
        {R: Relation (Kworlds M)}
        {po_R: PreOrder Krelation}
        {J: Join (Kworlds M)}
        {U: Unit (Kworlds M)}
        {SA: SeparationAlgebra (Kworlds M)}
        {dSA: DownwardsClosedSeparationAlgebra (Kworlds M)}
        {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD M SM}
        {kminSM: KripkeMinimumSemantics L MD M SM}
        {andpSM: KripkeAndSemantics L MD M SM}
        {iffpSM: KripkeIffSemantics L MD M SM}
        {coq_prop_SM : CoqPropSemantics L MD M SM}
        {fsepconSM: FlatSemantics.SepconSemantics L MD M SM}.

Lemma sound_corable_preserved:
  forall x y: expr,
    (forall m, KRIPKE: M, m |= x <--> y) ->
    sem_corable (Kdenotation M x) ->
    sem_corable (Kdenotation M y).
Proof.
  unfold Kdenotation.
  intros.
  pose proof valid_iffp _ _ H; clear H.
  unfold satisfies in H1.
  constructor.
  + intros ? ? ?.
    rewrite <- !H1.
    apply (local2global _ H0).
  + intros ? ? ?.
    rewrite <- !H1.
    intros HA HB.
    destruct (global2local _ H0 _ _ _ HA HB) as [w1' [w2' ?H]].
    exists w1', w2'.
    rewrite <- !H1.
    auto.
Qed.

Lemma sound_corable_andp_sepcon1: forall x y z,
  sem_corable (Kdenotation M x) ->
  forall m, KRIPKE: M, m |= (x && y) * z <--> x && (y * z).
Proof.
  intros.
  rewrite sat_iffp.
  intros ? _; clear m; split.
  + intros.
    rewrite sat_andp, sat_sepcon.
    rewrite sat_sepcon in H0.
    destruct H0 as [m1 [m2 [? [? ?]]]].
    rewrite sat_andp in H1.
    destruct H1.
    pose proof local2global _ H _ _ _ H0 H1.
    split; auto.
    exists m1, m2; auto.
  + intros.
    rewrite sat_andp, sat_sepcon in H0.
    destruct H0 as [? [m1 [m2 [? [? ?]]]]].
    pose proof global2local _ H _ _ _ H1 H0 as [m1' [m2' [? [? [? ?]]]]].
    rewrite sat_sepcon; exists m1', m2'.
    split; auto.
    rewrite sat_andp.
    split; [split |]; eapply sat_mono; eauto.
Qed.

Lemma sound_corable_coq_prop: forall P,
  sem_corable (Kdenotation M (!! P)).
Proof.
  intros.
  unfold Kdenotation.
  constructor.
  + change
      (forall w1 w2 w3 : Kworlds M,
         join w1 w2 w3 -> KRIPKE: M, w1 |= !! P -> KRIPKE: M, w3 |= !! P).
    intros.
    rewrite sat_coq_prop in H0 |- *.
    auto.
  + change
      (forall w1 w2 w3 : Kworlds M,
         join w1 w2 w3 ->
         KRIPKE: M, w3 |= !! P ->
         exists w1' w2' : Kworlds M,
           join w1' w2' w3 /\ w1 <= w1' /\ w2 <= w2' /\ KRIPKE: M, w1 |= !! P).
    intros.
    exists w1, w2.
    split; auto.
    split; [reflexivity |].
    split; [reflexivity |].
    rewrite sat_coq_prop in H0 |- *.
    auto.
Qed.

End Sound_Flat_Corable.
