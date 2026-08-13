Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.Semantics.Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import CoqPropInLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Sound_Kripke.

Context {L: Language}
        {minL: MinimumLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {SM: Semantics L MD}
        {R: Relation (Kworlds M)}
        {po_R: PreOrder Krelation}
        {kminSM: KripkeMinimumSemantics L MD M SM}
        {kiSM: KripkeIntuitionisticSemantics L MD M SM}
        {coq_prop_SM: CoqPropSemantics L MD M SM}.

Lemma sound_coq_prop_intros: forall P: Prop, P ->
  forall m, KRIPKE: M, m |=  !! P.
Proof.
  intros.
  rewrite sat_coq_prop.
  auto.
Qed.

Lemma sound_coq_prop_elim: forall (P: Prop) x,
  (P -> forall m, KRIPKE: M, m |= x) ->
  (forall m, KRIPKE: M, m |= !! P --> x).
Proof.
  intros.
  rewrite sat_impp.
  intros.
  rewrite sat_coq_prop in H1.
  specialize (H H1 n).
  auto.
Qed.

Lemma sound_coq_prop_impp: forall (P Q: Prop),
  forall m, KRIPKE: M, m |= (!! P --> !! Q) --> !! (P -> Q).
Proof.
  intros.
  rewrite sat_impp.
  intros.
  clear m H.
  rewrite sat_impp in H0.
  specialize (H0 n ltac:(reflexivity)).
  rewrite !sat_coq_prop in H0.
  rewrite sat_coq_prop.
  auto.
Qed.

End Sound_Kripke.

