Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MetaLogicInj.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import CoqPropInLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Module Semantics.

Definition coq_prop {worlds: Type} (P: Prop): Ensemble worlds :=
  fun _ => P.

End Semantics.

Module SemanticsMono.

Program Definition coq_prop
      {worlds: Type}
      {R: Relation worlds}
      (P: Prop): MonoEnsemble worlds :=
  Semantics.coq_prop P.
Next Obligation.
  hnf.
  unfold Semantics.coq_prop.
  auto.
Qed.

End SemanticsMono.

Class CoqPropSemantics
      (L: Language)
      {coq_prop_L: CoqPropLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      (SM: Semantics L MD): Type :=
  denote_coq_prop: forall P, Same_set _ (Kdenotation M (!! P)) (Semantics.coq_prop P).

Lemma sat_coq_prop
      {L: Language}
      {coq_prop_L: CoqPropLanguage L}
      {MD: Model}
      {kMD: KripkeModel MD}
      {M: Kmodel}
      {SM: Semantics L MD}
      {coq_prop_SM: CoqPropSemantics L MD M SM}:
  forall m P,
    KRIPKE: M , m |= !! P <-> P.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_coq_prop P).
  split; [apply H | apply H0].
Qed.
