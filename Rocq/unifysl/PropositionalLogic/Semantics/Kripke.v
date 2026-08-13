Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

(* TODO: It is so obvious that the first 3 definitions in this file are very similar with Trivial.v. The should be merged. The obstacle is the way that we formalize Kripke Semantics. See the "TODO" in GeneralLogic/Semantics/Kripke.v *)
Module Semantics.

Definition andp {worlds: Type} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => X m /\ Y m.

Definition orp {worlds: Type} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => X m \/ Y m.

Definition falsep {worlds: Type}: Ensemble worlds := fun m => False.

Definition truep {worlds: Type}: Ensemble worlds := fun m => True.

Definition iffp
           {worlds: Type} {R: Relation worlds}
           (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  andp (Semantics.impp X Y) (Semantics.impp Y X).

Definition negp
           {worlds: Type} {R: Relation worlds}
           (X: Ensemble worlds): Ensemble worlds :=
  Semantics.impp X falsep.

Lemma andp_closed {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (andp X Y).
Proof.
  intros.
  hnf; intros.
  destruct H2.
  split.
  + apply (H n); auto.
  + apply (H0 n); auto.
Qed.

Lemma orp_closed {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (orp X Y).
Proof.
  intros.
  hnf; intros.
  destruct H2; [left | right].
  + apply (H n); auto.
  + apply (H0 n); auto.
Qed.

Lemma falsep_closed {worlds: Type} {R: Relation worlds}:
  upwards_closed_Kdenote falsep.
Proof.
  intros.
  hnf; intros.
  inversion H0.
Qed.

Lemma truep_closed {worlds: Type} {R: Relation worlds}:
  upwards_closed_Kdenote truep.
Proof.
  intros.
  hnf; intros.
  exact I.
Qed.

End Semantics.

Module SemanticsMono.

Program Definition andp {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  Semantics.andp X Y.
Next Obligation.
  apply (@Semantics.andp_closed worlds R po_R);
  apply (proj2_sig _).
Defined.

Program Definition orp {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  Semantics.orp X Y.
Next Obligation.
  apply (@Semantics.orp_closed worlds R po_R);
  apply (proj2_sig _).
Defined.

Program Definition falsep {worlds: Type} {R: Relation worlds}: MonoEnsemble worlds :=
  Semantics.falsep.
Next Obligation.
  apply (@Semantics.falsep_closed worlds R);
  apply (proj2_sig _).
Defined.

End SemanticsMono.

Class KripkeAndSemantics
      (L: Language)
      {andpL: AndLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      (SM: Semantics L MD):= {
  denote_andp: forall x y, Same_set _ (Kdenotation M (x && y)) (Semantics.andp (Kdenotation M x) (Kdenotation M y));
}.

Class KripkeOrSemantics
      (L: Language)
      {orpL: OrLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      (SM: Semantics L MD):= {
  denote_orp: forall x y, Same_set _ (Kdenotation M (x || y)) (Semantics.orp (Kdenotation M x) (Kdenotation M y));
}.

Class KripkeFalseSemantics
      (L: Language)
      {falsepL: FalseLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      (SM: Semantics L MD):= {
  denote_falsep: Same_set _ (Kdenotation M FF) Semantics.falsep
}.

Class KripkeTrueSemantics
      (L: Language)
      {truepL: TrueLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      (SM: Semantics L MD):= {
  denote_truep: Same_set _ (Kdenotation M TT) Semantics.truep
}.

Class KripkeIffSemantics
      (L: Language)
      {iffpL: IffLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      {R: Relation (Kworlds M)}
      (SM: Semantics L MD):= {
  denote_iffp: forall x y, Same_set _ (Kdenotation M (x <--> y)) (Semantics.iffp (Kdenotation M x) (Kdenotation M y));
}.

Class KripkeNegSemantics
      (L: Language)
      {negpL: NegLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      {R: Relation (Kworlds M)}
      (SM: Semantics L MD):= {
  denote_negp: forall x, Same_set _ (Kdenotation M (~~ x)) (Semantics.negp (Kdenotation M x));
}.

Section KripkeSemantics.

Context {L: Language}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}.

Lemma sat_andp {andpL: AndLanguage L} {andpSM: KripkeAndSemantics L MD M SM}:
  forall m x y, KRIPKE: M , m |= x && y <-> (KRIPKE: M , m |= x /\ KRIPKE: M , m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_andp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_orp {orpL: OrLanguage L} {orpSM: KripkeOrSemantics L MD M SM}:
  forall m x y, KRIPKE: M , m |= x || y <-> (KRIPKE: M , m |= x \/ KRIPKE: M , m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_orp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_falsep {falsepL: FalseLanguage L} {falsepSM: KripkeFalseSemantics L MD M SM}:
  forall m, KRIPKE: M , m |= FF <-> False.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_falsep.
  split; [apply H | apply H0].
Qed.

Lemma sat_truep {truepL: TrueLanguage L} {truepSM: KripkeTrueSemantics L MD M SM}:
  forall m, KRIPKE: M , m |= TT <-> True.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_truep.
  split; [apply H | apply H0].
Qed.

Lemma sat_iffp {iffpL: IffLanguage L} {iffpSM: KripkeIffSemantics L MD M SM}:
  forall m x y, (KRIPKE: M , m |= x <--> y) <->
                (forall n, m <= n -> KRIPKE: M , n |= x <-> KRIPKE: M , n |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_iffp x y).
  split.
  + intros HH; apply H in HH; clear H H0.
    destruct HH.
    intros.
    specialize (H n H1).
    specialize (H0 n H1).
    tauto.
  + intros HH; apply H0; clear H H0.
    split; hnf; intros; specialize (HH n H); tauto.
Qed.

Lemma sat_negp {negpL: NegLanguage L} {negpSM: KripkeNegSemantics L MD M SM}:
  forall m x, (KRIPKE: M , m |= ~~ x) <->
               (forall n, m <= n -> ~ KRIPKE: M , n |= x).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_negp x).
  split.
  + intros HH; apply H in HH; clear H H0.
    intros.
    specialize (HH n H).
    tauto.
  + intros HH; apply H0; clear H H0.
    hnf; intros; specialize (HH n H); tauto.
Qed.

Lemma valid_iffp
      {po_R: PreOrder Krelation}
      {iffpL: IffLanguage L}
      {iffpSM: KripkeIffSemantics L MD M SM}:
  forall x y,
  (forall m, KRIPKE: M , m |= x <--> y) ->
  (forall m, KRIPKE: M , m |= x <-> KRIPKE: M , m |= y).
Proof.
  intros.
  specialize (H m).
  rewrite sat_iffp in H.
  apply H.
  reflexivity.
Qed.

End KripkeSemantics.
