Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Module Semantics.

Definition andp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m /\ Y m.

Definition orp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m \/ Y m.

Definition falsep {model: Type}: Ensemble model := fun m => False.

Definition truep {model: Type}: Ensemble model := fun m => True.

Definition iffp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m <-> Y m.

Definition negp {model: Type} (X: Ensemble model): Ensemble model :=
  fun m => ~ X m.

End Semantics.

Class AndSemantics
      (L: Language)
      {andpL: AndLanguage L}
      (MD: Model)
      (SM: Semantics L MD):= {
  denote_andp: forall x y, Same_set _ (denotation (x && y)) (Semantics.andp (denotation x) (denotation y));
}.

Class OrSemantics
      (L: Language)
      {orpL: OrLanguage L}
      (MD: Model)
      (SM: Semantics L MD):= {
  denote_orp: forall x y, Same_set _ (denotation (x || y)) (Semantics.orp (denotation x) (denotation y));
}.

Class FalseSemantics
      (L: Language)
      {falsepL: FalseLanguage L}
      (MD: Model)
      (SM: Semantics L MD):= {
  denote_falsep: Same_set _ (denotation FF) Semantics.falsep
}.

Class TrueSemantics
      (L: Language)
      {truepL: TrueLanguage L}
      (MD: Model)
      (SM: Semantics L MD):= {
  denote_truep: Same_set _ (denotation TT) Semantics.truep
}.

Class IffSemantics
      (L: Language)
      {iffpL: IffLanguage L}
      (MD: Model)
      (SM: Semantics L MD):= {
  denote_iffp: forall x y, Same_set _ (denotation (x <--> y)) (Semantics.iffp (denotation x) (denotation y));
}.

Class NegSemantics
      (L: Language)
      {negpL: NegLanguage L}
      (MD: Model)
      (SM: Semantics L MD):= {
  denote_negp: forall x, Same_set _ (denotation (~~ x)) (Semantics.negp (denotation x));
}.

Section Trivial.

Context {L: Language}
        {MD: Model}
        {SM: Semantics L MD}.

Lemma sat_andp {andpL: AndLanguage L} {andpSM: AndSemantics L MD SM}:
  forall m x y, m |= x && y <-> (m |= x /\ m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_andp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_orp {orpL: OrLanguage L} {orpSM: OrSemantics L MD SM}:
  forall m x y, m |= x || y <-> (m |= x \/ m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_orp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_falsep {falsepL: FalseLanguage L} {falsepSM: FalseSemantics L MD SM}:
  forall m, m |= FF <-> False.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_falsep.
  split; [apply H | apply H0].
Qed.

Lemma sat_truep {truepL: TrueLanguage L} {truepSM: TrueSemantics L MD SM}:
  forall m, m |= TT <-> True.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_truep.
  split; [apply H | apply H0].
Qed.

Lemma sat_iffp {iffpL: IffLanguage L} {iffpSM: IffSemantics L MD SM}:
  forall m x y, m |= x <--> y <-> (m |= x <-> m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_iffp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_negp {negpL: NegLanguage L} {negpSM: NegSemantics L MD SM}:
  forall m x, m |= ~~ x  <-> ~ (m |= x).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_negp x).
  split; [apply H | apply H0].
Qed.

End Trivial.
