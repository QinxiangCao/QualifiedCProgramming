Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.
Import SeparationLogicNotation.

Class Corable (L: Language): Type := {
  corable: expr -> Prop;
}.

Class Corable_withAxiomatization
      (L: Language)
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {sepconL: SepconLanguage L}
      (GammaP: Provable L)
      (Cor: Corable L) := {
  corable_preserved': forall x y,
    |-- x <--> y -> corable x -> corable y;
  corable_andp_sepcon1: forall x y z,
    corable x -> |-- (x && y) * z <--> x && (y * z);
}.

Class MinimumCorable
      (L: Language)
      {minL: MinimumLanguage L}
      (Cor: Corable L) := {
  corable_impp: forall x y,
    corable x -> corable y -> corable (x --> y);
}.

Class SepconCorable
      (L: Language)
      {sepconL: SepconLanguage L}
      (Cor: Corable L) := {
  corable_sepcon: forall x y,
    corable x -> corable y -> corable (x * y);
}.

Class CoqPropCorable
      (L: Language)
      {coq_prop_L: CoqPropLanguage L}
      (Cor: Corable L) := {
  corable_coq_prop: forall P,
    corable (!! P)
}.

Section Corable.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {Cor: Corable L}
        {CorAX: Corable_withAxiomatization L Gamma Cor}.

Lemma corable_sepcon_andp2: forall P Q R,
  corable P -> |-- Q * (R && P) <--> P && (Q * R).
Proof.
  intros.
  rewrite ! (provable_sepcon_impp_comm Q).
  rewrite (provable_andp_comm R).
  apply corable_andp_sepcon1; auto.
Qed.

Lemma corable_sepcon_andp1: forall P Q R,
  corable P -> |-- Q * (P && R) <--> P && (Q * R).
Proof.
  intros.
  rewrite !(provable_sepcon_impp_comm Q).
  apply corable_andp_sepcon1; auto.
Qed.

Lemma corable_andp_sepcon2: forall P Q R,
  corable P -> |-- Q && P * R <--> P && (Q * R).
Proof.
  intros.
  rewrite (provable_andp_comm Q).
  apply corable_andp_sepcon1; auto.
Qed.

Context {coq_prop_L: CoqPropLanguage L}
        {coq_prop_AX: CoqPropAxiomatization L Gamma}
        {coq_prop_Cor: CoqPropCorable L Cor}.

Lemma CoqPropCorable2SepconCoqPropAX: SepconCoqPropAxiomatization L Gamma.
Proof.
  constructor.
  intros.
  apply corable_andp_sepcon1.
  apply corable_coq_prop.
Qed.

End Corable.
