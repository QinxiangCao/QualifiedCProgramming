Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class DeMorganAxiomatization (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} {falsepL: FalseLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  provable_weak_excluded_middle: forall x, |-- ~~ x || ~~ ~~ x
}.

Section DeMorgan.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpGamma: AndAxiomatization L Gamma}
        {orpGamma: OrAxiomatization L Gamma}
        {falsepGamma: FalseAxiomatization L Gamma}
        {inegpGamma: IntuitionisticNegAxiomatization L Gamma}
        {iffpGamma: IffAxiomatization L Gamma}
        {truepGamma: TrueAxiomatization L Gamma}
        {dmpAX: DeMorganAxiomatization L Gamma}.

Lemma demorgan_negp_andp: forall (x y: expr),
  |-- ~~ (x && y) <--> (~~ x || ~~ y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite __provable_derivable.
  apply derivables_iffp_intros.
  + apply (derivables_modus_ponens _ (~~ x || ~~ ~~ x)); [apply derivables_weaken0, provable_weak_excluded_middle |].
    apply derivables_orp_elim'.
    - apply derivables_weaken0.
      apply provable_orp_intros1.
    - rewrite <- derivables_impp_theorem.
      apply derivables_orp_intros2.
      pose proof provable_derives_negp y. rewrite <- H.
      rewrite <- derivables_impp_theorem.
      apply  (derivables_modus_ponens _ (x --> FF)).
      * rewrite <- derivables_impp_theorem.
        apply (derivables_modus_ponens _ (x && y)).
        { apply derivables_andp_intros; [| apply deduction_weaken1]; apply derivable_assum1. }
        { pose proof provable_negp_derives (x && y). rewrite <- H0. solve_assum. }
      * pose proof provable_derives_negp x. rewrite H0.
        pose proof provable_negp_derives (~~x). rewrite <- H1.
        solve_assum.
  + rewrite derivables_impp_theorem.
    rewrite <- __provable_derivable.
    apply provable_demorgan_orp_negp.
Qed.

Lemma provables_weak_classic: forall x y: expr,
  |-- ~~ x --> y ->
  |-- ~~ (~~ x) --> y ->
  |-- y.
Proof.
  intros.
  eapply provables_modus_ponens; [| apply (provable_weak_excluded_middle x)].
  apply provables_orp_impp_fold; auto.
Qed.

End DeMorgan.
