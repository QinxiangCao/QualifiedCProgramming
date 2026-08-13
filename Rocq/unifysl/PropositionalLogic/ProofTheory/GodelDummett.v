(* M. Dummett. A propositional calculus with denumerable matrix. J. Symbolic Logic, 24(2):97–106, 1959. *)
(* K. G¨odel. On the intuitionistic propositional calculus. In S. Feferman, J. W. D. Jr, S. C. Kleene, G. H. Moore, R. M. Solovay, and J. van Heijenoort, editors, Collected Works, volume 1. Oxford University Press, 1986. *)

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class GodelDummettAxiomatization (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} (Gamma: Provable L) := {
  impp_choice: forall x y, |-- (x --> y) || (y --> x)
}.

Section GodelDummett.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {orpGamma: OrAxiomatization L Gamma}
        {falsepGamma: FalseAxiomatization L Gamma}
        {inegpGamma: IntuitionisticNegAxiomatization L Gamma}
        {gdpAX: GodelDummettAxiomatization L Gamma}.

#[export] Instance GodelDummett2DeMorgan: DeMorganAxiomatization L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  rewrite __provable_derivable.
  set (Phi := empty_context).
  clearbody Phi.

  pose proof impp_choice x (~~ x).
  apply derivables_weaken0 with (Phi := Phi) in H.

  assert (Phi |--- (x --> ~~ x) --> (x --> FF)).
  {
    rewrite <- derivables_impp_theorem.
    rewrite <- derivables_impp_theorem.
    eapply deduction_weaken with (Union _ (Union _ (Union _ Phi (Singleton _ (x --> ~~ x))) (Singleton _ x)) (Singleton _ x)).
    + intros y ?.
      destruct H0; [| right; auto].
      destruct H0; [| right; auto].
      left; auto.
    + rewrite derivables_impp_theorem.
      rewrite derivables_impp_theorem.
      pose proof provable_negp_derives x. rewrite <- H0.
      apply derivable_assum1.
  }
  assert (Phi |--- (~~ x --> x) --> (~~ x --> FF)).
  {
    rewrite <- derivables_impp_theorem.
    pose proof derivable_assum1 Phi (~~ x --> x).
    set (Psi := Union expr Phi (Singleton expr (~~ x --> x))) in H1 |- *; clearbody Psi.
    rewrite <- derivables_impp_theorem in H1 |- *.
    pose proof derivable_assum1 Psi (~~ x).
    pose proof provable_negp_derives x. rewrite H3 in H2 at 2.
    pose proof derivables_modus_ponens _ _ _ H1 H2.
    auto.
  }

  rewrite <- derivables_impp_theorem in H0, H1.
  apply (derivables_orp_intros1 _ _ (~~ x --> FF)) in H0.
  apply (derivables_orp_intros2 _ (x --> FF)) in H1.
  rewrite derivables_impp_theorem in H0, H1.
  pose proof derivables_orp_elim' _ _ _ _ H0 H1.
  pose proof derivables_modus_ponens _ _ _ H H2.
  pose proof provable_derives_negp (~~ x). rewrite <- H4.
  pose proof provable_derives_negp x. rewrite <- H5 at 1.
  apply H3.
Qed.

End GodelDummett.
