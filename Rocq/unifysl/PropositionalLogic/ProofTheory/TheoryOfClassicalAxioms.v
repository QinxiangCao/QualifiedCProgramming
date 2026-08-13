Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class PeirceLaw (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) := {
  __provable_peirce_law: forall x y, |-- ((x --> y) --> x) --> x
}.

Class ByContradiction (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  __by_contradiction: forall x y, |-- (~~ x --> y) --> (~~ x --> ~~ y) --> x
}.

Class DoubleNegElimination (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  __double_negp_elim: forall x, |-- ~~ (~~ x) --> x
}.

Class ClassicAnalysis (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  __classic_analysis: forall x y, |-- (x --> y) --> (~~ x --> y) --> y
}.

Class ExcludedMiddle (L: Language) {orpL: OrLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  __excluded_middle: forall x, |-- x || ~~ x
}.

Class ImplyToOr (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  __provable_derives_negp_orp: forall x y, |-- (x --> y) --> (~~ x || y)
}.


(* two new classes for each of the derivable rules; 
    prove that the two rules can derive excluded middle
    only using provable_by_contradiction suffices *)
  
(************************************************)
(*                                              *)
(*                  PeirceLaw                   *)
(*                /           |\                *)
(*              |/              \               *)
(*  ByContradiction          ClassicAnalysis    *)
(*              \               /|  /|\  |      *)
(*               \|            /     |   |      *)
(*         DoubleNegativeElimination |   |      *)
(*                                   |   |      *)
(*                                   |   |      *)
(*           ------------------------   \|/     *)
(*      ExcludedMiddle <--------  ImplyToOr     *)
(*                                              *)
(*                                              *)
(*                                              *)
(************************************************)
              
Section ExcludedMiddle2ClassicAnalysis.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {emAX: ExcludedMiddle L Gamma}.

Lemma ExcludedMiddle2ClassicAnalysis: ClassicAnalysis L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  rewrite __provable_derivable.
  rewrite <- derivables_impp_theorem.
  rewrite <- derivables_impp_theorem.
  apply deduction_subst1 with (x || ~~ x).
  + do 2 apply deduction_weaken1.
    rewrite <- __provable_derivable.
    apply __excluded_middle.
  + apply derivables_orp_elim; rewrite derivables_impp_theorem; solve_assum.
Qed.

End ExcludedMiddle2ClassicAnalysis.

Section ClassicAnalysis2ImplyToOr.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {orpGamma: OrAxiomatization L Gamma}
        {inegpGamma: IntuitionisticNegAxiomatization L Gamma}
        {cAX: ClassicAnalysis L Gamma}.

Lemma ClassicAnalysis2ExcludedMiddle: ExcludedMiddle L Gamma.
Proof.
  constructor.
  intros.
  pose proof __classic_analysis x (x || ~~ x).
  pose proof provables_modus_ponens _ _ H (provable_orp_intros1 _ _).
  pose proof provables_modus_ponens _ _ H0 (provable_orp_intros2 _ _).
  auto.
Qed.

Lemma ClassicAnalysis2ImplyToOr: ImplyToOr L Gamma.
Proof.
  pose proof ClassicAnalysis2ExcludedMiddle as EM.
  constructor.
  AddSequentCalculus.
  intros.
  rewrite __provable_derivable.
  rewrite <- derivables_impp_theorem.
  apply (derivables_modus_ponens _ (x || ~~ x)).
  + pose proof __excluded_middle x.
    pose proof provables_impp_elim (x-->y) _ H.
    rewrite __provable_derivable in H0.
    rewrite <- derivables_impp_theorem in H0. apply H0.
  + apply derivables_orp_elim'.
    - rewrite <- derivables_impp_theorem.
      apply derivables_orp_intros2.
      rewrite -> derivables_impp_theorem.
      apply derivable_assum1.
    - rewrite <- derivables_impp_theorem.
      apply derivables_orp_intros1.
      apply derivable_assum1.
Qed.

End ClassicAnalysis2ImplyToOr.

Section ImplyToOr2ExcludedMiddle.

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
        {itoAX: ImplyToOr L Gamma}.

Lemma ImplyToOr2ExcludedMiddle: ExcludedMiddle L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  pose proof __provable_derives_negp_orp x x.
  rewrite provable_orp_impp_comm in H.
  rewrite <- H.
  rewrite __provable_derivable. rewrite <- derivables_impp_theorem.
  solve_assum.
Qed.

End ImplyToOr2ExcludedMiddle.

Section PeirceLaw2ByContradiction.

Context {L: Language}
        {minL: MinimumLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {plAX: PeirceLaw L Gamma}.

Lemma Peirce2ByContradiction: ByContradiction L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  pose proof aux_negp_rule x _ (provable_impp_refl x).
  pose proof __provable_peirce_law x (~~ (x --> x)).
  rewrite H in H0.
  rewrite <- H0 at 3.
  rewrite <- (provable_axiom2 (~~ x) (~~ y) x).
  rewrite <- (provable_axiom2 (~~ x) y (~~ y --> x)).
  apply aux_minimun_rule00.
  apply provable_contradiction_elim2.
Qed.

End PeirceLaw2ByContradiction.

Section ByContradiction2DoubleNegElimination.

Context {L: Language}
        {minL: MinimumLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {bcAX: ByContradiction L Gamma}.

Lemma ByContradiction2DoubleNegElimination:
  DoubleNegElimination L Gamma.
Proof.
  constructor.
  intros.
  pose proof __by_contradiction x (~~ x).
  pose proof provables_modus_ponens _ _ H (provable_impp_refl _).
  rewrite <- H0 at 2.
  apply provable_axiom1.
Qed.

End ByContradiction2DoubleNegElimination.

Section DoubleNegElimination2ClassicAnalysis.

Context {L: Language}
        {minL: MinimumLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {dneAX: DoubleNegElimination L Gamma}.

Lemma DoubleNegElimination2ClassicAnalysis: ClassicAnalysis L Gamma.
Proof.
  constructor.
  intros.
  rewrite <- provable_impp_arg_switch.
  rewrite <- (__double_negp_elim y) at 3.
  rewrite <- provable_contrapositivePN.
  rewrite <- (aux_minimun_theorem04 (~~ y) (~~ (x --> y))).
  rewrite <- provable_contrapositivePP.
  rewrite <- (aux_minimun_theorem02 x y).
  rewrite (provable_contradiction_elim2 y x) at 1.
  rewrite (provable_impp_arg_switch (~~ x) (~~ y) x).
  rewrite <- aux_minimun_theorem00.
  rewrite <- (aux_minimun_theorem04 (~~ x --> x) x).
  AddSequentCalculus.
  rewrite __provable_derivable.
  rewrite <- ! derivables_impp_theorem.
  rewrite <- (__double_negp_elim x) at 5.
  apply derivables_contrapositivePN.
  apply (derivables_contradiction_elim _ x).
  + rewrite derivables_impp_theorem.
    solve_assum.
  + solve_assum.
Qed.

End DoubleNegElimination2ClassicAnalysis.

Section ClassicAnalysis2PeirceLaw.

Context {L: Language}
        {minL: MinimumLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {inegpGamma: IntuitionisticNegAxiomatization L Gamma}
        {cAX: ClassicAnalysis L Gamma}.

Lemma ClassicAnalysis2DoubleNegElimination: DoubleNegElimination L Gamma.
Proof.
  constructor.
  intros.
  pose proof __classic_analysis x x.
  pose proof provables_modus_ponens _ _ H (provable_impp_refl _).
  rewrite <- H0 at 2.
  apply provable_contradiction_elim1.
Qed.

Lemma ClassicAnalysis2PeirceLaw: PeirceLaw L Gamma.
Proof.
  pose proof ClassicAnalysis2DoubleNegElimination.
  constructor.
  intros.
  rewrite <- (__double_negp_elim x) at 3.
  rewrite <- (aux_minimun_theorem04 ((x --> y) --> x) (~~ (~~ x))).
  AddSequentCalculus.
  rewrite __provable_derivable.
  rewrite <- ! derivables_impp_theorem.
  apply derivables_contrapositivePN.
  apply derivables_contradiction_elim with x; [| solve_assum].
  rewrite ! derivables_impp_theorem.
  rewrite <- __provable_derivable.
  rewrite <- provable_impp_trans.
  apply provable_contradiction_elim1.
Qed.

End ClassicAnalysis2PeirceLaw.

(***************************************)
(*   Resuming Axioms of Negation       *)
(***************************************)

Section ByContradiction2IntuitionisticNegAxiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {bcAX: ByContradiction L Gamma}.

Lemma ByContradiction2IntuitionisticNegAxiomatization:
  IntuitionisticNegAxiomatization L Gamma.
Proof.
  pose proof ByContradiction2DoubleNegElimination as dneAX.
  constructor.
  + intros.
    pose proof __by_contradiction (~~ y) x.
    rewrite <- (provable_axiom1 (~~ x) (~~ (~~ y))) in H.
    rewrite <- H.
    rewrite <- provable_impp_trans.
    apply __double_negp_elim.
  + intros.
    rewrite (provable_axiom1 x (~~ y)) at 2.
    rewrite (provable_axiom1 (~~ x) (~~ y)).
    rewrite <- provable_impp_arg_switch.
    apply __by_contradiction.
  + intros.
    pose proof __by_contradiction (~~ (~~ x)) x.
    rewrite <- (provable_axiom1 x (~~ (~~ (~~ x)))) in H.
    rewrite provable_impp_arg_switch in H.
    eapply provables_modus_ponens; [exact H |].
    apply __double_negp_elim.
Qed.

End ByContradiction2IntuitionisticNegAxiomatization.

