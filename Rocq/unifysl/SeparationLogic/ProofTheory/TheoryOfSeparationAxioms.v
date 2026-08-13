Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.
Import SeparationLogicNotation.

Class SepconMonoAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (GammaP: Provable L) := {
  __provable_sepcon_mono: forall x1 x2 y1 y2 : expr, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- x1 * y1 --> x2 * y2
}.

Class SepconAxiomatization_weak
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (GammaP: Provable L) := {
  __provable_sepcon_comm_impp: forall x y, |-- x * y --> y * x;
  __provable_sepcon_assoc1: forall x y z, |-- x * (y * z) --> (x * y) * z;
}.

Class SepconAxiomatization_weak_iffp
        (L: Language)
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        (GammaP: Provable L) := {
  __sepcon_comm: forall x y, |-- x * y <--> y * x;
  __sepcon_assoc: forall x y z, |-- x * (y * z) <--> (x * y) * z;
}.

Class EmpAxiomatization_iffp
        (L: Language)
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaP: Provable L) := {
  __sepcon_emp: forall x, |-- x * emp <--> x
}.

Lemma SepconAxiomatizationWeak2SepconAxiomatization
      {L: Language}
      {minL: MinimumLanguage L}
      {sepconL: SepconLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {sepconAX: SepconAxiomatization_weak L GammaP}
      {provable_sepcon_mono_AX: SepconMonoAxiomatization L GammaP}:
  SepconAxiomatization L GammaP.
Proof.
  intros.
  constructor.
  + apply __provable_sepcon_comm_impp.
  + apply __provable_sepcon_assoc1.
  + apply __provable_sepcon_mono.
Qed.

Section FromAdjPlusSepconWeakToSepcon.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaP: Provable L}
        {minAX: MinimumAxiomatization L GammaP}
        {wandAX: WandAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization_weak L GammaP}.

Let sepcon_Comm: P.Commutativity L GammaP sepcon.
Proof.
  constructor.
  intros.
  apply __provable_sepcon_comm_impp.
Qed.

Let sepcon_Mono: P.Monotonicity L GammaP sepcon.
Proof.
  apply @P.Adjoint2Mono with (funcp := wand).
  + auto.
  + apply wand_sepcon_Adj.
  + apply sepcon_Comm.
Qed.

Lemma Adj2SepconMono: SepconMonoAxiomatization L GammaP.
Proof.
  constructor.
  intros.
  apply (@P.prodp_mono _ _ _ _ sepcon_Mono); auto.
Qed.

End FromAdjPlusSepconWeakToSepcon.

Section FromSepconWeakIffToSepconWeak.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {GammaP: Provable L}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization_weak_iffp L GammaP}.

Lemma SepconAxiomatizationWeakIff2SepconAxiomatizationWeak:
  SepconAxiomatization_weak L GammaP.
Proof.
  constructor.
  + pose proof __sepcon_comm.
    intros.
    eapply provables_iffp_elim1.
    apply H.
  + pose proof __sepcon_assoc.
    intros.
    eapply provables_iffp_elim1.
    apply H.
Qed.

End FromSepconWeakIffToSepconWeak.

Section FromAdjToPropositionalCombination.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaP: Provable L}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {coq_prop_AX: CoqPropAxiomatization L GammaP}
        {speconAX: SepconAxiomatization L GammaP}
        {wandAX: WandAxiomatization L GammaP}.

Let RDistr: P.RightDistr L GammaP sepcon orp.
Proof.
  apply (@P.Adjoint2RDistr _ _ _ _ _ _ _ wand).
  apply wand_sepcon_Adj.
Qed.

Let LDistr: P.LeftDistr L GammaP sepcon orp.
Proof.
  apply @P.RightDistr2LeftDistr; auto.
  + apply sepcon_Comm.
  + apply orp_Mono.
Qed.

Lemma Adj2SepconOr: SepconOrAxiomatization L GammaP.
Proof.
  intros.
  constructor.
  intros.
  pose proof @P.prodp_sump_distr_r _ _ _ _ _ _ _ _ RDistr.
  rewrite H.
  apply provable_impp_refl.
Qed.

Lemma Adj2SepconFalse: SepconFalseAxiomatization L GammaP.
Proof.
  intros.
  constructor.
  intros.
  rewrite (@P.falsep_prodp _ _ _ _ _ _ wand_sepcon_Adj); auto.
  apply provable_impp_refl.
Qed.

Lemma Adj2SepconCoqProp: SepconCoqPropAxiomatization L GammaP.
Proof.
  constructor.
  intros.
  apply provables_iffp_intros.
  + apply provables_impp_andp_fold.
    - apply provables_wand_sepcon_adjoint.
      apply provables_coq_prop_andp_derives.
      intros.
      apply provables_wand_sepcon_adjoint.
      apply aux_minimun_rule00.
      apply provables_coq_prop_intros.
      auto.
    - apply provable_sepcon_mono.
      * apply provable_andp_elim2.
      * apply provable_impp_refl.
  + apply provables_coq_prop_andp_derives.
    intros.
    apply provable_sepcon_mono.
    - rewrite provables_coq_prop_andp by auto.
      apply provable_impp_refl.
    - apply provable_impp_refl.
Qed.

End FromAdjToPropositionalCombination.

Section FromEmpIffToEmp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaP: Provable L}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization L GammaP}
        {empAX: EmpAxiomatization_iffp L GammaP}.

Lemma EmpAxiomatizationIff2EmpAxiomatization:
  EmpAxiomatization L GammaP.
Proof.
  constructor.
  + pose proof __sepcon_emp.
    intros.
    eapply provables_iffp_elim1.
    apply H.
  + pose proof __sepcon_emp.
    intros.
    eapply provables_iffp_elim2.
    apply H.
Qed.

End FromEmpIffToEmp.

