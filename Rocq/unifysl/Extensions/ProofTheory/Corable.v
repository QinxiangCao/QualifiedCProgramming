Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.Extensions.ProofTheory.Stable.
Require Import Logic.SeparationLogic.ProofTheory.Corable.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

#[export] Instance CorableAxiomatization2StableProperIff
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {sepconL: SepconLanguage L}
      {Gamma: Provable L}
      {minAX: MinimumAxiomatization L Gamma}
      {iffpAX: IffAxiomatization L Gamma}
      {Cor: Corable L}
      {CorAX: Corable_withAxiomatization L Gamma Cor}:
  StableProperIff L Gamma corable.
Proof.
  constructor.
  hnf; intros x y Hxy.
  split; intros Hstable.
  - eapply corable_preserved'; eauto.
  - eapply corable_preserved'.
    + apply (@Equivalence_Symmetric expr (fun x y => |-- x <--> y) _).
      exact Hxy.
    + exact Hstable.
Qed.

#[export] Instance CorableAxiomatization2SeparationAbsorbStable
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {sepconL: SepconLanguage L}
      {Gamma: Provable L}
      {Cor: Corable L}
      {CorAX: Corable_withAxiomatization L Gamma Cor}:
  SeparationAbsorbStable L Gamma corable.
Proof.
  constructor.
  apply corable_andp_sepcon1.
Qed.

Section Corable.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {Cor: Corable L}
        {CorAX: Corable_withAxiomatization L Gamma Cor}
        {corable_istable: ImpStable L corable}
        {corable_astable: AndStable L corable}
        {corable_ostable: OrStable L corable}
        {corable_fstable: FalseStable L corable}
        {corable_sstable: SeparationStable L corable}.

Lemma corable_impp: forall x y, corable x -> corable y -> corable (x --> y).
Proof. intros. apply impp_stable; auto. Qed.

Lemma corable_andp: forall x y, corable x -> corable y -> corable (x && y).
Proof. intros. apply andp_stable; auto. Qed.

Lemma corable_orp: forall x y, corable x -> corable y -> corable (x || y).
Proof. intros. apply orp_stable; auto. Qed.

Lemma corable_iffp
      {iffp_Def_andp_impp: IffDefinition_And_Imp L}:
  forall x y, corable x -> corable y -> corable (x <--> y).
Proof. intros. apply iffp_stable; auto. Qed.

Lemma corable_falsep: corable FF.
Proof. apply falsep_stable. Qed.

Lemma corable_truep
      {truep_Def_falsep_impp: TrueDefinition_False_Imp L}:
  corable TT.
Proof. apply truep_stable. Qed.

Lemma corable_sepcon: forall x y, corable x -> corable y -> corable (x * y).
Proof. intros. apply sepcon_stable; auto. Qed.

Lemma corable_wand: forall x y, corable x -> corable y -> corable (x -* y).
Proof. intros. apply wand_stable; auto. Qed.

Instance corable_proper_iff: Proper ((fun x y => |-- x <--> y) ==> iff) corable.
Proof. apply stable_proper_iffp. Qed.

Lemma corable_andp_sepcon2: forall x y z, corable y -> |-- (x && y) * z <--> y && (x * z).
Proof.
  intros.
  rewrite provable_andp_comm.
  apply corable_andp_sepcon1; auto.
Qed.

Lemma corable_sepcon_andp1: forall x y z, corable y -> |-- x * (y && z) <--> y && (x * z).
Proof.
  intros.
  rewrite Logic.SeparationLogic.ProofTheory.SeparationLogic.provable_sepcon_impp_comm.
  rewrite (Logic.SeparationLogic.ProofTheory.SeparationLogic.provable_sepcon_impp_comm x z).
  apply corable_andp_sepcon1; auto.
Qed.

Lemma corable_sepcon_andp2: forall x y z, corable z -> |-- x * (y && z) <--> z && (x * y).
Proof.
  intros.
  rewrite provable_andp_comm.
  apply corable_sepcon_andp1; auto.
Qed.

Lemma corable_sepcon_imply_andp: forall x y, corable x -> corable y -> |-- x * y --> x && y.
Proof.
  intros.
  rewrite <- (provable_andp_truep y) at 1.
  rewrite corable_sepcon_andp1 by auto.
  rewrite <- (provable_andp_truep x) at 1.
  rewrite corable_andp_sepcon1 by auto.
  rewrite <- provable_andp_assoc.
  rewrite (provable_andp_comm x y).
  apply provable_andp_elim1.
Qed.

Lemma corable_sepcon_is_andp {ExtsGamma: ExtSeparationLogic L Gamma}: forall x y, corable x -> corable y -> |-- x * y <--> x && y.
Proof.
  intros.
  rewrite <- (provable_andp_truep y) at 1.
  rewrite corable_sepcon_andp1 by auto.
  rewrite <- (provable_andp_truep x) at 1.
  rewrite corable_andp_sepcon1 by auto.
  rewrite <- provable_andp_assoc.
  rewrite (provable_andp_comm x y).
  rewrite provable_truep_sepcon_truep.
  rewrite provable_andp_truep.
  apply provable_iffp_refl.
Qed.

End Corable.

Existing Instance corable_proper_iff.
