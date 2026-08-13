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
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.Extensions.ProofTheory.Stable.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class Corable
      (L: Language)
      {minL: MinimumLanguage L}
      {pL: PropositionalLanguage L}
      {sepconL: SepconLanguage L}
      {wandL: WandLanguage L}
      (Gamma: Provable L) := {
  corable: expr -> Prop;
  corable_pstable: PropositionalStable L Gamma corable;
  corable_sstable: SeparationStable L Gamma corable;
  corable_sabs: SeparationAbsorbStable L Gamma corable
}.

Section Corable.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}
        {CosAX: Corable L Gamma}.

Lemma corable_andp: forall x y, corable x -> corable y -> corable (x && y).
Proof. intros. apply (@andp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_orp: forall x y, corable x -> corable y -> corable (x || y).
Proof. intros. apply (@orp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_impp: forall x y, corable x -> corable y -> corable (x --> y).
Proof. intros. apply (@impp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_iffp: forall x y, corable x -> corable y -> corable (x <--> y).
Proof. intros. apply (@iffp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_falsep: corable FF.
Proof. apply (@falsep_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_truep: corable TT.
Proof. apply (@truep_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_sepcon: forall x y, corable x -> corable y -> corable (x * y).
Proof. intros. apply (@sepcon_stable L _ _ _ Gamma corable corable_sstable); auto. Qed.

Lemma corable_wand: forall x y, corable x -> corable y -> corable (x -* y).
Proof. intros. apply (@wand_stable L _ _ _ Gamma corable corable_sstable); auto. Qed.

Instance corable_proper_iff: Proper ((fun x y => |-- x <--> y) ==> iff) corable.
Proof. apply (@stable_proper_iffp L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_andp_sepcon1: forall x y z, corable x -> |-- (x && y) * z <--> x && (y * z).
Proof. intros. apply (@stable_andp_sepcon1 L _ _ _ _ Gamma corable corable_sabs); auto. Qed.

Lemma corable_andp_sepcon2: forall x y z, corable y -> |-- (x && y) * z <--> y && (x * z).
Proof.
  intros.
  rewrite provable_andp_comm.
  apply corable_andp_sepcon1; auto.
Qed.

Lemma corable_sepcon_andp1: forall x y z, corable y -> |-- x * (y && z) <--> y && (x * z).
Proof.
  intros.
  rewrite provable_sepcon_impp_comm.
  rewrite (provable_sepcon_impp_comm x z).
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
