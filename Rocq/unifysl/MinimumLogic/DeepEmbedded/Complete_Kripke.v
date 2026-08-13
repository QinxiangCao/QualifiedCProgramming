Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Canonical_Kripke.
Require Import Logic.GeneralLogic.Complete.Complete_Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Complete.Truth_Kripke.
Require Import Logic.MinimumLogic.Complete.Lindenbaum_Kripke.
Require Logic.MinimumLogic.DeepEmbedded.MinimumLanguage.
Require Logic.MinimumLogic.DeepEmbedded.MinimumLogic.
Require Logic.MinimumLogic.DeepEmbedded.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.

Section Complete.

Context (Var: Type) (CV: Countable Var).

#[export] Instance L: Language := MinimumLanguage.L Var.
#[export] Instance minL: MinimumLanguage L := MinimumLanguage.minL Var.

#[export] Instance GP: Provable L := MinimumLogic.GP Var.
#[export] Instance GD: Derivable L := MinimumLogic.GD Var.
#[export] Instance GDP: DerivableFromProvable L GP GD := MinimumLogic.GDP Var.
#[export] Instance minAX: MinimumAxiomatization L GP := MinimumLogic.minAX Var.
#[export] Instance SC: ProvableFromDerivable L GP GD := MinimumLogic.GPD Var.
#[export] Instance bSC: BasicSequentCalculus L GD := MinimumLogic.bSC Var.
#[export] Instance fwSC: FiniteWitnessedSequentCalculus L GD := MinimumLogic.fwSC Var.
#[export] Instance minSC: MinimumSequentCalculus L GD := MinimumLogic.minSC Var.
#[export] Instance Kripke_MD: Model := KripkeSemantics.MD Var.
#[export] Instance Kripke_kMD: KripkeModel Kripke_MD := KripkeSemantics.kMD Var.
#[export] Instance Kripke_R (M: Kmodel): Relation (Kworlds M) := KripkeSemantics.R Var M.
#[export] Instance Kripke_SM: Semantics L Kripke_MD := KripkeSemantics.SM Var.
#[export] Instance Kripke_kminSM (M: Kmodel): KripkeMinimumSemantics L Kripke_MD M Kripke_SM := KripkeSemantics.kminSM Var M.

Definition cP: context -> Prop := derivable_closed.

Lemma AL_DC: at_least derivable_closed cP.
Proof. solve_at_least. Qed.

Lemma LIN_CD: forall x: expr, Lindenbaum_constructable (cannot_derive x) cP.
Proof.
  intros.
  apply Lindenbaum_constructable_suffice; auto.
  + apply MinimumLanguage.formula_countable; auto.
  + apply Lindenbaum_preserves_cannot_derive.
  + unfold cP.
    apply Lindenbaum_cannot_derive_ensures_derivable_closed.
Qed.

Definition canonical_frame: KripkeSemantics.frame :=
  KripkeSemantics.Build_frame (sig cP) (fun a b => Included _ (proj1_sig a) (proj1_sig b)).

Definition canonical_eval: Var -> KripkeSemantics.sem canonical_frame :=
  fun p a => proj1_sig a (MinimumLanguage.varp p).

Definition canonical_Kmodel: @Kmodel (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) :=
  KripkeSemantics.Build_Kmodel Var canonical_frame canonical_eval.

Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.

Definition H_R:
  forall m n Phi Psi, rel m Phi -> rel n Psi ->
    (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
Proof.
  intros.
  change (m = Phi) in H.
  change (n = Psi) in H0.
  subst; reflexivity.
Qed.

Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + exact (truth_lemma_impp cP rel H_R AL_DC LIN_CD x1 x2 IHx1 IHx2).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.

Import Logic.MinimumLogic.DeepEmbedded.KripkeSemantics.

Theorem complete_MinimumLogic_Kripke_all:
  strongly_complete GD Kripke_SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder)).
Proof.
  apply (general_completeness cP rel LIN_CD TRUTH).
  constructor; hnf.
  + intros.
    exact (denote_monotonic cP rel H_R
             (MinimumLanguage.varp v)
             (TRUTH (MinimumLanguage.varp v))).
  + exact (po_R cP rel H_R).
Qed.

End Complete.
