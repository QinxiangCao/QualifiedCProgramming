Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Logic.MinimumLogic.Sound.Sound_Kripke.
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

(* TODO: soundness about trivial semantics is not yet added. *)

Section Sound.

Context (Var: Type).

#[export] Instance L: Language := MinimumLanguage.L Var.
#[export] Instance minL: MinimumLanguage L := MinimumLanguage.minL Var.

#[export] Instance GP: Provable L := MinimumLogic.GP Var.
#[export] Instance GD: Derivable L := MinimumLogic.GD Var.
#[export] Instance GDP: DerivableFromProvable L GP GD := MinimumLogic.GDP Var.
#[export] Instance minAX: MinimumAxiomatization L GP := MinimumLogic.minAX Var.

#[export] Instance Kripke_MD: Model := KripkeSemantics.MD Var.
#[export] Instance Kripke_kMD: KripkeModel Kripke_MD := KripkeSemantics.kMD Var.
#[export] Instance Kripke_R (M: Kmodel): Relation (Kworlds M) := KripkeSemantics.R Var M.
#[export] Instance Kripke_SM: Semantics L Kripke_MD := KripkeSemantics.SM Var.
#[export] Instance Kripke_kminSM (M: Kmodel): KripkeMinimumSemantics L Kripke_MD M Kripke_SM := KripkeSemantics.kminSM Var M.

Section Sound_Kripke.

Import Logic.MinimumLogic.Sound.Sound_Kripke.
Import Logic.MinimumLogic.DeepEmbedded.KripkeSemantics.

Theorem sound_intuitionistic_Kripke_all:
  provable_sound GP Kripke_SM (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder)).
Proof.
  hnf; intros.
  intros _ [M m [mono po_R]].
  pose proof (@KripkeSemantics.kiSM Var M mono po_R) as kiSM.
  hnf in mono, po_R.
  change (Kmodel Var) in M.
  change (Kworlds M) in m.
  change (KRIPKE: M, m |= x).
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
Qed.

End Sound_Kripke.

End Sound.
