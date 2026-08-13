Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MinimumLogic.Sound.Sound_Classical_Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.

(* TODO: split part of this file into MinimumLogic folder. *)

#[export] Instance Pred_minL (A: Type): MinimumLanguage (Pred_L A) := Build_MinimumLanguage (Pred_L A) Semantics.impp.

#[export] Instance Pred_andpL (A: Type): AndLanguage (Pred_L A) := Build_AndLanguage (Pred_L A) Semantics.andp.

#[export] Instance Pred_orpL (A: Type): OrLanguage (Pred_L A) := Build_OrLanguage (Pred_L A) Semantics.orp.

#[export] Instance Pred_falsepL (A: Type): FalseLanguage (Pred_L A) := Build_FalseLanguage (Pred_L A) Semantics.falsep.

#[export] Instance Pred_tminSM (A: Type): TrivialMinimumSemantics (Pred_L A) (Build_Model A) (Pred_SM A).
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

#[export] Instance Pred_andpSM (A: Type): AndSemantics (Pred_L A) (Build_Model A) (Pred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
Qed.

#[export] Instance Pred_orpSM (A: Type): OrSemantics (Pred_L A) (Build_Model A) (Pred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
Qed.

#[export] Instance Pred_falsepSM (A: Type): FalseSemantics (Pred_L A) (Build_Model A) (Pred_SM A).
Proof.
  constructor.
  + apply Same_set_refl.
Qed.

#[export] Instance Pred_Gamma (A: Type): Provable (Pred_L A) :=
  Build_Provable (Pred_L A) (fun x: expr => forall a: A, x a).

#[export] Instance Pred_minAX (A: Type): MinimumAxiomatization (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y ? ? m.
    pose proof @sound_modus_ponens (Pred_L A) _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) x y.
    exact (H1 m (H m) (H0 m)).
  + intros x y.
    exact (@sound_axiom1 (Pred_L A) _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) x y).
  + intros x y z.
    exact (@sound_axiom2 (Pred_L A) _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) x y z).
Qed.

#[export] Instance Pred_andpAX (A: Type): AndAxiomatization (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_andp_intros (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_andpSM A) x y).
  + intros x y.
    exact (@sound_provable_andp_elim1 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_andpSM A) x y).
  + intros x y.
    exact (@sound_provable_andp_elim2 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_andpSM A) x y).
Qed.

#[export] Instance Pred_orpAX (A: Type): OrAxiomatization (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_provable_orp_intros1 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_orpSM A) x y).
  + intros x y.
    exact (@sound_provable_orp_intros2 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_orpSM A) x y).
  + intros x y z.
    exact (@sound_provable_orp_elim (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_orpSM A) x y z).
Qed.

#[export] Instance Pred_falsepAX (A: Type): FalseAxiomatization (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x.
    exact (@sound_provable_falsep_elim (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_falsepSM A) x).
Qed.
(*TODO: need to adjust(about classical)
#[export] Instance Pred_cpGamma (A: Type): ClassicalPropositionalLogic (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_excluded_middle (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_tpSM A) x).
Qed.
*)
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Semantics.SemanticEquiv.
Require Import Logic.PropositionalLogic.Semantics.Kripke.

#[export] Instance Pred_kiSM (A: Type): @KripkeIntuitionisticSemantics (Pred_L A) (Build_Model A) (unit_kMD _) tt eq (Pred_SM A) :=
  @eqR_KripkeIntuitionistic _ _ _.

#[export] Instance Pred_kminSM (A: Type): @KripkeMinimumSemantics (Pred_L A) (Pred_minL A) (Build_Model A) (unit_kMD _) tt eq (Pred_SM A) :=
  @Trivial2Kripke _ _ _ _ (Pred_tminSM A).

#[export] Instance Pred_kandpSM (A: Type): @KripkeAndSemantics (Pred_L A) (Pred_andpL A) (Build_Model A) (unit_kMD _) tt (Pred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
Qed.

#[export] Instance Pred_korpSM (A: Type): @KripkeOrSemantics (Pred_L A) (Pred_orpL A) (Build_Model A) (unit_kMD _) tt (Pred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
Qed.

#[export] Instance Pred_kfalsepSM (A: Type): @KripkeFalseSemantics (Pred_L A) (Pred_falsepL A) (Build_Model A) (unit_kMD _) tt (Pred_SM A).
Proof.
  constructor.
  + apply Same_set_refl.
Qed.
