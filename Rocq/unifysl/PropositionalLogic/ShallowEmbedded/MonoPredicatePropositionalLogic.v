Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Sound.Sound_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Sound.Sound_Kripke.

#[export] Instance MonoPred_minL (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: MinimumLanguage (MonoPred_L A) := Build_MinimumLanguage (MonoPred_L A) SemanticsMono.impp.

#[export] Instance MonoPred_andpL (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: AndLanguage (MonoPred_L A) := Build_AndLanguage (MonoPred_L A) SemanticsMono.andp.

#[export] Instance MonoPred_orpL (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: OrLanguage (MonoPred_L A) := Build_OrLanguage (MonoPred_L A) SemanticsMono.orp.

#[export] Instance MonoPred_falsepL (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: FalseLanguage (MonoPred_L A) := Build_FalseLanguage (MonoPred_L A) SemanticsMono.falsep.

#[export] Instance MonoPred_kiSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: KripkeIntuitionisticSemantics (MonoPred_L A) (Build_Model A) (tt: @Kmodel _ (unit_kMD (Build_Model A))) (MonoPred_SM A).
Proof.
  constructor.
  intros; apply (proj2_sig _).
Qed.

#[export] Instance MonoPred_kminSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: KripkeMinimumSemantics (MonoPred_L A) (Build_Model A) (tt: @Kmodel _ (unit_kMD (Build_Model A))) (MonoPred_SM A).
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

#[export] Instance MonoPred_kandpSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: KripkeAndSemantics (MonoPred_L A) (Build_Model A) (tt: @Kmodel _ (unit_kMD (Build_Model A))) (MonoPred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
Qed.

#[export] Instance MonoPred_korpSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: KripkeOrSemantics (MonoPred_L A) (Build_Model A) (tt: @Kmodel _ (unit_kMD (Build_Model A))) (MonoPred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
Qed.

#[export] Instance MonoPred_kfalsepSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: KripkeFalseSemantics (MonoPred_L A) (Build_Model A) (tt: @Kmodel _ (unit_kMD (Build_Model A))) (MonoPred_SM A).
Proof.
  constructor.
  + apply Same_set_refl.
Qed.

#[export] Instance MonoPred_Gamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation}:
  Provable (MonoPred_L A) :=
  Build_Provable _ (fun x: expr => forall a: A, proj1_sig x a).

#[export] Instance MonoPred_minAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: MinimumAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y ? ? m.
    pose proof @sound_modus_ponens (MonoPred_L A) _ (Build_Model A) (unit_kMD (Build_Model A)) tt R po_R (MonoPred_SM A) (MonoPred_kminSM A) x y.
    exact (H1 m (H m) (H0 m)).
  + intros x y.
    exact (@sound_axiom1 (MonoPred_L A) _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) x y).
  + intros x y z.
    exact (@sound_axiom2 (MonoPred_L A) _ (Build_Model A) (unit_kMD (Build_Model A)) tt R po_R (MonoPred_SM A) (MonoPred_kminSM A) x y z).
Qed.

#[export] Instance MonoPred_andpAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: AndAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_andp_intros (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_kandpSM A) x y).
  + intros x y.
    exact (@sound_provable_andp_elim1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kandpSM A) x y).
  + intros x y.
    exact (@sound_provable_andp_elim2 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kandpSM A) x y).
Qed.

#[export] Instance MonoPred_orpAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: OrAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_provable_orp_intros1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_korpSM A) x y).
  + intros x y.
    exact (@sound_provable_orp_intros2 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_korpSM A) x y).
  + intros x y z.
    exact (@sound_provable_orp_elim (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R po_R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_korpSM A) x y z).
Qed.

#[export] Instance MonoPred_falsepAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: FalseAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x.
    exact (@sound_provable_falsep_elim (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kfalsepSM A) x).
Qed.

#[export] Instance MonoPred_gdpAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {nkiM: NoBranchKripkeIntuitionisticModel A}: GodelDummettAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x y.
  exact (@sound_impp_choice_no_branch (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_korpSM A) nkiM x y).
Qed.
(*TODO: need to adjust(about DeMorgan and Classical)
#[export] Instance MonoPred_dmpAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {bkiM: BranchJoinKripkeIntuitionisticModel A}: DeMorganPropositionalAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_weak_excluded_middle_branch_join (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R po_R (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_kpSM A) bkiM x).
Qed.

#[export] Instance MonoPred_cpAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {ikiM: IdentityKripkeIntuitionisticModel A}: ClassicalPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_excluded_middle_ident (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) ikiM x).
Qed.
*)
