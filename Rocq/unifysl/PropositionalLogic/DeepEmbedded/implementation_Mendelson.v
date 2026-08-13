Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Countable.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MinimumLogic.Sound.Sound_Classical_Trivial.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Trivial.
Require Import Logic.PropositionalLogic.Complete.Truth_Trivial.
Require Import Logic.PropositionalLogic.Complete.Complete_Trivial.
Require Import Logic.PropositionalLogic.DeepEmbedded.interface_Mendelson.

(*********************************)
(*   Definitions                 *)
(*********************************)

Inductive expr: Type :=
  | impp : expr -> expr -> expr
  | negp : expr -> expr
  | varp : nat -> expr.

Declare Scope logic.
Local Open Scope logic.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : logic.
Notation "~~ x" := (negp x) (at level 35) : logic.

Inductive provable: expr -> Prop :=
| provables_modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| provable_axiom1: forall x y, provable (x --> (y --> x))
| provable_axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| provable_by_contradiction: forall x y, provable ((~~ x --> y) --> (~~ x --> ~~ y) --> x).

Definition model: Type := nat -> Prop.

Fixpoint denotation (x: expr): model -> Prop :=
  match x with
  | impp y z => fun m => (denotation y m) -> (denotation z m)
  | negp y => fun m => ~ (denotation y m)
  | varp p => fun m => m p
  end.

Definition valid (x: expr): Prop := forall m, denotation x m.

Definition sound: Prop := forall x, provable x -> valid x.

Definition complete: Prop := forall x, valid x -> provable x.

(*********************************)
(*   Proofs                      *)
(*********************************)

Module Lang <: LanguageSig.
  Definition expr := expr.
  Definition context := expr -> Prop.
  Definition provable := provable.
  Definition impp := impp.
  Definition negp := negp.
  Definition truep := varp 1 --> varp 1.
End Lang.

Module Rule <: PrimitiveRuleSig Lang.
Include DerivedNames Lang.
Definition provable_by_contradiction := provable_by_contradiction.
Definition provables_modus_ponens := provables_modus_ponens.
Definition provable_axiom1 := provable_axiom1.
Definition provable_axiom2 := provable_axiom2.
Definition impp_self2truep: exists x, truep = x --> x := ex_intro _ (varp 1) eq_refl.
End Rule.

Module Theorems := LogicTheorem Lang Rule.

#[export] Instance MD: Model :=
  Build_Model model.

#[export] Instance SM: Semantics Theorems.L MD :=
  Build_Semantics Theorems.L MD denotation.

#[export] Instance tminSM: TrivialMinimumSemantics Theorems.L MD SM.
Proof.
  constructor.
  simpl; intros.
  unfold Same_set, Included, Ensembles.In, Semantics.impp.
  firstorder.
Qed.

#[export] Instance negpSM: NegSemantics Theorems.L MD SM.
Proof.
  constructor.
  simpl; intros.
  unfold Same_set, Included, Ensembles.In, Semantics.negp.
  firstorder.
Qed.

Theorem soundness: sound.
Proof.
  hnf; intros.
  induction H.
  + exact (fun m => sound_modus_ponens x y m (IHprovable1 _) (IHprovable2 _)).
  + exact (fun m => sound_axiom1 x y m).
  + exact (fun m => sound_axiom2 x y z m).
  + exact (fun m => sound_by_contradiction x y m).
Qed.

Axiom expr_countable: Countable expr.

Definition cP: context -> Prop := maximal consistent.

Lemma AL_MC: at_least (maximal consistent) cP.
Proof. solve_at_least. Qed.

Lemma LIN_CONSI: Lindenbaum_constructable consistent cP.
Proof.
  eapply Lindenbaum_constructable_Same_set.
  + rewrite Same_set_spec.
    intros Phi.
    apply consistent_spec.
  + apply Lindenbaum_constructable_suffice.
    - apply expr_countable.
    - apply Lindenbaum_preserves_cannot_derive.
    - apply Lindenbaum_cannot_derive_ensures_max_consistent.
Qed.

Definition canonical_frame: Type := sig cP.

Definition canonical_eval: nat -> canonical_frame -> Prop :=
  fun p a => proj1_sig a (varp p).

#[export] Instance kMD: KripkeModel MD :=
  Build_KripkeModel MD
    unit (fun _ => canonical_frame) (fun u a v => canonical_eval v a).

Definition canonical_Kmodel: @Kmodel MD kMD := tt.

Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.

Import KripkeModelFamilyNotation.
Open Scope kripke_model.
Open Scope logic_base.

Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + exact (truth_lemma_impp cP rel AL_MC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_negp cP rel AL_MC x IHx).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.
  
Theorem completeness: complete.
Proof.
  assert (strongly_complete Theorems.GammaD SM
           (KripkeModelClass _ (fun _ => True))).
  2: {
    hnf; intros.
    specialize (H empty_context x).
    rewrite <- Minimum.__provable_derivable in H; apply H.
    hnf; intros.
    apply H0; auto.
  }
  apply (general_completeness _ rel LIN_CONSI TRUTH); auto.
Qed.
