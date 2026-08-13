Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ModelClass.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.Canonical_Kripke.
Require Import Logic.GeneralLogic.Complete.Complete_Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.MinimumLogic.Complete.Truth_Kripke.
Require Import Logic.MinimumLogic.Complete.Complete.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Truth_Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.
Require Import Logic.SeparationLogic.Complete.Lindenbaum_Flat.
Require Import Logic.SeparationLogic.Complete.Truth_Flat.
Require Import Logic.SeparationLogic.Complete.Canonical_Flat.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.DeepEmbedded.MinimumSeparationLogic_LibSupport.

Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

(***** Language *****)

Inductive expr: Type :=
  | impp : expr -> expr -> expr
  | andp : expr -> expr -> expr
  | sepcon : expr -> expr -> expr
  | varp : nat -> expr.

Declare Scope local_syntax.
Local Open Scope local_syntax.

Notation "x --> y" := (impp x y) (at level 55, right associativity) : local_syntax.
Notation "x && y" := (andp x y) (at level 40, left associativity) : local_syntax.
Notation "x * y" := (sepcon x y) (at level 40, left associativity) : local_syntax.

(***** Proof Theory *****)

Inductive provable: expr -> Prop :=
| provables_modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| provable_axiom1: forall x y, provable (x --> (y --> x))
| provable_axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| provable_andp_intros: forall x y, provable (x --> y --> x && y)
| provable_andp_elim1: forall x y, provable (x && y --> x)
| provable_andp_elim2: forall x y, provable (x && y --> y)
| provable_sepcon_comm_impp: forall x y, provable (x * y --> y * x)
| provable_sepcon_assoc1: forall x y z, provable (x * (y * z) --> (x * y) * z)
| provable_sepcon_mono: forall x1 x2 y1 y2,
    provable (x1 --> x2) -> provable (y1 --> y2) -> provable ((x1 * y1) --> (x2 * y2)).

(***** Semantics *****)

Record frame: Type := {
  underlying_set:> Type;
  underlying_relation: relation underlying_set;
  underlying_join: Join underlying_set
}.

Declare Scope TheKripkeSemantics.
Infix "<=" := (underlying_relation _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

Definition sem (f: frame) := @Ensemble (underlying_set f).

Definition denotation (F: frame) (eval: nat -> sem F): expr -> sem F :=
  fix denotation (x: expr): sem F:=
  match x with
  | impp y z => @Semantics.impp F (underlying_relation F) (denotation y) (denotation z)
  | andp y z => @Semantics.andp F (denotation y) (denotation z)
  | sepcon y z => @WeakSemantics.sepcon F (underlying_join F) (denotation y) (denotation z)
  | varp p => eval p
  end.

Record Kmodel : Type := {
  underlying_frame :> frame;
  sem_var: nat -> sem underlying_frame
}.

Record model: Type := {
  underlying_model :> Kmodel;
  elm: underlying_model
}.

Record well_formed (m: Kmodel): Prop := {
  WF_Monotonic:
    forall v: nat, @upwards_closed_Kdenote _ (underlying_relation m) (sem_var m v);
  WF_PreOrder:
    PreOrder (@Krelation _ (underlying_relation m));
  WF_SeparationAlgebra:
    @SeparationAlgebra _ (underlying_join m);
  WF_UpwardsClosed:
    @UpwardsClosedSeparationAlgebra _ (underlying_relation m) (underlying_join m);
  WF_DownwardsClosed:
    @DownwardsClosedSeparationAlgebra _ (underlying_relation m) (underlying_join m)
}.

Definition satisfy (m: model) (x: expr): Prop :=
  denotation m (sem_var m) x (elm m).

Definition valid (x: expr): Prop :=
  forall m: model, well_formed m -> satisfy m x.

Definition sound: Prop := forall x, provable x -> valid x.

Definition complete: Prop := forall x, valid x -> provable x.

(***** Auxiliary *****)

Module Lang <: LanguageSig.
  Definition expr := expr.
  Definition context := expr -> Prop.
  Definition provable := provable.
  Definition impp := impp.
  Definition andp := andp.
  Definition sepcon := sepcon.
End Lang.

Module Rule <: PrimitiveRuleSig Lang.
Include DerivedNames Lang.
Definition provables_modus_ponens := provables_modus_ponens.
Definition provable_axiom1 := provable_axiom1.
Definition provable_axiom2 := provable_axiom2.
Definition provable_andp_intros := provable_andp_intros.
Definition provable_andp_elim1 := provable_andp_elim1.
Definition provable_andp_elim2 := provable_andp_elim2.
Definition provable_sepcon_comm_impp := provable_sepcon_comm_impp.
Definition provable_sepcon_assoc1 := provable_sepcon_assoc1.
Definition provable_sepcon_mono := provable_sepcon_mono.
End Rule.

Module Theorems := LogicTheorem Lang Rule.

#[export] Instance MD: Model :=
  Build_Model model.

#[export] Instance kMD: KripkeModel MD :=
  Build_KripkeModel _
    Kmodel
    (fun M => M)
    (fun M m => Build_model M m).

#[export] Instance SM: Semantics Theorems.L MD :=
  Build_Semantics Theorems.L MD (fun x m => denotation m (sem_var m) x (elm m)).

#[export] Instance R (M: Kmodel): Relation (Kworlds M) :=
  @underlying_relation M.

#[export] Instance J (M: Kmodel): Join (Kworlds M) :=
  @underlying_join M.

#[export] Instance kminSM (M: Kmodel): KripkeMinimumSemantics Theorems.L MD M SM.
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

#[export] Instance andpSM (M: Kmodel): KripkeAndSemantics Theorems.L MD M SM.
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

#[export] Instance fsepconSM (M: Kmodel): SepconSemantics Theorems.L MD M SM.
Proof.
  hnf; intros; apply Same_set_refl.
Qed.

Definition Kmodel_Monotonic: Kmodel -> Prop := fun M =>
  forall v: nat, upwards_closed_Kdenote (sem_var M v).

Definition Kmodel_PreOrder: Kmodel -> Prop := fun M =>
  PreOrder (@Krelation _ (R M)).

Definition Kmodel_SeparationAlgebra: Kmodel -> Prop := fun M =>
  SeparationAlgebra (Kworlds M).

Definition Kmodel_UpwardsClosed: Kmodel-> Prop := fun M =>
  UpwardsClosedSeparationAlgebra (Kworlds M).

Definition Kmodel_DownwardsClosed: Kmodel -> Prop := fun M =>
  DownwardsClosedSeparationAlgebra (Kworlds M).

(***** Completeness *****)

Section Complete.

Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.
Local Open Scope logic_base.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.

Context {CV: Countable expr}.

Definition cP : context -> Prop :=
  derivable_closed.

Lemma AL_DC: at_least derivable_closed cP.
Proof. solve_at_least. Qed.

Lemma LIN_CD: forall x: expr, Lindenbaum_constructable (cannot_derive x) cP.
Proof.
  intros.
  apply Lindenbaum_constructable_suffice; auto.
  + apply Lindenbaum_preserves_cannot_derive.
  + unfold cP.
    repeat apply Lindenbaum_ensures_by_conjunct.
    apply Lindenbaum_cannot_derive_ensures_derivable_closed.
Qed.

Lemma LIN_SL: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_l Phi (proj1_sig Psi)) cP.
Proof.
  intros.
  apply Lindenbaum_constructable_suffice; auto.
  + apply Lindenbaum_preserves_context_sepcon_included_l.
  + unfold cP.
    repeat apply Lindenbaum_ensures_by_conjunct.
    apply Lindenbaum_context_sepcon_included_l_ensures_derivable_closed.
Qed.

Lemma LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP.
Proof.
  intros.
  eapply Lindenbaum_constructable_Same_set.
  + symmetry.
    apply context_sepcon_included_equiv.
    apply AL_DC, (proj2_sig Psi).
  + apply LIN_SL.
Qed.

Definition canonical_frame: frame :=
  Build_frame (sig cP)
    (fun a b => Included _ (proj1_sig a) (proj1_sig b))
    (fun a b c => Included _ (context_sepcon (proj1_sig a) (proj1_sig b)) (proj1_sig c)).

Definition canonical_eval: nat -> sem canonical_frame :=
  fun p a => proj1_sig a (varp p).

Definition canonical_Kmodel: @Base.Kmodel MD kMD :=
  Build_Kmodel canonical_frame canonical_eval.

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

Definition H_J:
  forall m1 m2 m Phi1 Phi2 Phi, rel m1 Phi1 -> rel m2 Phi2 -> rel m Phi ->
    (join m1 m2 m <-> Included _ (context_sepcon (proj1_sig Phi1) (proj1_sig Phi2)) (proj1_sig Phi)).
Proof.
  intros.
  change (m = Phi) in H1.
  change (m1 = Phi1) in H.
  change (m2 = Phi2) in H0.
  subst; reflexivity.
Qed.

Lemma TRUTH:
  forall x: expr , forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + exact (truth_lemma_impp cP rel H_R AL_DC LIN_CD x1 x2 IHx1 IHx2).
  + exact (truth_lemma_andp cP rel AL_DC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_sepcon cP rel H_J AL_DC LIN_SL LIN_SR x1 x2 IHx1 IHx2).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.

Theorem completeness: complete.
Proof.
  assert (Same_set model well_formed (KripkeModelClass _ well_formed)).
  {
    apply (@KripkeModelClass_ModelClass_Same_set_spec MD).
    intros.
    destruct m as [M w].
    simpl.
    split; intros; [eauto |].
    destruct H as [? [? [? ?]]].
    inversion H0.
    subst; auto.
  }
  pose proof @strongly_complete_strong _ _ _ _ _ _ well_formed.
  pose proof @general_completeness _ _ _ _ _ canonical_Kmodel _ well_formed cP rel LIN_CD TRUTH.
  apply H0.
  rewrite H.
  apply H1.
  clear H H0 H1.
  constructor.
  + hnf; intros.
    exact (denote_monotonic cP rel H_R
             (varp v)
             (TRUTH (varp v))).
  + exact (po_R cP rel H_R).
  + exact (SA cP rel H_J AL_DC LIN_SR).
  + exact (uSA cP rel H_R H_J AL_DC).
  + exact (dSA cP rel H_R H_J AL_DC).
Qed.

End Complete.
