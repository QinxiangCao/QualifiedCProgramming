Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Morphisms.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section ContextProperties.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}.

Definition context_sepcon (Phi Psi: context): context :=
  fun z => exists x y, z = x * y /\ Phi |--- x /\ Psi |--- y.

Definition context_sepcon_included_l (Phi2 Psi: context): context -> Prop :=
  fun Phi1 => Included _ (context_sepcon Phi1 Phi2) Psi.

Definition context_sepcon_included_r (Phi1 Psi: context): context -> Prop :=
  fun Phi2 => Included _ (context_sepcon Phi1 Phi2) Psi.

Context {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {wandL: WandLanguage L}
        {GammaPD: ProvableFromDerivable L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {fwSC: FiniteWitnessedSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}
        {GammaDP: DerivableFromProvable L GammaP GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization L GammaP}
        {wandAX: WandAxiomatization L GammaP}
        {sepcon_orp_AX: SepconOrAxiomatization L GammaP}
        {sepcon_falsep_AX: SepconFalseAxiomatization L GammaP}.

Lemma context_sepcon_derivable:
  forall (Phi Psi: context) z,
    context_sepcon Phi Psi |--- z ->
    exists x y, |-- x * y --> z /\ Phi |--- x /\ Psi |--- y.
Proof.
  clear iffpAX iffpSC truepL truepAX truepSC.
  intros.
  AddConnective_truep_impp_self.
  pose proof Axiomatization2SequentCalculus_truepSC as truepSC. (* TODO remove it *)
  rewrite __derivable_provable in H.
  destruct H as [xs [? ?]].
  revert z H0; induction H; intros.
  + exists TT, TT.
    split; [| split].
    - apply aux_minimun_rule00; auto.
    - apply derivable_truep_intros.
    - apply derivable_truep_intros.
  + pose proof provable_multi_imp_arg_switch1 l x z.
    pose proof provables_modus_ponens _ _ H2 H1.
    specialize (IHForall _ H3); clear H1 H2 H3.
    destruct H as [x' [y' [? [? ?]]]]; subst x.
    destruct IHForall as [x [y [? [? ?]]]].
    exists (x && x'), (y && y').
    split; [| split].
    - clear l H0 H1 H2 H3 H4.
      rewrite (provable_sepcon_andp_derives (x && x') y y').
      rewrite (provable_andp_sepcon_derives x x' y).
      rewrite (provable_andp_sepcon_derives x x' y').
      rewrite (provable_andp_elim1 (x * y) _).
      rewrite (provable_andp_elim2 _ (x' * y')).
      rewrite <- provable_impp_curry.
      auto.
    - apply derivables_andp_intros; auto.
    - apply derivables_andp_intros; auto.
Qed.

Lemma context_sepcon_consistent_rev_left:
  forall (Phi1 Phi2 Psi: context),
    Included _ (context_sepcon Phi1 Phi2) Psi ->
    consistent Psi ->
    consistent Phi1.
Proof.
  intros.
  rewrite consistent_spec in H0 |- *.
  intro; apply H0; clear H0.
  rewrite <- (provable_falsep_sepcon TT).
  apply derivable_assum.
  apply H; exists FF, TT; split; [| split]; auto.
  apply derivable_truep_intros.
Qed.

Lemma context_sepcon_included_l_derivable_subset_preserved: forall Phi2 Psi,
  derivable_subset_preserved (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  unfold context_sepcon_included_l.
  hnf; intros Phi1 Phi1' ? ?.
  eapply Included_trans; [clear Psi H0 | exact H0].
  unfold Included, Ensembles.In; intros z ?.
  destruct H0 as [x [y [? [? ?]]]].
  exists x, y; split; [| split]; auto.
  apply H; auto.
Qed.

Lemma context_sepcon_included_l_subset_preserved: forall Phi2 Psi,
  subset_preserved (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  apply derivable_subset_preserved_subset_preserved.
  apply context_sepcon_included_l_derivable_subset_preserved.
Qed.

Lemma context_sepcon_included_l_finite_captured: forall Phi2 Psi,
  finite_captured (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  unfold context_sepcon_included_l.
  hnf; intros.
  unfold Included, Ensembles.In; intros z ?.
  destruct H0 as [x [y [? [? ?]]]].
  apply derivable_finite_witnessed in H1.
  destruct H1 as [xs [? ?]].
  specialize (H _ H1).
  subst z.
  apply H; auto; unfold Ensembles.In.
  exists x, y; split; [| split]; auto.
Qed.

Lemma context_sepcon_included_l_context_orp_captured: forall Phi2 Psi
      (DC: derivable_closed Psi)
      (OW: orp_witnessed Psi),
  context_orp_captured (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  unfold context_sepcon_included_l.
  hnf; intros Phi1 Phi1' ?.
  assert (forall z1 z2,
            context_sepcon Phi1 Phi2 z1  ->
            ~ Psi z1 ->
            context_sepcon Phi1' Phi2 z2 ->
            ~ Psi z2 ->
            False) as HH.
  2: {
    clear - HH; unfold Included, Ensembles.In.
    apply NNPP; intro.
    apply not_or_and in H; destruct H.
    apply not_all_ex_not in H.
    apply not_all_ex_not in H0.
    destruct H as [z1 ?], H0 as [z2 ?].
    specialize (HH z1 z2).
    tauto.
  }
  intros.
  destruct H0 as [x1 [y1 [? [? ?]]]], H2 as [x2 [y2 [? [? ?]]]].
  subst z1 z2.
  assert (context_orp Phi1 Phi1' (x1 || x2));
  [| assert (context_sepcon (context_orp Phi1 Phi1') Phi2 ((x1 || x2) * (y1 && y2)));
     [| assert (Psi |--- (x1 * y1) || (x2 * y2))]].
  + exists x1, x2.
    split; [| split]; auto.
  + exists (x1 || x2), (y1 && y2).
    split; [| split]; auto.
    - apply derivable_assum; auto.
    - apply derivables_andp_intros; auto.
  + apply H in H2.
    apply derivable_assum in H2.
    rewrite provable_orp_sepcon in H2.
    rewrite (provable_andp_elim1 y1 y2) in H2 at 1.
    rewrite (provable_andp_elim2 y1 y2) in H2 at 1.
    auto.
  + rewrite <- derivable_closed_element_derivable in H8 by auto.
    apply OW in H8.
    tauto.
Qed.

Lemma wand_derivables_impp_theorem:
  forall (Phi: context) x y,
    context_sepcon Phi (Union _ empty_context (Singleton _ x)) |--- y <->
    Phi |--- x -* y.
Proof.
  intros.
  split; intros.
  + apply context_sepcon_derivable in H.
    destruct H as [x' [y' [? [? ?]]]].
    rewrite derivables_impp_theorem, <- __provable_derivable in H1.
    rewrite <- H1 in H.
    apply provables_wand_sepcon_adjoint in H.
    rewrite H in H0; auto.
  + rewrite <- (provable_wand_elim1 x y).
    apply derivable_assum.
    exists (x -* y), x.
    split; [| split]; auto.
    rewrite derivables_impp_theorem.
    apply derivable_impp_refl.
Qed.

Lemma context_sepcon_included_equiv: forall Phi Psi,
  derivable_closed Psi ->
  Same_set _ (context_sepcon_included_l Phi Psi) (context_sepcon_included_r Phi Psi).
Proof.
  intros.
  rewrite Same_set_spec; intros Phi'; split; intros.
  + hnf; intros.
    destruct H1 as [y [z [? [? ?]]]].
    subst x.
    apply H.
    rewrite <- provable_sepcon_comm_impp.
    apply derivable_assum.
    apply H0.
    exists z, y; split; [| split]; auto.
  + hnf; intros.
    destruct H1 as [y [z [? [? ?]]]].
    subst x.
    apply H.
    rewrite <- provable_sepcon_comm_impp.
    apply derivable_assum.
    apply H0.
    exists z, y; split; [| split]; auto.
Qed.

End ContextProperties.
