Require Import Coq.Classes.Morphisms.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ShallowEmbedded.ModelLanguage.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.Extensions.ProofTheory.Stable.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section Join2CorableStable.

Context {M : Model} {J : Join model}.

Lemma CorableDefinition_Join2ImpStable
      {minL : MinimumLanguage Model_L}
      {imppDef_model : ImppDefinition_Model minL}
      {Cor : Corable Model_L}
      {corableDef_join : CorableDefinition_Join Cor}:
  @ImpStable Model_L minL (@corable Model_L Cor).
Proof.
  constructor.
  intros x y Hx Hy.
  rewrite (join2corable x) in Hx.
  rewrite (join2corable y) in Hy.
  rewrite (join2corable (x --> y)).
  rewrite model2impp.
  simpl. intros m1 m2 m Hjoin.
  split; intros Himp Hxm.
  - apply (proj1 (Hy m1 m2 m Hjoin)).
    apply Himp.
    apply (proj2 (Hx m1 m2 m Hjoin)).
    exact Hxm.
  - apply (proj2 (Hy m1 m2 m Hjoin)).
    apply Himp.
    apply (proj1 (Hx m1 m2 m Hjoin)).
    exact Hxm.
Qed.

Lemma Join2Corable_ImpStable:
  @ImpStable Model_L Model2Impp (@corable Model_L Join2Corable).
Proof.
  apply (@CorableDefinition_Join2ImpStable
    _ Model2Impp_Normal _ Join2Corable_Normal).
Qed.

Lemma CorableDefinition_Join2AndStable
      {andpL : AndLanguage Model_L}
      {andpDef_model : AndpDefinition_Model andpL}
      {Cor : Corable Model_L}
      {corableDef_join : CorableDefinition_Join Cor}:
  @AndStable Model_L andpL (@corable Model_L Cor).
Proof.
  constructor.
  intros x y Hx Hy.
  rewrite (join2corable x) in Hx.
  rewrite (join2corable y) in Hy.
  rewrite (join2corable (x && y)).
  rewrite model2andp.
  simpl. intros m1 m2 m Hjoin.
  split; intros [Hxm Hym]; split.
  - apply (proj1 (Hx m1 m2 m Hjoin)); exact Hxm.
  - apply (proj1 (Hy m1 m2 m Hjoin)); exact Hym.
  - apply (proj2 (Hx m1 m2 m Hjoin)); exact Hxm.
  - apply (proj2 (Hy m1 m2 m Hjoin)); exact Hym.
Qed.

Lemma  Join2Corable_AndStable:
  @AndStable Model_L Model2Andp (@corable Model_L Join2Corable).
Proof.
  apply (@CorableDefinition_Join2AndStable
    _ Model2Andp_Normal _ Join2Corable_Normal).
Qed.

Lemma CorableDefinition_Join2OrStable
      {orpL : OrLanguage Model_L}
      {orpDef_model : OrpDefinition_Model orpL}
      {Cor : Corable Model_L}
      {corableDef_join : CorableDefinition_Join Cor}:
  @OrStable Model_L orpL (@corable Model_L Cor).
Proof.
  constructor.
  intros x y Hx Hy.
  rewrite (join2corable x) in Hx.
  rewrite (join2corable y) in Hy.
  rewrite (join2corable (x || y)).
  rewrite model2orp.
  simpl. intros m1 m2 m Hjoin.
  split; intros [Hxm | Hym].
  - left. apply (proj1 (Hx m1 m2 m Hjoin)); exact Hxm.
  - right. apply (proj1 (Hy m1 m2 m Hjoin)); exact Hym.
  - left. apply (proj2 (Hx m1 m2 m Hjoin)); exact Hxm.
  - right. apply (proj2 (Hy m1 m2 m Hjoin)); exact Hym.
Qed.

Lemma Join2Corable_OrStable:
  @OrStable Model_L Model2Orp (@corable Model_L Join2Corable).
Proof.
  apply (@CorableDefinition_Join2OrStable
    _ Model2Orp_Normal _ Join2Corable_Normal).
Qed.

Lemma CorableDefinition_Join2FalseStable
      {falsepL : FalseLanguage Model_L}
      {falsepDef_model : FalsepDefinition_Model falsepL}
      {Cor : Corable Model_L}
      {corableDef_join : CorableDefinition_Join Cor}:
  @FalseStable Model_L falsepL (@corable Model_L Cor).
Proof.
  constructor.
  rewrite (join2corable FF).
  rewrite model2falsep.
  simpl. intros m1 m2 m Hjoin; split; intros H; contradiction.
Qed.

Lemma Join2Corable_FalseStable:
  @FalseStable Model_L Model2Falsep (@corable Model_L Join2Corable).
Proof.
  apply (@CorableDefinition_Join2FalseStable
    _ Model2Falsep_Normal _ Join2Corable_Normal).
Qed.

Context {J_SA : SeparationAlgebra model}
        {U : Unit model}
        {UJR : UnitJoinRelation model}.

Lemma CorableDefinition_Join2SeparationStable
      {Cor : Corable Model_L}
      {corableDef_join : CorableDefinition_Join Cor}:
  @SeparationStable
    Model_L Join2Sepcon Join2Wand
    (@corable Model_L Cor).
Proof.
  constructor.
  - intros x y Hx Hy.
    rewrite (join2corable x) in Hx.
    rewrite (join2corable y) in Hy.
    rewrite (join2corable (x * y)).
    unfold sepcon, Join2Sepcon.
    simpl. intros m1 m2 m Hjoin.
    split; intros Hsep.
    + destruct Hsep as [mx [my [Hxy [Hx_mx Hy_my]]]].
      destruct (join_assoc mx my m2 m1 m Hxy Hjoin)
        as [my2 [Hmy2 Hx_my2]].
      exists mx, my2.
      split; [exact Hx_my2 |].
      split; [exact Hx_mx |].
      apply (proj1 (Hy my m2 my2 Hmy2)).
      exact Hy_my.
    + destruct Hsep as [mx [my [Hxy [Hx_mx Hy_my]]]].
      destruct (unit_join m1) as [u [Hu Hunit]].
      exists m1, u.
      split; [exact Hunit |].
      split.
      * apply (proj2 (Hx m1 m2 m Hjoin)).
        apply (proj1 (Hx mx my m Hxy)).
        exact Hx_mx.
      * apply (proj2 (Hy u m1 m1 (join_comm m1 u m1 Hunit))).
        apply (proj2 (Hy m1 m2 m Hjoin)).
        apply (proj1 (Hy my mx m (join_comm mx my m Hxy))).
        exact Hy_my.
  - intros x y Hx Hy.
    rewrite (join2corable x) in Hx.
    rewrite (join2corable y) in Hy.
    rewrite (join2corable (x -* y)).
    unfold wand, Join2Wand.
    simpl. intros m1 m2 m Hjoin.
    split; intros Hwand mx my Hext Hx_mx.
    + destruct (join_assoc m1 m2 mx m my Hjoin Hext)
        as [m2x [Hm2x Hm1_m2x]].
      eapply Hwand.
      * exact Hm1_m2x.
      * apply (proj1 (Hx mx m2 m2x (join_comm m2 mx m2x Hm2x))).
        exact Hx_mx.
    + destruct (unit_join m) as [u [Hu Hunit]].
      apply (proj1 (Hy m1 mx my Hext)).
      apply (proj2 (Hy m1 m2 m Hjoin)).
      eapply Hwand.
      * exact Hunit.
      * apply (proj2 (Hx u m m (join_comm m u m Hunit))).
        apply (proj1 (Hx m1 m2 m Hjoin)).
        apply (proj2 (Hx m1 mx my Hext)).
	        apply (proj1 (Hx mx m1 my (join_comm m1 mx my Hext))).
	        exact Hx_mx.
Qed.

Lemma Join2Corable_SeparationStable:
  @SeparationStable
    Model_L Join2Sepcon Join2Wand
    (@corable Model_L Join2Corable).
Proof.
  apply (CorableDefinition_Join2SeparationStable
    (Cor := Join2Corable)
    (corableDef_join := Join2Corable_Normal)).
Qed.

End Join2CorableStable.
