Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.DownwardsSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Sound_Downwards.

Context {L: Language}
        {minL: MinimumLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {MD: Model}
        {kMD: KripkeModel MD}
        (M: Kmodel)
        {R: Relation (Kworlds M)}
        {po_R: PreOrder Krelation}
        {J: Join (Kworlds M)}
        {U: Unit (Kworlds M)}
        {SA: SeparationAlgebra (Kworlds M)}
        {dSA: DownwardsClosedSeparationAlgebra (Kworlds M)}
        {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD M SM}
        {kminSM: KripkeMinimumSemantics L MD M SM}
        {kiffpSM: KripkeIffSemantics L MD M SM}
        {dsepconSM: DownwardsSemantics.SepconSemantics L MD M SM}
        {dwandSM: DownwardsSemantics.WandSemantics L MD M SM}.

Lemma sound_sepcon_comm:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= x * y --> y * x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H0 |- *; intros.
  destruct H0 as [m0 [m1 [m2 [? [? [? ?]]]]]].
  exists m0, m2, m1.
  split; [| split]; auto.
  apply join_comm; auto.
Qed.

Lemma sound_sepcon_assoc:
  forall x y z: expr,
    forall m,
      KRIPKE: M, m |= x * (y * z) <--> (x * y) * z.
Proof.
  intros.
  apply sat_iffp.
  split; intros.
  + rewrite sat_sepcon in H0.
    destruct H0 as [n' [mx' [myz' [? [? [? ?]]]]]].
    rewrite sat_sepcon in H3.
    destruct H3 as [myz'' [my'' [mz'' [? [? [? ?]]]]]].
    apply join_comm in H1.
    apply join_comm in H4.
    assert (mx' <= mx') by reflexivity.
    destruct (join_Korder_down _ _ _ _ _ H1 H3 H7) as [n'' [? ?]].
    destruct (join_assoc mz'' my'' mx' myz'' n'' H4 H8) as [mxy'' [? ?]].
    apply join_comm in H10.
    apply join_comm in H11.
    rewrite sat_sepcon.
    exists n'', mxy'', mz''.
    split; [| split; [| split]]; auto.
    - etransitivity; eauto.
    - rewrite sat_sepcon.
      exists mxy'', mx', my''.
      split; [| split; [| split]]; auto.
      reflexivity.
  + rewrite sat_sepcon in H0.
    destruct H0 as [n' [mxy' [mz' [? [? [? ?]]]]]].
    rewrite sat_sepcon in H2.
    destruct H2 as [mxy'' [mx'' [my'' [? [? [? ?]]]]]].
    assert (mz' <= mz') by reflexivity.
    destruct (join_Korder_down _ _ _ _ _ H1 H2 H7) as [n'' [? ?]].
    destruct (join_assoc mx'' my'' mz' mxy'' n'' H4 H8) as [myz'' [? ?]].
    rewrite sat_sepcon.
    exists n'', mx'', myz''.
    split; [| split; [| split]]; auto.
    - etransitivity; eauto.
    - rewrite sat_sepcon.
      exists myz'', my'', mz'.
      split; [| split; [| split]]; auto.
      reflexivity.
Qed.

Lemma sound_provables_wand_sepcon_adjoint:
  forall x y z: expr,
   (forall m, KRIPKE: M, m |= x * y --> z) <-> (forall m, KRIPKE: M, m |= x --> (y -* z)).
Proof.
  intros.
  split; intro.
  + assert (ASSU: forall m0 m1 m2 m, m0 <= m -> join m1 m2 m0 -> KRIPKE: M, m1 |= x -> KRIPKE: M, m2 |= y -> KRIPKE: M, m |= z).
    {
      intros.
      specialize (H m).
      rewrite sat_impp in H.
      apply (H m); [reflexivity |].
      rewrite sat_sepcon.
      exists m0, m1, m2; auto.
    }
    clear H.
    intros.
    rewrite sat_impp; intros.
    rewrite sat_wand; intros.
    apply (ASSU m2 n m1 m2); auto.
    reflexivity.
  + assert (ASSU: forall m1 m2 m, join m m1 m2 -> KRIPKE: M, m |= x -> KRIPKE: M, m1 |= y -> KRIPKE: M, m2 |= z).
    {
      intros.
      specialize (H m).
      rewrite sat_impp in H.
      revert m1 m2 H0 H2.
      rewrite <- sat_wand.
      apply (H m); [reflexivity | auto].
    }
    intros.
    rewrite sat_impp; intros.
    rewrite sat_sepcon in H1.
    destruct H1 as [m0 [m1 [m2 [? [? [? ?]]]]]].
    pose proof (ASSU m2 m0 m1 H2 H3 H4).
    eapply sat_mono; eauto.
Qed.

Lemma sound_provable_sepcon_mono:
  forall x1 x2 y1 y2: expr,
   (forall m, KRIPKE: M, m |= x1 --> x2) ->
   (forall m, KRIPKE: M, m |= y1 --> y2) ->
   (forall m, KRIPKE: M, m |= x1 * y1 --> x2 * y2).
Proof.
  intros.
  assert (ASSUx: forall m, KRIPKE: M, m |= x1 -> KRIPKE: M, m |= x2).
  {
    intros.
    specialize (H m0).
    rewrite sat_impp in H.
    apply (H m0); [reflexivity | auto].
  }
  assert (ASSUy: forall m, KRIPKE: M, m |= y1 -> KRIPKE: M, m |= y2).
  {
    intros.
    specialize (H0 m0).
    rewrite sat_impp in H0.
    apply (H0 m0); [reflexivity | auto].
  }
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H2 |- *.
  destruct H2 as [m0 [m1 [m2 [? [? [? ?]]]]]].
  exists m0, m1, m2; auto.
Qed.

Lemma sound_provable_sepcon_elim1 {incrSA: IncreasingSeparationAlgebra (Kworlds M)}:
  forall x y: expr,
    forall m, KRIPKE: M, m |= x * y --> x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H0.
  destruct H0 as [m0 [m1 [m2 [? [? [? ?]]]]]].
  apply join_comm in H1.
  apply all_increasing in H1.
  eapply sat_mono; eauto.
  eapply sat_mono; eauto.
Qed.

Context {empL: EmpLanguage L}
        {dempSM: DownwardsSemantics.EmpSemantics L MD M SM}.

Lemma sound_sepcon_emp {UJO_Rel: UnitJoinOrderRelation (Kworlds M)}:
  forall x: expr,
    forall m, KRIPKE: M, m |= x * emp <--> x.
Proof.
  intros.
  apply sat_iffp.
  split; intros.
  + clear m H.
    rewrite sat_sepcon in H0.
    destruct H0 as [m'' [m' [u [? [? [? ?]]]]]].
    rewrite sat_emp in H2.
    pose proof unit_join_order_min_2 _ _ _ H2 H0.
    eapply sat_mono; eauto.
    eapply sat_mono; eauto.
  + rewrite sat_sepcon.
    pose proof unit_join_order_min_1 n.
    destruct H1 as [m1 [m2 [? [? ?]]]].
    exists n, m1,m2.
    split; [| split; [| split]]; auto.
    - reflexivity.
    - eapply sat_mono; eauto.
    - rewrite sat_emp.
      auto.
Qed.

End Sound_Downwards.
