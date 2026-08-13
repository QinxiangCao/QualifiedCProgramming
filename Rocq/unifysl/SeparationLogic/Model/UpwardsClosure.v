Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Section UpwardsClosure.

Context {worlds: Type}
        {R: Relation worlds}
        {po_R: PreOrder Krelation}
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}
        {dSA: DownwardsClosedSeparationAlgebra worlds}.

(** *Upwards CLosure*)
Definition UpwardsClosure_J: Join worlds.
Proof. intros m1 m2 m; exact (exists n, n <= m /\ join m1 m2 n).
Defined.

Definition UpwardsClosure_SA:
  @SeparationAlgebra worlds (UpwardsClosure_J).
Proof.
  constructor.
  + intros.
    destruct H as [n [? ?]].
    exists n.
    split; auto.
    apply join_comm; auto.
  + intros.
    rename mx into mx', my into my', mz into mz'.
    destruct H as [mxy' [? ?]].
    destruct H0 as [mxyz' [? ?]].
    destruct (join_Korder_down _ _ _ _ mz' H2 H) as [mxyz'' [? ?]]; [reflexivity |].
    destruct (join_assoc _ _ _ _ _ H1 H3) as [myz' [? ?]].
    exists myz'.
    split.
    - exists myz'; split; auto.
      reflexivity.
    - exists mxyz''; split; auto.
      etransitivity; eauto.
Defined.

Definition UpwardsClosure_UpwardsClosed:
  @UpwardsClosedSeparationAlgebra worlds _ (UpwardsClosure_J).
Proof.
  intros until m2; intros.
  exists m1, m2.
  split; [| split]; [| reflexivity | reflexivity].
  destruct H as [n' [? ?]].
  exists n'.
  split; auto; etransitivity; eauto.
Defined.

Definition UpwardsClosure_DownwardsClosed:
  @DownwardsClosedSeparationAlgebra worlds _ (UpwardsClosure_J).
Proof.
  intros until n2; intros.
  simpl in *.
  destruct H as [n [? ?]].
  destruct (join_Korder_down _ _ _ _ _ H2 H0 H1) as [n' [? ?]].
  exists n; split; auto.
  exists n'; split; auto.
Defined.

End UpwardsClosure.
