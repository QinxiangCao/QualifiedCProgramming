Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Module EmpSemantics.

Definition emp {worlds: Type} {U: Unit worlds}: Ensemble worlds := is_unit.

Lemma emp_closed
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {U: Unit worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}
      {UJORel: UnitJoinOrderRelation worlds}:
  upwards_closed_Kdenote emp.
Proof.
  intros.
  hnf; intros.
  hnf in H0 |- *.
  eapply mono_unit; eauto.
Qed.

End EmpSemantics.

Module EmpSemanticsMono.

Program Definition emp
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {U: Unit worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}
      {UJORel: UnitJoinOrderRelation worlds}: MonoEnsemble worlds :=
  EmpSemantics.emp.
Next Obligation.
  apply (@EmpSemantics.emp_closed worlds R po_R J U SA dSA UJORel);
  apply (proj2_sig _).
Defined.

End EmpSemanticsMono.