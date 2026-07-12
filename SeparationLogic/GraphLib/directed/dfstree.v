Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.directed.rootedtree.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Coq.Logic.Classical.
Require Import Lia.

Definition dfn_valid {G V E: Type} {pg: Graph G V E} (dfstree: G) (dfn: V -> nat) := 
   forall x y, step dfstree x y -> dfn x < dfn y.

Section DFN.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {dfstree: G}
        {dfn: V -> nat}
        {dfnv: dfn_valid dfstree dfn}.

Lemma dfn_valid_offspring: forall x y, 
  offspring dfstree x y -> dfn x <= dfn y.
Proof.
  intros.
  unfold offspring, reachable in H.
  induction_1n H.
  lia.
  eapply dfnv in H0; eauto.
  apply IHrt in dfnv.
  lia.
Qed.
      
Lemma dfn_valid_offspring': forall x y, 
  x <> y -> 
  offspring dfstree x y -> dfn x < dfn y.
Proof.
  intros.
  unfold offspring, reachable in H0.
  induction_1n H0.
  - exfalso; auto.
  - destruct_equality_impl x0 y.
    eapply IHrt in neq_x0y; eauto.
    apply dfnv in H1.
    lia.
Qed.


Lemma offspring_reachable_gt : forall x y: V,
  offspring dfstree x y -> 
  reachable_dfn_gt dfn (dfn x) dfstree x y.
Proof.
  intros x y H.
  unfold reachable_dfn_gt.
  unfold reachable_tl.
  unfold offspring, reachable in H.
  induction_1n H.
  + reflexivity.
  + transitivity x0; auto.
    * apply step_tl_rt; auto.
      destruct H0 as [e ?].
      split; auto.
      ** exists e. auto.
      ** apply step_trivial in H0.
         apply dfnv in H0. lia.
    * pose proof IHrt dfnv.
    apply dfnv in H0.
    remember (dfn x0) as z.
    apply PeanoNat.Nat.lt_le_incl in H0.
    eapply reachable_gt_mono; eauto.
Qed.


End DFN.
