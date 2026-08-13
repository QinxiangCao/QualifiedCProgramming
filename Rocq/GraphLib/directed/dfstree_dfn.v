Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.directed.rootedtree.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Coq.Logic.Classical.
Require Import Lia.

Record is_dfn {G1 G2 V E: Type} {pg1: Graph G1 V E} {pg2: Graph G2 V E} (g: G1) (dfstree: G2) (dfn: V -> nat) := {
    dfn_valid: forall x y, step dfstree x y -> dfn x < dfn y;
    subtree_segment: forall u v1 v2 x y, 
        step dfstree u v1 -> step dfstree u v2 ->
        reachable dfstree v1 x -> reachable dfstree v2 y -> 
        dfn v1 < dfn v2 
        -> dfn x < dfn y;
    no_cross_edge: forall u v1 v2 x y,
        step dfstree u v1 -> step dfstree u v2 ->
        reachable dfstree v1 x -> reachable dfstree v2 y -> 
        dfn v1 < dfn v2 ->
        ~ step g x y;
    dfn_unique: forall x y, dfn x = dfn y -> x = y;
}.

Section DFSTREE.

Context {G1 G2 V E: Type}
        {pg1: Graph G1 V E}
        {pg2: Graph G2 V E}
        {gv1: GValid G1}
        {gv2: GValid G2}
        {rootedtree: @RootedTree G2 V E pg2 gv2}
        (g: G1)
        (dfstree: G2)
        (sub: subgraph g dfstree)
        (dfn: V -> nat)
        (isdfn: is_dfn g dfstree dfn).

Lemma dfn_valid_offspring: forall x y, 
  offspring dfstree x y -> dfn x <= dfn y.
Proof.
  intros.
  unfold offspring, reachable in H.
  induction_1n H.
  lia.
  destruct isdfn.
  eapply dfn_valid0 in H0; eauto.
  apply IHrt in isdfn; auto.
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
    * apply isdfn; auto.
    * eapply IHrt in neq_x0y; eauto.
      apply isdfn in H1.
      lia.
Qed.

(* Definition dominate (w: V): V -> Prop := 
    fun v => forall p: vpath, p dfstree.root w -> In v p. *)
