Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import SetsClass.SetsClass.

Section UNDIRECTED.

Context {G: Type}
        {V: Type}
        {E: Type}
        {g: G}
        {graph: Graph G V E}
        {gv: GValid G}
        {undirectedgraph: UndirectedGraph G V E}
        {stepuniqueundirected: StepUniqueUndirected G V E}.

Lemma step_sym': forall x y,
  step g x y -> step g y x.
Proof.
  intros x y H.
  unfold step in *.
  destruct H as [e H].
  exists e; auto.
  eapply step_sym; eauto.
Qed.   

Lemma reachable_sym: forall x y,
  reachable g x y -> reachable g y x.
Proof.
  intros.
  unfold reachable in *.
  induction_1n H.
  - reflexivity.
  - transitivity_n1 x0; auto.
    eapply step_sym'; eauto.
Qed.

Lemma reachable_without_sym: forall e x y,
  reachable_without g e x y -> reachable_without g e y x.
Proof.
  intros e x y H.
  unfold reachable_without in *.
  induction_1n H.
  - reflexivity.
  - etransitivity; eauto.
    transitivity_1n x; auto.
    2: reflexivity.
    destruct H0 as [e0 [? ?]].
    exists e0; split; auto.
    apply step_sym; auto.
Qed.

Lemma reachable_gt_sym (P: V -> Prop): forall x y, P x -> 
  reachable_tl P g x y -> 
  reachable_tl P g y x.
Proof.
  intros x y gt H.
  unfold reachable_tl in *.
  induction_1n H.
  - reflexivity.
  - destruct H0 as [? ?].
    etransitivity; eauto.
    transitivity_1n x; auto.
    2: reflexivity.
    split; auto.
    apply step_sym'; auto.
Qed.

Lemma step_aux_eunique_l
  {g_valid: gvalid g}: 
  forall u x y e, 
  step_aux g e u x -> 
  step_aux g e u y -> 
  x = y.
Proof.
  intros.
  eapply step_aux_unique_undirected in H; eauto.
  destruct H as [[]|[]]; subst; auto.
Qed.

Lemma step_aux_eunique_r
  {g_valid: gvalid g}: 
  forall v x y e, 
  step_aux g e x v -> 
  step_aux g e y v -> 
  x = y.
Proof.
  intros.
  eapply step_aux_unique_undirected in H; eauto.
  destruct H as [[]|[]]; subst; auto.
Qed.

(* Lemma bridge_sym: forall x y,
  is_bridge g x y -> is_bridge g y x.
Proof.
  intros.
  unfold is_bridge in *.
  intros.
  apply step_sym in H0.
  unfold not; intros.
  apply H in H0.
  apply H0.
  apply reachable_without_sym; auto.
Qed. *)

End UNDIRECTED.
