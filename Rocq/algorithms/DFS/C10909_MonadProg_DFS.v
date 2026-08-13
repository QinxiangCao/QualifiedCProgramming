(* COQ-HEAD *)

Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
(* /COQ-HEAD *)

Theorem Hoare_normalize {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall s0, P s0 -> Hoare (fun s => s = s0) f Q) ->
    Hoare P f Q.
Proof.
  unfold Hoare. intros.
  revert H1.
  apply (H s1); tauto.
Qed.

Theorem Hoare_normal_assume_bind {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q: A -> Σ -> Prop) s0,
    (P s0 -> Hoare (fun s => s = s0) f Q) ->
    (Hoare (fun s => s = s0) (assume P;; f) Q).
Proof.
  intros.
  apply Hoare_assume_bind.
  apply Hoare_normalize.
  intros.
  destruct H0.
  subst; tauto.
Qed.

Theorem Hoare_normal_LFix {Σ A B: Type}:
  forall (Q: A -> Σ -> B -> Σ -> Prop)
         (f: (A -> StateRelMonad.M Σ B) -> (A -> StateRelMonad.M Σ B)),
    (forall (W: A -> StateRelMonad.M Σ B),
       (forall s0 a, Hoare (fun s => s = s0) (W a) (Q a s0)) ->
       (forall s0 a, Hoare (fun s => s = s0) (f W a) (Q a s0))) ->
    (forall s0 a, Hoare (fun s => s = s0) (Lfix f a) (Q a s0)).
Proof.
  intros.
  unfold Hoare.
  intros s1 b s2 ? ?.
  change (exists n, (s1, b, s2) ∈ Nat.iter n f ∅ a) in H1.
  destruct H1 as [n ?].
  revert s1 b s2 H0 H1.
  change (Hoare (fun s => s = s0) (Nat.iter n f ∅ a) (Q a s0)).
  revert s0 a.
  induction n.
  + unfold Hoare; simpl; sets_unfold; tauto.
  + simpl.
    apply H.
    apply IHn.
Qed.

Section DFS.

Context {G V E: Type}
        `{graph: Graph G V E} 
        `{gv: GValid G}
        `{step_aux_unique_undirected: StepUniqueUndirected G V E}
        (g: G)
        (g_valid: gvalid g).

Lemma step_aux_end_unique: 
  forall e u v1 v2, 
    step_aux g e u v1 -> 
    step_aux g e u v2 ->
    v1 = v2.
Proof.
  intros.
  eapply step_aux_unique_undirected in H; eauto.
  destruct H as [[]|[]]; subst; auto.
Qed.

Definition state: Type := V -> Prop.

Definition visit (u: V): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    s2 == s1 ∪ Sets.singleton u.

Definition DFS_rec_f
             (W: V -> StateRelMonad.M state unit)
             (u: V): StateRelMonad.M state unit :=
  visit u;;
  repeat_break
    (fun e_set =>
       choice
         (e <- any E;;
          v <- any V;;
          assume (fun _ => ~ e ∈ e_set);;
          assume (fun s => ~ v ∈ s);;
          assume (fun _ => step_aux g e u v);;
          W v;;
          continue (e_set ∪ Sets.singleton e))
         (assume (fun s =>
                    forall (e:E) (v:V),
                      step_aux g e u v ->
                      e ∈ e_set \/ v ∈ s);;
          break tt))
  ∅.

Definition DFS (u: V): StateRelMonad.M state unit :=
  Lfix (DFS_rec_f) u.

Definition neighbor_visited (s: state) (u: V): Prop :=
  forall v: V, step g u v -> v ∈ s.

Lemma neighbor_visited_incl:
  forall s1 s2 u,
    s1 ⊆ s2 ->
    neighbor_visited s1 u ->
    neighbor_visited s2 u.
Proof.
  unfold neighbor_visited.
  intros.
  rewrite <- H.
  revert H1.
  apply H0.
Qed.

Lemma Hoare_visit:
  forall s0 u P,
    (forall s1,
       s1 == s0 ∪ Sets.singleton u ->
       P s1) ->
    Hoare (fun s => s = s0) (visit u) (fun _ => P).
Proof.
  intros.
  unfold Hoare; sets_unfold; unfold visit; simpl.
  intros.
  subst s1.
  apply H.
  tauto.
Qed.

(* 尝试不写成这种形式。 *)
(* 已经访问过的顶点集合是单调递增的 *)
Theorem DFS_rec_visited_incr:
  forall W,
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (W u)
         (fun _ s => s0 ⊆ s)) ->
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (DFS_rec_f W u)
         (fun _ s => s0 ⊆ s)).
Proof.
  intros.
  unfold DFS_rec_f.
  eapply Hoare_bind;
    [| intros;
       apply (Hoare_repeat_break _ 
                (fun _ s => s0 ⊆ s))].
  { apply Hoare_visit.
    intros; subst.
    rewrite H0; sets_unfold; tauto. }
  intros e_set.
  apply Hoare_normalize.
  intros s1 ?.
  apply Hoare_choice.
  + apply Hoare_any_bind.
    intros e.
    apply Hoare_any_bind.
    intros v.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    eapply Hoare_bind; [apply H |].
    simpl; intros _.
    apply Hoare_ret'.
    intros s ?.
    rewrite <- H4.
    tauto.
  + apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_ret'.
    intros.
    subst.
    tauto.
Qed.

(* 尝试不写成这种形式 *)
(* DFS调用结束时一定会访问过自己 *)
Theorem DFS_rec_visited_self:
  forall W,
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (W u)
         (fun _ s => s0 ⊆ s)) ->
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (DFS_rec_f W u)
         (fun _ s => u ∈ s)).
Proof.
  intros.
  unfold DFS_rec_f.
  eapply Hoare_bind;
    [| intros;
       apply (Hoare_repeat_break _ (fun _ s => u ∈ s))].
  { apply Hoare_visit.
    intros; subst.
    rewrite H0; sets_unfold; tauto. }
  intros e_set.
  apply Hoare_normalize.
  intros s1 ?.
  apply Hoare_choice.
  + apply Hoare_any_bind.
    intros e.
    apply Hoare_any_bind.
    intros v.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    eapply Hoare_bind; [apply H |].
    simpl; intros _.
    apply Hoare_ret'.
    intros s ?.
    rewrite <- H4.
    tauto.
  + apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_ret'.
    intros.
    subst.
    tauto.
Qed.

(* DFS调用结束时一定会访问完自己的邻居 *)
Theorem DFS_rec_self_neighbor_visited:
  forall W,
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (W u)
         (fun _ s => u ∈ s /\ s0 ⊆ s)) ->
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (DFS_rec_f W u)
         (fun _ s => neighbor_visited s u)).
Proof.
  intros.
  unfold DFS_rec_f.
  eapply Hoare_bind;
    [| intros;
       apply (Hoare_repeat_break _ 
                (fun e_set s => 
                   forall e v, 
                     e ∈ e_set ->
                     step_aux g e u v ->
                     v ∈ s))].
  { apply Hoare_visit.
    simpl. intros.
    sets_unfold in H2; tauto. }
  intros e_set.
  apply Hoare_normalize.
  intros s1 ?.
  apply Hoare_choice.
  + apply Hoare_any_bind.
    intros e.
    apply Hoare_any_bind.
    intros v.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    eapply Hoare_bind; [apply H |].
    simpl; intros _.
    apply Hoare_ret'.
    intros.
    destruct H4.
    Sets_unfold1 in H5.
    destruct H5; [rewrite <- H7; apply (H0 e0 v0); tauto |].
    sets_unfold in H5.
    subst e.
    pose proof step_aux_end_unique _ _ _ _ H3 H6.
    subst v0; tauto.
  + apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_ret'.
    intros.
    subst.
    unfold neighbor_visited.
    intros. destruct H2 as [e ?].
    pose proof H0 e v.
    pose proof H1 e v.
    tauto.
Qed.

(* 核心结论：neighbor_visited的preservation *)
Theorem DFS_rec_other_neighbor_visited:
  forall W,
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (W u)
         (fun _ s =>
            s0 ⊆ s /\
            forall v,
              v ∈ s ->
              v ∈ s0 \/ neighbor_visited s v)) ->
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (DFS_rec_f W u)
         (fun _ s =>
            forall v,
              v ∈ s ->
              v ∈ s0 \/ v = u \/ neighbor_visited s v)).
Proof.
  intros.
  unfold DFS_rec_f.
  eapply Hoare_bind;
    [| intros;
       apply (Hoare_repeat_break _ 
                (fun _ s => 
                   forall v,
                     v ∈ s ->
                     v ∈ s0 \/ v = u \/ neighbor_visited s v))].
  { apply Hoare_visit.
    simpl.
    intros.
    rewrite H0 in H1.
    Sets_unfold1 in H1.
    destruct H1; [tauto |].
    sets_unfold in H1; subst; tauto. }
  intros e_set.
  apply Hoare_normalize.
  intros s1 ?.
  apply Hoare_choice.
  + apply Hoare_any_bind.
    intros e.
    apply Hoare_any_bind.
    intros v.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    eapply Hoare_bind; [apply H |].
    simpl; intros _.
    apply Hoare_ret'.
    intros s [? ?] v0 ?.
    pose proof H5 _ H6.
    destruct H7; [| tauto].
    pose proof H0 _ H7.
    destruct H8; [tauto |].
    destruct H8; [tauto |].
    pose proof neighbor_visited_incl _ _ _ H4 H8.
    tauto.
  + apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_ret'.
    intros; subst s.
    pose proof H0 _ H3.
    tauto.
Qed.

Theorem DFS_rec_neighbor_visited:
  forall W,
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (W u)
         (fun _ s =>
            u ∈ s /\
            s0 ⊆ s /\
            forall v,
              v ∈ s ->
              v ∈ s0 \/ neighbor_visited s v)) ->
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (DFS_rec_f W u)
         (fun _ s =>
            forall v,
              v ∈ s ->
              v ∈ s0 \/ neighbor_visited s v)).
Proof.
  intros.
  assert (Hoare
            (fun s => s = s0)
            (DFS_rec_f W u)
            (fun _ s =>
               forall v,
                 v ∈ s ->
                 v ∈ s0 \/ v = u \/ neighbor_visited s v)).
  {
    apply DFS_rec_other_neighbor_visited.
    clear s0 u.
    intros.
    pose proof H s0 u.
    revert H0.
    apply Hoare_conseq_post.
    intros; tauto.
  }
  assert (Hoare
            (fun s => s = s0)
            (DFS_rec_f W u)
            (fun _ s => neighbor_visited s u)).
  {
    apply DFS_rec_self_neighbor_visited.
    clear s0 u H0.
    intros.
    pose proof H s0 u.
    revert H0.
    apply Hoare_conseq_post.
    intros; tauto.
  }
  pose proof Hoare_conj _ _ _ _ H0 H1.
  clear H H0 H1.
  revert H2; apply Hoare_conseq_post.
  intros _ s [? ?] v ?.
  specialize (H v H1).
  destruct H as [? | [? | ?]]; subst; tauto.
Qed.

Theorem DFS_neighbor_visited:
  forall s0 u,
    Hoare
      (fun s => s = s0)
      (DFS u)
      (fun _ s =>
         u ∈ s /\
         s0 ⊆ s /\
         forall v,
           v ∈ s ->
           v ∈ s0 \/ neighbor_visited s v).
Proof.
  intros.
  unfold DFS.
  apply (Hoare_normal_LFix
           (fun u s1 _ s2 =>
              u ∈ s2 /\
              s1 ⊆ s2 /\
              forall v,
                v ∈ s2 ->
                v ∈ s1 \/ neighbor_visited s2 v)).
  intros.
  clear s0 u.
  apply Hoare_conj; [| apply Hoare_conj].
  + apply DFS_rec_visited_self.
    clear s1 a.
    intros s0 u.
    pose proof H s0 u.
    revert H0.
    apply Hoare_conseq_post; intros; tauto.
  + apply DFS_rec_visited_incr.
    clear s1 a.
    intros s0 u.
    pose proof H s0 u.
    revert H0.
    apply Hoare_conseq_post; intros; tauto.
  + apply DFS_rec_neighbor_visited.
    clear s1 a.
    intros s0 u.
    pose proof H s0 u.
    revert H0.
    apply Hoare_conseq_post; intros; tauto.
Qed.

Theorem DFS_rec_visited_reachable:
  forall W,
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (W u)
         (fun _ s =>
            forall v,
              v ∈ s ->
              v ∈ s0 \/ reachable g u v)) ->
    (forall s0 u,
       Hoare
         (fun s => s = s0)
         (DFS_rec_f W u)
         (fun _ s =>
            forall v,
              v ∈ s ->
              v ∈ s0 \/ reachable g u v)).
Proof.
  intros.
  unfold DFS_rec_f.
  eapply Hoare_bind;
    [| intros;
       apply (Hoare_repeat_break _ 
                (fun _ s => 
                   forall v,
                     v ∈ s ->
                     v ∈ s0 \/ reachable g u v))].
  { apply Hoare_visit.
    simpl.
    intros.
    rewrite H0 in H1.
    Sets_unfold1 in H1.
    destruct H1; [tauto |].
    sets_unfold in H1; subst.
    right.
    reflexivity. }
  intros e_set.
  apply Hoare_normalize.
  intros s1 ?.
  apply Hoare_choice.
  + apply Hoare_any_bind.
    intros e.
    apply Hoare_any_bind.
    intros v.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_normal_assume_bind.
    intros.
    eapply Hoare_bind; [apply H |].
    simpl; intros _.
    apply Hoare_ret'.
    intros.
    pose proof H4 v0.
    pose proof H0 v0.
    assert (reachable g v v0 -> reachable g u v0).
    {
      intros. 
      unfold reachable.
      transitivity_1n v.
      + exists e; tauto.
      + tauto.
    } 
    tauto. 
  + apply Hoare_normal_assume_bind.
    intros.
    apply Hoare_ret'.
    intros; subst s.
    pose proof H0 v.
    tauto.
Qed.

Theorem DFS_visited_reachable:
  forall s0 u,
    Hoare
      (fun s => s = s0)
      (DFS u)
      (fun _ s =>
         forall v,
           v ∈ s ->
           v ∈ s0 \/ reachable g u v).
Proof.
  intros.
  unfold DFS.
  apply (Hoare_normal_LFix
           (fun u s1 _ s2 =>
              forall v,
                v ∈ s2 ->
                v ∈ s1 \/ reachable g u v)).
  intros.
  apply DFS_rec_visited_reachable.
  tauto.
Qed.

Theorem DFS_correct:
  forall u,
    Hoare
      (fun s => s = ∅)
      (DFS u)
      (fun _ s =>
         forall v, v ∈ s <-> reachable g u v).
Proof.
  intros.
  pose proof DFS_neighbor_visited ∅ u.
  pose proof DFS_visited_reachable ∅ u.
  pose proof Hoare_conj _ _ _ _ H H0.
  revert H1; clear H H0.
  apply Hoare_conseq_post.
  intros _ s [[? [_ ?]] ?].
  intros.
  split; intros.
  { pose proof H1 v; tauto. }
  clear H1. 
  unfold reachable in H2.
  induction_1n H2.
  + tauto.
  + pose proof H0 u H as [[] | ].
    unfold neighbor_visited in H3.
    pose proof H3 _ H1.
    pose proof IHrt g_valid _ H4 H0.
    tauto.
Qed.

End DFS.
