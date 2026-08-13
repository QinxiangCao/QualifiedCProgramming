
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelMonad StateRelHoare.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Module DFSExample.

(** A directed graph can be defined as follows. *)
Record PreGraph (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

Notation "pg '.(vvalid)'" := (vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).

(** Based on this, we can define that there is an edge from x to y. *)

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y.

(** Furthermore, the reflexive transitive closure of the single-step reachability relation is the multi-step reachability relation. *)

Definition reachable {V E: Type} (pg: PreGraph V E) :=
  clos_refl_trans (step pg).


(** The reflexive transitive closure [clos_refl_trans] is provided by the SetsClass library. *)
(** Next, we define the program state for the DFS algorithm; each state includes a 'visited' set and a stack. *)

Record state (V: Type): Type :=
{
  stack: list V;
  visited: V -> Prop;
}.

Definition unvisited (V: Type) (s: state V): V -> Prop :=
  Sets.complement (visited V s).

Notation "s '.(visited)'" := (visited _ s) (at level 1).
Notation "s '.(unvisited)'" := (unvisited _ s) (at level 1).
Notation "s '.(stack)'" := (stack _ s) (at level 1).

Lemma unvisited_visited {V: Type}:
  forall (s: state V),
    s.(unvisited) == Sets.complement s.(visited).
Proof. intros. reflexivity. Qed.

(** Based on this, we can define the basic state operations required by DFS. *)
Definition visit {V} (v: V): StateRelMonad.M (state V) unit :=
  update (fun s1 s2 =>
    s2.(visited) == s1.(visited) ∪ Sets.singleton v /\
    s2.(stack) = s1.(stack)).

Definition push_stack {V} (v: V): StateRelMonad.M (state V) unit :=
  update (fun s1 s2 =>
    s2.(stack) = v :: s1.(stack) /\ s2.(visited) = s1.(visited)).

Definition pop_stack {V}: StateRelMonad.M (state V) V :=
  fun s1 v s2 =>
    s1.(stack) = v :: s2.(stack) /\ s2.(visited) = s1.(visited).

Definition if_empty_stack {V}: StateRelMonad.M (state V) unit :=
  assume (fun s => s.(stack) = nil).

(** The following is the description of the DFS algorithm. *)

Definition body_DFS {V E} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) (CntOrBrk V unit) :=
  choice
    (assume (fun s => forall v, step pg u v -> v ∈ s.(visited));;
     choice
     (assume (fun s => s.(stack) = nil);;
      break tt)
     (v <- pop_stack;;
      continue v))
    (v <- any V;;
     assume (fun s => ~ v ∈ s.(visited));;
     assume!! (step pg u v);;
     push_stack u;;
     visit v;;
     continue v).
  
Definition DFS {V E} (pg: PreGraph V E) (v: V): StateRelMonad.M (state V) unit :=
  visit v;; repeat_break (body_DFS pg) v.

End DFSExample.

(** As an example, we will show that a vertex is visited in DFS iff it is reachable. *)
Module DFSProof.
Import DFSExample
       StateRelHoare
       StateRelMonad.

(** First list the Hoare logic properties for the operations 'push_stack', 'pop_stack', and 'visit'. *)

Fact push_stack_fact {V: Type}: forall (v: V) P,
  Hoare P (push_stack v) (fun _ s => exists s', s.(stack) = v :: s'.(stack) /\ s.(visited) = s'.(visited) /\ P s').
Proof.
  intros.
  unfold push_stack.
  eapply Hoare_conseq_post; [| apply Hoare_update].
  firstorder.
Qed.

Fact pop_stack_fact {V: Type}: forall P,
  Hoare P (pop_stack) (fun (v: V) s => exists s', s'.(stack) = v :: s.(stack) /\ s.(visited) = s'.(visited) /\ P s').
Proof.
  intros.
  unfold pop_stack.
  eapply Hoare_conseq_post; [| apply Hoare_step].
  firstorder.
Qed.

Fact visit_fact {V: Type}: forall (v: V) P,
  Hoare P (visit v) (fun _ s => exists s', s.(stack) = s'.(stack) /\ s.(visited) == s'.(visited) ∪ Sets.singleton v /\ P s').
Proof.
  intros.
  unfold visit.
  eapply Hoare_conseq_post; [| apply Hoare_update].
  firstorder.
Qed.

Module DFSProp.
Section DFS.
Context {V E: Type} (pg: PreGraph V E).

Definition branch1_prop (u: V) (P: state V -> Prop) (w: V) (s: state V) :=
  exists s',
      s'.(stack) = w :: s.(stack) /\
      s.(visited) = s'.(visited) /\
      (forall v : V, step pg u v -> v ∈ s'.(visited)) /\ P s'.

Lemma branch1_prop_proof (u: V): forall (P: state V -> Prop),
  Hoare P
        (x <- (assume (fun s => forall v, step pg u v -> v ∈ s.(visited));;
        choice
        (assume (fun s => s.(stack) = nil);;
        break tt)
        (v <- pop_stack;;
        continue v));; continue_case x)
        (branch1_prop u P).
Proof.
  intros.
  hoare_auto. 
  hoare_bind pop_stack_fact. simpl.
  hoare_auto.
Qed.

Definition branch2_prop (u: V) (P: state V -> Prop) (v: V) (s: state V) :=
  exists s',
      s.(stack) = u :: s'.(stack) /\
      s.(visited) == s'.(visited) ∪ [v] /\
      step pg u v /\ ~ v ∈ s'.(visited) /\ P s'.

Lemma branch2_prop_proof (u: V): forall (P: state V -> Prop),
  Hoare P
        (v <- any V;;
        assume (fun s => ~ v ∈ s.(visited));;
        assume!! (step pg u v);;
        push_stack u;;
        visit v;;
        ret v)
        (branch2_prop u P).
Proof.
  intros.
  hoare_bind Hoare_any; simpl.
  hoare_auto.
  hoare_bind push_stack_fact.
  hoare_bind visit_fact.
  hoare_cons_pre Hoare_ret.
  intros.
  unfold branch2_prop.
  destruct H0 as (s'' & ? & ? & s' & ? & ? & ? & ?).
  exists s'.
  rewrite H0, H1 in *; clear H0 H1 s.
  rewrite H3.
  repeat split; tauto.
Qed.

Lemma branch2_equiv {B:Type} (u: V):
  x <- (v <- any V;;
        assume (fun s => ~ v ∈ s.(visited));;
        assume!! (step pg u v);;
        push_stack u;;
        visit v;;
        continue v);; (@continue_case _ _ B) x
  ==
  (v <- any V;;
  assume (fun s => ~ v ∈ s.(visited));;
  assume!! (step pg u v);;
  push_stack u;;
  visit v;;
  ret v).
Proof. monad_equiv. Qed.

(** We first prove that visited vertices are reachable. *)
Definition stack_inv (s: state V) :=
  forall v, In v s.(stack) -> v ∈ s.(visited).

Definition reachable_inv (u: V) (s: state V)  :=
  forall v, v ∈ s.(visited) -> reachable pg u v.

Lemma visit_stack_cnt (v:V):
  Hoare (fun s => v ∈ s.(visited) /\ stack_inv s)
        (x <- body_DFS pg v;; continue_case x)
        (fun v' s => v' ∈ s.(visited) /\ stack_inv s).
Proof.
  intros; unfold body_DFS.
  rewrite bind_choice_equiv; apply Hoare_choice.
  - eapply Hoare_conseq_post.
    2: apply branch1_prop_proof.
    unfold branch1_prop; intros.
    destruct H as (s' & ? & ? & ? & ? & ?).
    unfold stack_inv in *.
    rewrite H0 in *; clear H0.
    split.
    + apply H3.
      rewrite H; constructor; easy.
    + intros.
      apply H3.
      rewrite H; constructor; easy.
  - rewrite branch2_equiv.
    eapply Hoare_conseq_post.
    2: apply branch2_prop_proof.
    unfold branch2_prop; intros.
    destruct H as (s' & ? & ? & ? & ? & ? & ?).
    unfold stack_inv in *.
    rewrite H0 in *.
    split.
    + sets_unfold; auto.
    + intros.
      rewrite H in H5.
      rewrite H0; left; clear H0.
      inversion H5.
      subst v; easy.
      apply H4; easy.
Qed.

Lemma reachable_cnt (u v: V):
  Hoare (fun s => v ∈ s.(visited) /\ reachable_inv u s)
        (x <- body_DFS pg v;; continue_case x)
        (fun v' s => reachable_inv u s).
Proof.
  intros; unfold body_DFS.
  rewrite bind_choice_equiv; apply Hoare_choice.
  - eapply Hoare_conseq_post.
    2: apply branch1_prop_proof.
    unfold branch1_prop; intros.
    destruct H as (s' & ? & ? & ? & ? & ?).
    unfold reachable_inv in *.
    rewrite H0 in *; auto.
  - rewrite branch2_equiv.
    eapply Hoare_conseq_post.
    2: apply branch2_prop_proof.
    unfold branch2_prop; intros.
    destruct H as (s' & ? & ? & ? & ? & ? & ?).
    unfold reachable_inv in *.
    intros.
    rewrite H0 in H5.
    destruct H5.
    { apply H4; auto. }
    inversion H5; subst b.
    apply H4 in H3.
    transitivity_n1 v; auto.
Qed.

Lemma reachable_brk (u v: V):
  Hoare (fun s => reachable_inv u s)
        (x <- body_DFS pg v;; break_case x)
        (fun _ s => reachable_inv u s).
Proof.
  unfold body_DFS; hoare_auto; try hoare_skip.
  tauto.
Qed.

(** Proving another direction is a little more tricky, 
    so we prove a simpler proposition that can derive it. *)
Lemma visit_cnt (v:V): forall w,
  Hoare (fun s => v ∈ s.(visited))
        (x <- body_DFS pg w;; continue_case x)
        (fun _ s => v ∈ s.(visited)).
Proof.
  intros; unfold body_DFS.
  rewrite bind_choice_equiv; apply Hoare_choice.
  - eapply Hoare_conseq_post.
    2: apply branch1_prop_proof.
    unfold branch1_prop; intros.
    destruct H as (s' & ? & ? & ? & ?).
    rewrite H0 in *; auto.
  - rewrite branch2_equiv.
    eapply Hoare_conseq_post.
    2: apply branch2_prop_proof.
    unfold branch2_prop; intros.
    destruct H as (s' & ? & ? & ? & ? & ?).
    rewrite H0 in *.
    left; auto.
Qed.

Lemma visit_break (v :V): forall w,
  Hoare (fun s => v ∈ s.(visited))
        (x <- body_DFS pg w;; break_case x)
        (fun _ s => v ∈ s.(visited)).
Proof.
  intros; unfold body_DFS; hoare_auto.
  - tauto.
  - hoare_skip.
  - hoare_skip.
Qed.

Definition neighbor_visited (s: state V) (u: V) :=
  forall w, step pg u w -> w ∈ s.(visited).

Definition all_neighbor_visit (s: state V) :=
  forall u,
    u ∈ s.(visited) -> neighbor_visited s u.

Definition neighbor_inv (s: state V) (u: V) :=
  forall v,
    v ∈ s.(visited) ->  ~ In v s.(stack) -> v <> u ->
      neighbor_visited s v.

Lemma neighbor_cnt (u: V):
  Hoare (fun s => neighbor_inv s u)
        (x <- body_DFS pg u;; continue_case x)
        (fun u' s => neighbor_inv s u').
Proof.
  unfold body_DFS.
  rewrite bind_choice_equiv; apply Hoare_choice.
  - (*Branch 1*)
    eapply Hoare_conseq_post; [|apply branch1_prop_proof].
    unfold branch1_prop; intros.
    destruct H as (s' & ? & ? & ? & ?).
    unfold neighbor_inv, neighbor_visited in *. 
    rewrite H, H0 in *. clear H H0.
    intros w.
    destruct (classic (w=u)).
    + subst; tauto.
    + intros. 
      apply (H2 w); try easy.
      simpl.
      intros Con; destruct Con; subst; tauto.
  - (* Branch 2 *)
    rewrite branch2_equiv.
    eapply Hoare_conseq_post; [|apply branch2_prop_proof].
    unfold branch2_prop; intros.
    destruct H as (s' & ? & ? & ? & ? & ?).
    unfold neighbor_inv in *; intros.
    unfold neighbor_visited in *.
    intros w; intros.
    rewrite H, H0 in *; clear H H0.
    destruct H4; try congruence.
    simpl in H5.
    left; apply (H3 v); auto.
Qed.

Lemma neighbor_brk (u: V):
  Hoare (fun s => neighbor_inv s u)
        (x <- body_DFS pg u;; break_case x)
        (fun _ => all_neighbor_visit).
Proof.
  unfold body_DFS; hoare_auto; try hoare_skip.
  destruct H as (? & ? & ?).
  unfold all_neighbor_visit.
  unfold neighbor_inv in H1.
  intros v ?.
  destruct (classic (v = u)).
  - subst; auto.
  - apply H1; auto.
    rewrite H; simpl; auto.
Qed.

(** Glue them together *)

Definition DFS_inv (s: state V) (u v: V) :=
  v ∈ s.(visited) /\ stack_inv s /\ reachable_inv u s /\ 
  u ∈ s.(visited) /\ neighbor_inv s v.

Lemma loop_pre (u:V):
  Hoare (fun s => s.(stack) = nil /\ s.(visited) = ∅)
        (visit u)
        (fun _ s => DFS_inv s u u).
Proof.
  eapply Hoare_conseq_post.
  2:apply visit_fact.
  simpl; intros _ s H.
  destruct H as (s' & ? & ? & ? & ?).
  rewrite H1, H2 in *; clear H1 H2.
  rewrite Sets_empty_union in H0.
  hnf; unfold neighbor_inv, neighbor_visited, stack_inv, reachable_inv.
  rewrite H0; split; try easy.
  repeat split; intros.
  - rewrite H, H0 in *; inversion H1; congruence.
  - rewrite H0 in H1.
    inversion H1.
    easy.
  - rewrite H, H0 in *; inversion H1; congruence.
Qed.

Lemma DFS_prop (u:V):
    Hoare (fun s => s.(stack) = nil /\ s.(visited) = ∅)
          (DFS pg u)
          (fun _ s => reachable_inv u s /\ u ∈ s.(visited) /\ 
                      all_neighbor_visit s).
Proof.
  unfold DFS.
  eapply Hoare_bind; [apply loop_pre |].
  simpl; intros _.
  apply Hoare_repeat_break' with (P:= fun v s => DFS_inv s u v); 
  intros v; unfold DFS_inv.
  - hoare_conj.
    eapply Hoare_conseq_post; [|hoare_cons_pre visit_stack_cnt]; simpl; tauto. 
    eapply Hoare_conseq_post; [|hoare_cons_pre visit_stack_cnt]; simpl; tauto. 
    hoare_cons_pre reachable_cnt. 
    hoare_cons_pre visit_cnt. 
    hoare_cons_pre neighbor_cnt. 
  - hoare_conj.
    hoare_cons_pre reachable_brk.
    hoare_cons_pre visit_break.
    hoare_cons_pre neighbor_brk.
Qed.

End DFS.
End DFSProp.

(** We prove the reduction above by contradiction. *)
Module ContradictionProof.
Import DFSProp.
Section DFS.
Context {V E: Type} (pg: PreGraph V E).

Lemma path_exists_pair: forall v u (P: V -> Prop),
  reachable pg v u -> P v -> ~ P u -> 
    exists w z, reachable pg v z /\ step pg z w /\ P z /\ ~ P w.
Proof.
  intros.
  apply NNPP; intros Hnot.
  assert 
  (Hs: forall w z, reachable pg v z -> step pg z w -> P z -> P w).
  {
    intros.
    apply NNPP; intros wnot.
    apply Hnot.
    exists w, z; tauto.
  }
  clear Hnot.
  assert 
  (HP: forall w, reachable pg v w -> P w).
  {
    intros w Hr.
    induction Hr.
    change (nsteps (step pg) x v w) with ((v, w) ∈ nsteps (step pg) x) in H2.
    rewrite nsteps_nsteps' in H2.
    sets_unfold in H2.
    revert H2; revert w.
    rename x into n; induction n; simpl; intros.
    - inversion H2.
      subst; auto.
    - sets_unfold in H2.
      destruct H2 as [z [? ?]].
      pose proof (IHn _ H2).
      change (nsteps' (step pg) n v z) with ((v, z) ∈ (nsteps' (step pg) n)) in H2.
      rewrite <- nsteps_nsteps' in H2.
      assert (reachable pg v z).
      { 
         sets_unfold in H2; unfold reachable, clos_refl_trans; sets_unfold.
         exists n; auto. 
      }
      eapply Hs; eauto. 
  }
  apply HP in H; tauto.
Qed.

Lemma pair_contra: forall v u s,
  reachable pg v u -> v ∈ s.(visited) -> ~ u ∈ s.(visited) ->
  all_neighbor_visit pg s -> False.
Proof.
  intros.
  pose proof (path_exists_pair v u s.(visited) H H0 H1).
  destruct H3 as (w & z & ?).
  unfold all_neighbor_visit, neighbor_visited in H2.
  destruct H3 as (? & ? & ? & ?).
  apply H6.
  apply (H2 z); tauto.
Qed.

Theorem DFS_visited_reachable:
  forall (v u: V),
    Hoare (fun s => s.(stack) = nil /\ s.(visited) = ∅)
          (DFS pg v)
          (fun _ s => u ∈ s.(visited) <-> reachable pg v u).
Proof.
  intros.
  eapply Hoare_conseq_post.
  2:{ apply DFS_prop. }
  simpl; intros.
  split; intros.
  - destruct H.
    apply H; auto. 
  - apply NNPP; intros Hu.
    destruct H as [? []].
    eapply pair_contra; sets_unfold; eauto; tauto.
Qed.

End DFS.
End ContradictionProof.
End DFSProof.
