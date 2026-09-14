(**
  C-facing refinement interface for the Kosaraju monadic development.

  The old [Kosaraju] development stores a finishing time as a vertex-indexed
  function [finish : V -> nat].  The C implementation instead writes a
  vertex into [fin] at each finishing event and consumes [fin] backwards in
  phase 2.  This file deliberately makes that representation change explicit.

  It is an interface layer, not an axiomatisation of the C program.  A C VC
  proves [CFinishSequence], [CLabelsRepresent], and the step simulation below;
  the theorems in this file then transfer the already proved monadic SCC
  correctness theorem to the C-facing arrays.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import SetsClass.SetsClass.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare.
From GraphLib Require Import graph_basic reachable_basic.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import Kosaraju.

Import ListNotations.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section CRefinement.

Context {G V E : Type}
        `{KG : KosarajuGraph G V E}
        (g : G)
        (g_valid : gvalid g).

(** [fin[i] = v] is the C meaning of [finish v = i + 1].  The offset is
    intentional: the monadic model reserves zero for an unfinished vertex,
    whereas C stores the first completed vertex in [fin[0]]. *)
Definition CFinishSequence (s : St) (fin : list V) : Prop :=
  length fin = timer s /\
  forall i v, nth_error fin i = Some v <-> finish s v = S i.

Definition CPhase1Refinement (s : St) (fin : list V) : Prop :=
  CFinishSequence s fin /\ Phase1_Order g s.

Lemma c_finish_sequence_length : forall s fin,
  CFinishSequence s fin -> length fin = timer s.
Proof. intros s fin [H _]. exact H. Qed.

Lemma c_finish_sequence_lookup : forall s fin i v,
  CFinishSequence s fin ->
  (nth_error fin i = Some v <-> finish s v = S i).
Proof. intros s fin i v [_ H]. apply H. Qed.

Lemma c_finish_sequence_finished : forall s fin v,
  CFinishSequence s fin -> finish s v <> 0 ->
  exists i, nth_error fin i = Some v.
Proof.
  intros s fin v Hfin Hdone.
  destruct (finish s v) as [| i] eqn:Htime; [contradiction|].
  exists i. apply (proj2 (c_finish_sequence_lookup s fin i v Hfin)).
  exact Htime.
Qed.

(** The C phase-2 loop reads [fin[n - 1 - i]].  Keeping [fin_at] total is
    convenient for the monadic schedule; VCs provide [i < n] before using it.
    With [n = length fin], this is exactly reverse finish order. *)
Definition c_phase2_root_at (fin_at : nat -> V) (n i : nat) : V :=
  fin_at (n - S i).

Definition c_phase2_root_at_list (fallback : V) (fin : list V) (i : nat) : V :=
  c_phase2_root_at (fun j => nth j fin fallback) (length fin) i.

Lemma c_phase2_root_at_list_in_range : forall fallback fin i,
  (i < length fin)%nat ->
  c_phase2_root_at_list fallback fin i = nth (length fin - S i) fin fallback.
Proof. reflexivity. Qed.

(** One C phase-2 iteration, at the monadic abstraction level.  The explicit
    [visit2; set_scc_id root root] is deliberately retained: it is the shape
    of the C branch [sid[root] = root; dfs2(root, root)].  The second visit
    and assignment inside [DFS_scc] are idempotent model steps. *)
Definition c_phase2_iteration (root : V) : MonadErr.M St unit :=
  if_else (fun st => visited2 st root)
    (ret tt)
    (visit2 root;; set_scc_id root root;; DFS_scc g root root).

Lemma c_phase2_iteration_unfold : forall root,
  c_phase2_iteration root =
  if_else (fun st => visited2 st root)
    (ret tt)
    (visit2 root;; set_scc_id root root;; DFS_scc g root root).
Proof. reflexivity. Qed.

(** This is the exact program used by the old scheduled phase-2 model. *)
Lemma c_phase2_iteration_is_monadic_schedule_branch : forall root,
  c_phase2_iteration root =
  if_else (fun st => visited2 st root)
    (ret tt)
    (visit2 root;; set_scc_id root root;; DFS_scc g root root).
Proof. reflexivity. Qed.

Definition c_phase2_schedule
           (fin_at : nat -> V) (n start fuel : nat) : MonadErr.M St unit :=
  kosaraju_scc_schedule g (c_phase2_root_at fin_at n) start fuel.

Lemma c_phase2_schedule_done : forall fin_at n start,
  c_phase2_schedule fin_at n start 0 = ret tt.
Proof. intros. unfold c_phase2_schedule. apply kosaraju_scc_schedule_done. Qed.

(** C stores a root vertex as the component label; the old monad stores a
    fresh natural component id.  Equality of labels, rather than their raw
    representation, is the simulation relation required by all SCC clients. *)
Definition CLabelsRepresent (label : V -> V) (s : St) : Prop :=
  forall u v, label u = label v <-> scc_id s u = scc_id s v.

Definition CLabelsCorrect (label : V -> V) : Prop :=
  forall u v, label u = label v <-> mutually_reachable g u v.

Lemma c_labels_correct_of_R : forall s label,
  R g s ->
  (forall v, visited2 s v) ->
  CLabelsRepresent label s ->
  CLabelsCorrect label.
Proof.
  intros s label HR Hall Hrep u v.
  rewrite (Hrep u v).
  apply R_all_visited_correct with (st := s); assumption.
Qed.

(** The end-to-end monadic theorem is the semantic source for a C refinement:
    a C final-state proof supplies [CLabelsRepresent] for its simulated final
    monadic state, and this lemma transfers the theorem without reproving SCC
    graph theory in the C VC layer. *)
Lemma c_labels_correct_of_monadic_post : forall s label,
  (forall v, visited2 s v) ->
  (forall u v, scc_id s u = scc_id s v <-> mutually_reachable g u v) ->
  CLabelsRepresent label s ->
  CLabelsCorrect label.
Proof.
  intros s label Hall Hmonad Hrep u v.
  rewrite (Hrep u v). apply Hmonad.
Qed.

(** A root-labelled C component can be connected to the monad locally.  This
    is the postcondition a C [sid[root] = root; dfs2(root, root)] simulation
    should establish for newly visited vertices; old labels are intentionally
    framed outside this local component relation. *)
Definition CRootLabelComponent (before after : St) (root : V)
           (label : V -> V) : Prop :=
  label root = root /\
  forall v, ~ visited2 before v ->
    (label v = root <-> scc_id after v = scc_id after root).

Lemma c_root_label_component_eq : forall before after root label v,
  CRootLabelComponent before after root label ->
  ~ visited2 before v ->
  (label v = root <-> scc_id after v = scc_id after root).
Proof. intros before after root label v [_ H] Hnew. apply H; exact Hnew. Qed.

End CRefinement.
