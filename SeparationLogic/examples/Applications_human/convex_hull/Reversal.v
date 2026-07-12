(* COQ-HEAD *)
Require Import Coq.Lists.List.
From SimpleC.EE.Applications_human.convex_hull Require Import Maximality.
Import ListNotations.
(* /COQ-HEAD *)

(** * Reversal preservation for convex hulls *)

(** Disjunctive convex hull definition accepting both orientations.
    Second disjunct uses (rev T) for the containment check since
    point_in_hull_edges is direction-dependent (left-of-edge). *)
Definition is_convex_hull' (base T : list point) : Prop :=
  (ccw_convex T /\ is_max_hull'_edges T base) \/
  (rev_ccw_convex T /\ is_max_hull'_edges (rev T) base).

Lemma ccw_convex_forall3_inv : forall l,
  ccw_convex l ->
  forall l1 p l2 q l3 r l4,
    l = l1 ++ p :: l2 ++ q :: l3 ++ r :: l4 ->
    ccw p q r.
Proof.
  exact gs_ccw_convex_forall3_inv.
Qed.

(** ccw_convex (CCW order) is preserved under reversal *)
Lemma ccw_convex_rev : forall T,
  ccw_convex T ->
  rev_ccw_convex (rev T).
Proof.
  intros T Hconv.
  apply gs_ccw_convex_rev_to_rev_ccw_convex.
  rewrite rev_involutive.
  exact Hconv.
Qed.

(** rev_ccw_convex (CW order) is preserved under reversal *)
Lemma rev_ccw_convex_rev : forall T,
  rev_ccw_convex T ->
  ccw_convex (rev T).
Proof.
  exact gs_rev_ccw_convex_to_ccw_convex_rev.
Qed.

(** is_max_hull'_edges is preserved under base reversal *)
Lemma is_max_hull'_edges_rev_base : forall T base,
  is_max_hull'_edges T base ->
  is_max_hull'_edges T (rev base).
Proof.
  intros T base Hall.
  unfold is_max_hull'_edges in *.
  apply Forall_rev.
  exact Hall.
Qed.

(** base reversal theorem *)
Theorem is_convex_hull'_rev_base : forall base T,
  is_convex_hull' base T ->
  is_convex_hull' (rev base) T.
Proof.
  intros base T [H | H].
  - (* Case 1: ccw_convex T /\ is_max_hull'_edges T base *)
    destruct H as [Hconv Hmax].
    left; split.
    + exact Hconv.
    + apply is_max_hull'_edges_rev_base. exact Hmax.
  - (* Case 2: rev_ccw_convex T /\ is_max_hull'_edges (rev T) base *)
    destruct H as [Hrev Hmax].
    right; split.
    + exact Hrev.
    + apply is_max_hull'_edges_rev_base. exact Hmax.
Qed.

(** double reversal theorem *)
Theorem is_convex_hull'_rev : forall base T,
  is_convex_hull' base T ->
  is_convex_hull' (rev base) (rev T).
Proof.
  intros base T [H | H].
  - (* Case 1: ccw_convex T /\ is_max_hull'_edges T base *)
    destruct H as [Hconv Hmax].
    right; split.
    + apply ccw_convex_rev; exact Hconv.
    + rewrite rev_involutive. apply is_max_hull'_edges_rev_base; exact Hmax.
  - (* Case 2: rev_ccw_convex T /\ is_max_hull'_edges (rev T) base *)
    destruct H as [Hrev Hmax].
    left; split.
    + apply rev_ccw_convex_rev; exact Hrev.
    + apply is_max_hull'_edges_rev_base; exact Hmax.
Qed.

(** hull reversal theorem *)
Theorem is_convex_hull'_rev_ : forall base T,
  is_convex_hull' base T ->
  is_convex_hull' base (rev T).
Proof.
  intros base T [H | H].
  - (* Case 1: ccw_convex T /\ is_max_hull'_edges T base *)
    destruct H as [Hconv Hmax].
    right; split.
    + apply ccw_convex_rev. exact Hconv.
    + rewrite rev_involutive. exact Hmax.
  - (* Case 2: rev_ccw_convex T /\ is_max_hull'_edges (rev T) base *)
    destruct H as [Hrev Hmax].
    left; split.
    + apply rev_ccw_convex_rev. exact Hrev.
    + exact Hmax.
Qed.
