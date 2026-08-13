Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic.

Section BFS_DIST.

Context {G V E: Type}
        `{graph: Graph G V E}
        (g: G).

Notation step := (step g).
Notation reachable := (reachable g).

(** Unweighted graph distance.

    This file contains the pure graph-theoretic facts used by BFS.  Unlike
    [epath.v], which reasons about concrete edge lists and weighted paths,
    [path_of_len] records only the number of unweighted edges in a path. *)

(** [path_of_len src v d]: there is a directed path from [src] to [v]
    of exactly [d] edges. *)
Inductive path_of_len : V -> V -> nat -> Prop :=
  | pol_0 u : path_of_len u u 0
  | pol_S u w v d :
      path_of_len u w d ->
      step w v ->
      path_of_len u v (S d).

Context (src: V).

(** [bfs_dist v d]: the shortest unweighted path from [src] to [v]
    has length [d]. *)
Definition bfs_dist (v: V) (d: nat) : Prop :=
  path_of_len src v d /\
  forall d', path_of_len src v d' -> d <= d'.

(** [bfs_dist_le v d]: [v] is reachable from [src] by a shortest path
    of length at most [d]. *)
Definition bfs_dist_le (v: V) (d: nat) : Prop :=
  exists d', bfs_dist v d' /\ d' <= d.

Lemma path_of_len_0_eq :
  forall u v, path_of_len u v 0 -> v = u.
Proof.
  intros u v H.
  inversion H; subst; reflexivity.
Qed.

Lemma bfs_dist_src_0 : bfs_dist src 0.
Proof.
  split.
  - constructor.
  - intros d' Hd'.
    lia.
Qed.

Lemma bfs_dist_0_iff_src :
  forall v, bfs_dist v 0 <-> v = src.
Proof.
  intro v.
  split.
  - intros [Hpath _].
    apply path_of_len_0_eq in Hpath.
    exact Hpath.
  - intro Hv.
    subst v.
    apply bfs_dist_src_0.
Qed.

Lemma bfs_dist_le_0_iff_src :
  forall v, bfs_dist_le v 0 <-> v = src.
Proof.
  intro v.
  split.
  - intros [d' [Hd' Hd'le]].
    assert (d' = 0) by lia.
    subst d'.
    apply bfs_dist_0_iff_src in Hd'.
    exact Hd'.
  - intro Hv.
    subst v.
    exists 0.
    split.
    + apply bfs_dist_src_0.
    + lia.
Qed.

Lemma path_of_len_S_inv :
  forall u v d,
    path_of_len u v (S d) ->
    exists w, path_of_len u w d /\ step w v.
Proof.
  intros u v d H.
  inversion H; subst.
  exists w.
  split; assumption.
Qed.

Lemma path_of_len_min :
  forall v n,
    path_of_len src v n ->
    exists d, bfs_dist v d /\ d <= n.
Proof.
  intros v n.
  revert v.
  induction n as [n IH] using lt_wf_ind.
  intros v Hpath.
  destruct (classic (exists d, d < n /\ path_of_len src v d))
    as [[d [Hdlt Hdpath]] | Hnone].
  - specialize (IH d Hdlt v Hdpath) as [dmin [Hdist Hle]].
    exists dmin.
    split; [exact Hdist | lia].
  - exists n.
    split; [|lia].
    unfold bfs_dist.
    split; [exact Hpath |].
    intros d Hdpath.
    destruct (le_lt_dec n d) as [Hle | Hlt]; [exact Hle |].
    exfalso.
    apply Hnone.
    exists d.
    split; assumption.
Qed.

Lemma path_of_len_reachable :
  forall u v d,
    path_of_len u v d -> reachable u v.
Proof.
  intros u v d H.
  induction H.
  - reflexivity.
  - eapply reachable_step_reachable; eauto.
Qed.

Lemma reachable_path_of_len :
  forall v,
    reachable src v -> exists d, path_of_len src v d.
Proof.
  intros v Hreach.
  unfold reachable in Hreach.
  induction_n1 Hreach.
  - exists 0. constructor.
  - destruct IHrt as [d Hpath].
    exists (S d).
    eapply pol_S; eauto.
Qed.

Lemma reachable_iff_bfs_dist :
  forall v,
    reachable src v <-> exists d, bfs_dist v d.
Proof.
  intro v.
  split.
  - intro Hreach.
    apply reachable_path_of_len in Hreach.
    destruct Hreach as [n Hpath].
    destruct (path_of_len_min v n Hpath) as [d [Hdist _]].
    exists d. exact Hdist.
  - intros [d [Hpath _]].
    eapply path_of_len_reachable; eauto.
Qed.

Lemma bfs_dist_unique :
  forall v d1 d2,
    bfs_dist v d1 ->
    bfs_dist v d2 ->
    d1 = d2.
Proof.
  intros v d1 d2 [Hpath1 Hmin1] [Hpath2 Hmin2].
  pose proof (Hmin1 d2 Hpath2).
  pose proof (Hmin2 d1 Hpath1).
  lia.
Qed.

Lemma bfs_dist_le_of_dist :
  forall v d d',
    bfs_dist v d' ->
    d' <= d ->
    bfs_dist_le v d.
Proof.
  intros v d d' Hdist Hle.
  exists d'.
  split; assumption.
Qed.

Lemma bfs_dist_not_le_lt :
  forall v d d',
    bfs_dist v d ->
    d' < d ->
    ~ bfs_dist_le v d'.
Proof.
  intros v d d' Hdist Hlt [k [Hk Hkle]].
  pose proof (bfs_dist_unique v d k Hdist Hk).
  lia.
Qed.

Lemma bfs_dist_S_pred :
  forall v d,
    bfs_dist v (S d) ->
    exists u, bfs_dist u d /\ step u v.
Proof.
  intros v d [Hpath Hmin].
  apply path_of_len_S_inv in Hpath.
  destruct Hpath as [u [Hpath_u Hstep]].
  exists u.
  split; [|exact Hstep].
  unfold bfs_dist.
  split; [exact Hpath_u |].
  intros d' Hpath_u'.
  destruct (le_lt_dec d d') as [Hle | Hgt]; [exact Hle |].
  assert (Hpath_v': path_of_len src v (S d')).
  { eapply pol_S; eauto. }
  specialize (Hmin (S d') Hpath_v').
  lia.
Qed.

Lemma bfs_dist_no_layer_succ :
  forall d,
    (forall v, ~ bfs_dist v d) ->
    forall v, ~ bfs_dist v (S d).
Proof.
  intros d Hnone v Hdist.
  apply bfs_dist_S_pred in Hdist.
  destruct Hdist as [u [Hu _]].
  exact (Hnone u Hu).
Qed.

Lemma bfs_dist_no_layer_ge :
  forall d k,
    d <= k ->
    (forall v, ~ bfs_dist v d) ->
    forall v, ~ bfs_dist v k.
Proof.
  intros d k Hle.
  induction Hle as [|k Hle IH]; intros Hno.
  - exact Hno.
  - apply bfs_dist_no_layer_succ.
    apply IH.
    exact Hno.
Qed.

Lemma bfs_dist_le_S_inv :
  forall v d,
    bfs_dist_le v (S d) ->
    bfs_dist_le v d \/ bfs_dist v (S d).
Proof.
  intros v d [k [Hk Hle]].
  destruct (Nat.eq_dec k (S d)) as [Heq | Hneq].
  - subst k. right. exact Hk.
  - left. exists k. split; [exact Hk | lia].
Qed.

Section FINITE_BFS_DIST.

Context
  {gv: GValid G}
  {stepvalid: @StepValid G V E graph gv}
  {finite_graph: @FiniteGraph G V E graph gv}.

Context
  (g_valid: gvalid g)
  (src_valid: vvalid g src).

Lemma bfs_dist_vvalid :
  forall v d,
    bfs_dist v d ->
    vvalid g v.
Proof.
  intros v d [Hpath _].
  destruct (classic (v = src)) as [Heq | Hneq].
  - subst v. exact src_valid.
  - assert (Hsrc_neq_v: src <> v).
    { intro H. apply Hneq. symmetry. exact H. }
    pose proof (path_of_len_reachable src v d Hpath) as Hreach.
    destruct (@reachable_vvalid G V E g graph gv stepvalid
      src v Hsrc_neq_v Hreach) as [_ Hv].
    exact Hv.
Qed.

Lemma finite_bfs_dist_bound_list :
  forall l,
    exists dmax,
      forall v d,
        In v l ->
        bfs_dist v d ->
        d <= dmax.
Proof.
  induction l as [|a l [dmax IH]].
  - exists 0.
    intros v d Hin _.
    contradiction.
  - destruct (classic (exists da, bfs_dist a da)) as [[da Hda] | Hnone].
    + exists (Nat.max da dmax).
      intros v d [Hv | Hin] Hdist.
      * subst v.
        pose proof (bfs_dist_unique a d da Hdist Hda).
        lia.
      * specialize (IH v d Hin Hdist).
        lia.
    + exists dmax.
      intros v d [Hv | Hin] Hdist.
      * subst v.
        exfalso.
        apply Hnone.
        exists d.
        exact Hdist.
      * apply IH with (v := v); assumption.
Qed.

Lemma finite_bfs_dist_bound :
  exists dmax,
    forall v d,
      bfs_dist v d ->
      d <= dmax.
Proof.
  destruct (finite_bfs_dist_bound_list (listV g)) as [dmax Hbound].
  exists dmax.
  intros v d Hdist.
  apply Hbound with (v := v).
  - apply finite_vertices; [exact g_valid |].
    apply bfs_dist_vvalid with (d := d).
    exact Hdist.
  - exact Hdist.
Qed.

End FINITE_BFS_DIST.

End BFS_DIST.
