(** * Z-indexed walk length and graph distance.

    GraphLib's [path_of_len] indexes a walk by its length in [nat].  The
    Codeforces specifications work in [Z] throughout — lengths are compared,
    summed and squared alongside other [Z] quantities — so this file gives a
    self-contained [Z] development: the walk-length relation, the distance
    built from it with MaxMinLib's [min_value_of_subset], and a [Z]
    counterpart of every fact GraphLib proves on the [nat] side.

    Nothing here mentions [path_of_len] or [bfs_dist].  The two developments
    are equivalent, but that equivalence is deliberately not exposed: a
    specification reaching for this file should never have to see a [nat].

    A [Z] index is a computed term rather than a constructor pattern, so two
    facts that [nat] supplies by typing have to be supplied here as lemmas:
    a walk length is non-negative ([path_of_zlen_nonneg]), and peeling one
    step off needs [0 <= d] as a side condition ([path_of_zlen_succ_inv]) —
    without it the statement is false, since [d = -1] would satisfy
    [k = d + 1] at [k = 0].  That side condition reappears wherever the [nat]
    proof relied on [S d] being a pattern, or on [le] being inductive. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical_Prop.
Require Import SetsClass.SetsClass.
Require Import MaxMinLib.MaxMin.
Require Import MaxMinLib.Interface.
From GraphLib Require Import graph_basic reachable_basic.

Local Open Scope Z_scope.

Section PATH_OF_ZLEN.

Context {G V E: Type}
        `{graph: Graph G V E}
        (g: G).

Notation step := (step g).
Notation reachable := (reachable g).

(** ** Walks of a given length *)

(** [path_of_zlen u v k]: there is a walk from [u] to [v] of exactly [k]
    edges. *)
Inductive path_of_zlen : V -> V -> Z -> Prop :=
  | pozl_0 u : path_of_zlen u u 0
  | pozl_step u w v d :
      path_of_zlen u w d ->
      step w v ->
      path_of_zlen u v (d + 1).

(** A walk length is never negative.  In the [nat] development this is the
    type; here it is the lemma every other proof leans on. *)
Lemma path_of_zlen_nonneg :
  forall u v k, path_of_zlen u v k -> 0 <= k.
Proof. induction 1; lia. Qed.

(** Length zero forces the endpoints to coincide.  [inversion] alone does not
    close the step case, because [d + 1 = 0] is not syntactically absurd the
    way [S d = 0] is; it takes the bound above. *)
Lemma path_of_zlen_0_eq :
  forall u v k, path_of_zlen u v k -> k = 0 -> v = u.
Proof.
  induction 1; intros Hk; auto.
  apply path_of_zlen_nonneg in H. lia.
Qed.

Lemma path_of_zlen_0_inv :
  forall u v, path_of_zlen u v 0 -> v = u.
Proof. intros u v H. eapply path_of_zlen_0_eq; eauto. Qed.

(** Peeling the last step off.  [0 <= d] is required: at [k = 0] the equation
    [k = d + 1] is satisfied by [d = -1], for which no witness exists. *)
Lemma path_of_zlen_succ_inv :
  forall u v k d,
    path_of_zlen u v k ->
    0 <= d ->
    k = d + 1 ->
    exists w, path_of_zlen u w d /\ step w v.
Proof.
  induction 1; intros Hd Hk.
  - exfalso; lia.
  - assert (d0 = d) by lia. subst. eauto.
Qed.

Lemma path_of_zlen_reachable :
  forall u v k, path_of_zlen u v k -> reachable u v.
Proof.
  intros u v k H. induction H.
  - reflexivity.
  - eapply reachable_step_reachable; eauto.
Qed.

Lemma reachable_path_of_zlen :
  forall u v, reachable u v -> exists k, path_of_zlen u v k.
Proof.
  intros u v Hreach. unfold reachable in Hreach.
  induction_n1 Hreach.
  - exists 0. constructor.
  - destruct IHrt as [k Hpath].
    exists (k + 1). eapply pozl_step; eauto.
Qed.

(** ** Distance *)

(** [zdistance u v d]: the shortest walk from [u] to [v] has [d] edges.  The
    minimum is MaxMinLib's, not an inlined minimality quantifier. *)
Definition zdistance (u v : V) (d : Z) : Prop :=
  min_value_of_subset Z.le (path_of_zlen u v) (fun k => k) d.

(** [zdistance_le u v d]: [v] lies within [d] edges of [u]. *)
Definition zdistance_le (u v : V) (d : Z) : Prop :=
  exists d', zdistance u v d' /\ d' <= d.

(** The workhorse: MaxMinLib's packaging, unfolded once. *)
Lemma zdistance_iff :
  forall u v d,
    zdistance u v d <->
    path_of_zlen u v d /\ (forall k, path_of_zlen u v k -> d <= k).
Proof.
  intros u v d. split.
  - intros [a [[Ha Hmin] Hfa]]. simpl in Hfa. subst a.
    split; [exact Ha |]. intros k Hk. apply (Hmin k Hk).
  - intros [Hd Hmin]. exists d. split; [split | reflexivity].
    + sets_unfold. exact Hd.
    + intros b Hb. sets_unfold in Hb. simpl. apply (Hmin b Hb).
Qed.

Lemma zdistance_path :
  forall u v d, zdistance u v d -> path_of_zlen u v d.
Proof. intros u v d H. apply zdistance_iff in H. tauto. Qed.

Lemma zdistance_least :
  forall u v d k, zdistance u v d -> path_of_zlen u v k -> d <= k.
Proof. intros u v d k H Hk. apply zdistance_iff in H as [_ Hmin]. auto. Qed.

Lemma zdistance_nonneg :
  forall u v d, zdistance u v d -> 0 <= d.
Proof.
  intros u v d H. apply zdistance_path in H.
  eapply path_of_zlen_nonneg; eauto.
Qed.

Lemma zdistance_refl : forall u, zdistance u u 0.
Proof.
  intros u. apply zdistance_iff. split.
  - constructor.
  - intros k Hk. eapply path_of_zlen_nonneg; eauto.
Qed.

Lemma zdistance_0_iff_eq :
  forall u v, zdistance u v 0 <-> v = u.
Proof.
  intros u v. split.
  - intros H. apply zdistance_path in H. eapply path_of_zlen_0_inv; eauto.
  - intros Hv. subst v. apply zdistance_refl.
Qed.

Lemma zdistance_le_0_iff_eq :
  forall u v, zdistance_le u v 0 <-> v = u.
Proof.
  intros u v. split.
  - intros [d' [Hd' Hle]].
    assert (0 <= d') by (eapply zdistance_nonneg; eauto).
    assert (d' = 0) by lia. subst d'.
    apply zdistance_0_iff_eq in Hd'. exact Hd'.
  - intros Hv. subst v. exists 0. split; [apply zdistance_refl | lia].
Qed.

(** The distance exists whenever any walk does.  The [nat] proof recurses on
    [lt_wf_ind]; here the recursion is on [Z.lt_wf 0], which is the same
    argument once lengths are known non-negative. *)
Lemma path_of_zlen_min :
  forall k u v,
    path_of_zlen u v k -> exists d, zdistance u v d /\ d <= k.
Proof.
  intros k.
  induction k as [k IH] using (well_founded_induction (Z.lt_wf 0)).
  intros u v Hpath.
  destruct (classic (exists q, 0 <= q < k /\ path_of_zlen u v q))
    as [[q [Hq Hqp]] | Hnone].
  - destruct (IH q Hq u v Hqp) as [dmin [Hdist Hle]].
    exists dmin. split; [exact Hdist | lia].
  - exists k. split; [| lia].
    apply zdistance_iff. split; [exact Hpath |].
    intros q Hq.
    destruct (Z_le_gt_dec k q) as [Hle | Hgt]; [exact Hle |].
    exfalso. apply Hnone. exists q. split; [split |].
    + eapply path_of_zlen_nonneg; eauto.
    + lia.
    + exact Hq.
Qed.

Lemma reachable_iff_zdistance :
  forall u v, reachable u v <-> exists d, zdistance u v d.
Proof.
  intros u v. split.
  - intros Hreach. apply reachable_path_of_zlen in Hreach as [k Hpath].
    destruct (path_of_zlen_min k u v Hpath) as [d [Hdist _]].
    exists d. exact Hdist.
  - intros [d Hd]. apply zdistance_path in Hd.
    eapply path_of_zlen_reachable; eauto.
Qed.

Lemma zdistance_unique :
  forall u v d1 d2, zdistance u v d1 -> zdistance u v d2 -> d1 = d2.
Proof.
  intros u v d1 d2 H1 H2.
  pose proof (zdistance_least u v d1 d2 H1 (zdistance_path _ _ _ H2)).
  pose proof (zdistance_least u v d2 d1 H2 (zdistance_path _ _ _ H1)).
  lia.
Qed.

Lemma zdistance_le_of_dist :
  forall u v d d', zdistance u v d' -> d' <= d -> zdistance_le u v d.
Proof. intros u v d d' Hdist Hle. exists d'. split; assumption. Qed.

Lemma zdistance_not_le_lt :
  forall u v d d', zdistance u v d -> d' < d -> ~ zdistance_le u v d'.
Proof.
  intros u v d d' Hdist Hlt [k [Hk Hkle]].
  pose proof (zdistance_unique u v d k Hdist Hk). lia.
Qed.

(** The predecessor of a vertex one step further out. *)
Lemma zdistance_succ_pred :
  forall u v d,
    0 <= d ->
    zdistance u v (d + 1) ->
    exists w, zdistance u w d /\ step w v.
Proof.
  intros u v d Hd Hdist.
  apply zdistance_iff in Hdist as [Hpath Hmin].
  destruct (path_of_zlen_succ_inv u v (d + 1) d Hpath Hd eq_refl)
    as [w [Hpath_w Hstep]].
  exists w. split; [| exact Hstep].
  apply zdistance_iff. split; [exact Hpath_w |].
  intros q Hq.
  destruct (Z_le_gt_dec d q) as [Hle | Hgt]; [exact Hle |].
  assert (Hpath_v: path_of_zlen u v (q + 1)) by (eapply pozl_step; eauto).
  specialize (Hmin (q + 1) Hpath_v). lia.
Qed.

Lemma zdistance_no_layer_succ :
  forall u d,
    0 <= d ->
    (forall v, ~ zdistance u v d) ->
    forall v, ~ zdistance u v (d + 1).
Proof.
  intros u d Hd Hnone v Hdist.
  apply zdistance_succ_pred in Hdist; [| exact Hd].
  destruct Hdist as [w [Hw _]]. exact (Hnone w Hw).
Qed.

(** The [nat] proof inducts on the derivation of [d <= k]; [Z.le] is not
    inductive, so the recursion is on [k] instead. *)
Lemma zdistance_no_layer_ge :
  forall u k d,
    0 <= d ->
    d <= k ->
    (forall v, ~ zdistance u v d) ->
    forall v, ~ zdistance u v k.
Proof.
  intros u k.
  induction k as [k IH] using (well_founded_induction (Z.lt_wf 0)).
  intros d Hd Hle Hnone v Hdist.
  destruct (Z.eq_dec d k) as [Heq | Hneq].
  - subst k. exact (Hnone v Hdist).
  - assert (Hk1: 0 <= k - 1) by lia.
    assert (Hlt: 0 <= k - 1 < k) by lia.
    assert (Hd1: d <= k - 1) by lia.
    apply (zdistance_no_layer_succ u (k - 1) Hk1
             (IH (k - 1) Hlt d Hd Hd1 Hnone) v).
    replace (k - 1 + 1) with k by lia. exact Hdist.
Qed.

Lemma zdistance_le_succ_inv :
  forall u v d,
    zdistance_le u v (d + 1) ->
    zdistance_le u v d \/ zdistance u v (d + 1).
Proof.
  intros u v d [k [Hk Hle]].
  destruct (Z.eq_dec k (d + 1)) as [Heq | Hneq].
  - subst k. right. exact Hk.
  - left. exists k. split; [exact Hk | lia].
Qed.

(** ** Finiteness *)

Section FINITE_ZDISTANCE.

Context
  {gv: GValid G}
  {stepvalid: @StepValid G V E graph gv}
  {finite_graph: @FiniteGraph G V E graph gv}.

Context (g_valid: gvalid g).

Lemma zdistance_vvalid :
  forall u v d, vvalid g u -> zdistance u v d -> vvalid g v.
Proof.
  intros u v d Hu Hdist.
  destruct (classic (v = u)) as [Heq | Hneq].
  - subst v. exact Hu.
  - assert (Hne: u <> v) by (intro H; apply Hneq; symmetry; exact H).
    apply zdistance_path in Hdist.
    pose proof (path_of_zlen_reachable u v d Hdist) as Hreach.
    destruct (@reachable_vvalid G V E g graph gv stepvalid u v Hne Hreach)
      as [_ Hv].
    exact Hv.
Qed.

Lemma finite_zdistance_bound_list :
  forall u l,
    exists dmax,
      forall v d, In v l -> zdistance u v d -> d <= dmax.
Proof.
  intros u l. induction l as [| a l [dmax IH]].
  - exists 0. intros v d Hin _. contradiction.
  - destruct (classic (exists da, zdistance u a da)) as [[da Hda] | Hnone].
    + exists (Z.max da dmax).
      intros v d [Hv | Hin] Hdist.
      * subst v. pose proof (zdistance_unique u a d da Hdist Hda). lia.
      * specialize (IH v d Hin Hdist). lia.
    + exists dmax.
      intros v d [Hv | Hin] Hdist.
      * subst v. exfalso. apply Hnone. exists d. exact Hdist.
      * apply IH with (v := v); assumption.
Qed.

Lemma finite_zdistance_bound :
  forall u,
    vvalid g u ->
    exists dmax, forall v d, zdistance u v d -> d <= dmax.
Proof.
  intros u Hu.
  destruct (finite_zdistance_bound_list u (listV g)) as [dmax Hbound].
  exists dmax. intros v d Hdist.
  apply Hbound with (v := v).
  - apply finite_vertices; [exact g_valid |].
    apply zdistance_vvalid with (u := u) (d := d); assumption.
  - exact Hdist.
Qed.

End FINITE_ZDISTANCE.

End PATH_OF_ZLEN.

Arguments path_of_zlen {G V E _} g _ _ _.
Arguments zdistance {G V E _} g _ _ _.
Arguments zdistance_le {G V E _} g _ _ _.
