(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From SimpleC.EE.Applications_human.convex_hull Require Export Convexity.
Local Open Scope Z.
Import ListNotations.
Import GeoNotations.
(* /COQ-HEAD *)

Fixpoint point_in_or_on (p : point) (CH : list point) : Prop :=
  match CH with
  | nil => True
  | cons r CH' =>
    match CH' with
    | nil => True
    | cons s _ => ccw r p s /\ point_in_or_on p CH'
    end
  end.

(* Convex hull algorithm ensures that CH is subset of l. *)
Definition is_max_hull (CH l: list point) :=
  (* ? In p T \/ *)
  Forall (fun p => point_in_or_on p CH) l.

(* Print left_equal. *)

(* Check if p is in triangle p1-p2-p3 *)
(** requires `~ ccw p1 p2 p3` *)
Definition point_in_triangle (p p1 p2 p3: point) : Prop :=
  (
    ccw p3 p2 p1 /\
    left_equal (build_vec p1 p2) (build_vec p1 p) /\
    left_equal (build_vec p2 p3) (build_vec p2 p) /\
    left_equal (build_vec p3 p1) (build_vec p3 p)
  ) \/
  (
    colinear p1 p2 p3 /\
    (
      colinear p p1 p2 /\ at_mid p p1 p2 \/
      colinear p p2 p3 /\ at_mid p p2 p3 \/
      colinear p p3 p1 /\ at_mid p p3 p1
    )
  ).

Lemma point_in_tri_1 : forall p1 p2 p3,
  ~ ccw p1 p2 p3 -> point_in_triangle p1 p1 p2 p3.
Proof.
  intros.
  destruct (ccw_trichotomy p1 p2 p3) as [[? | ?] | ?].
  - (** ccw p1 p2 p3 *)
    contradiction.
  - (** colinear p1 p2 p3 *)
    clear H.
    right. split; [tauto|].
    left.
    unfold colinear, parallel, at_mid, backward_or_perp in *.
    unfold cross_prod, dot_prod in *.
    simpl in *. nia.
  - (** ccw p2 p1 p3 *)
    clear H.
    left. split; [apply ccw_cyclicity; tauto|].
    unfold ccw, left_equal, left_than in *.
    unfold cross_prod in *. simpl in *.
    repeat split; nia.
Qed.

Lemma point_in_tri_2 : forall p1 p2 p3,
  ~ ccw p1 p2 p3 -> point_in_triangle p2 p1 p2 p3.
Proof.
  intros.
  destruct (ccw_trichotomy p1 p2 p3) as [[? | ?] | ?].
  - (** ccw p1 p2 p3 *)
    contradiction.
  - (** colinear p1 p2 p3 *)
    clear H.
    right. split; [tauto|].
    right; left.
    unfold colinear, parallel, at_mid, backward_or_perp in *.
    unfold cross_prod, dot_prod in *.
    simpl in *. nia.
  - (** ccw p2 p1 p3 *)
    clear H.
    left. split; [apply ccw_cyclicity; tauto|].
    unfold ccw, left_equal, left_than in *.
    unfold cross_prod in *. simpl in *.
    repeat split; nia.
Qed.

Lemma point_in_tri_3 : forall p1 p2 p3,
  ~ ccw p1 p2 p3 -> point_in_triangle p3 p1 p2 p3.
Proof.
  intros.
  destruct (ccw_trichotomy p1 p2 p3) as [[? | ?] | ?].
  - (** ccw p1 p2 p3 *)
    contradiction.
  - (** colinear p1 p2 p3 *)
    clear H.
    right. split; [tauto|].
    right.
    unfold colinear, parallel, at_mid, backward_or_perp in *.
    unfold cross_prod, dot_prod in *.
    simpl in *. nia.
  - (** ccw p2 p1 p3 *)
    clear H.
    left. split; [apply ccw_cyclicity; tauto|].
    unfold ccw, left_equal, left_than in *.
    unfold cross_prod in *. simpl in *.
    repeat split; nia.
Qed.

Lemma point_in_tri_general : forall p a b c,
  ccw c p b ->
  ccw b p a ->
  ccw c p a ->
  ~ ccw a b c ->
  point_in_triangle b p c a.
Proof.
  unfold point_in_triangle, ccw, left_equal, left_than, cross_prod, build_vec;
  simpl in *. intros.
  nia.
Qed.

Lemma point_in_tri_weak_pop : forall p a b c,
  weak_rev_ccw p c b ->
  weak_rev_ccw p c a ->
  weak_rev_ccw p b a ->
  ~ ccw a b c ->
  point_in_triangle b c a p.
Proof.
  intros p a b c Hcb Hca Hba Hn.
  destruct Hcb as [Hcb | [Hcb_col Hcb_mid]];
  destruct Hca as [Hca | [Hca_col Hca_mid]];
  destruct Hba as [Hba | [Hba_col Hba_mid]];
  unfold point_in_triangle, weak_rev_ccw, ccw, colinear, at_mid,
         left_equal, left_than, parallel, backward_or_perp, build_vec,
         cross_prod, dot_prod in *; simpl in *; nia.
Qed.

Lemma parallel_backward_same_side_impossible : forall e d v,
  parallel d e ->
  backward_or_perp d e ->
  left_than v d ->
  left_than v e ->
  False.
Proof.
  intros e d v Hpar Hbwd Hvd Hve.
  pose proof aux2 e v d as Haux.
  pose proof left_than_nonzero2 _ _ Hve as Hnz_e.
  rewrite nonzero_iff in Hnz_e.
  unfold parallel, backward_or_perp, left_than in *.
  nia.
Qed.

Lemma left_equal_segment : forall u v b a q,
  left_equal (build_vec u v) (build_vec u b) ->
  left_equal (build_vec u v) (build_vec u a) ->
  colinear q b a ->
  at_mid q b a ->
  left_equal (build_vec u v) (build_vec u q).
Proof.
  intros u v b a q Hlb Hla Hcol Hmid.
  destruct (Z_lt_ge_dec 0 (cross_prod (build_vec u v) (build_vec u q)))
    as [Hpos | Hle].
  - assert (left_than (build_vec u v) (build_vec q b)) as Hvb.
    { unfold left_equal, left_than, build_vec, cross_prod in *; simpl in *; nia. }
    assert (left_than (build_vec u v) (build_vec q a)) as Hva.
    { unfold left_equal, left_than, build_vec, cross_prod in *; simpl in *; nia. }
    unfold colinear, at_mid in Hcol, Hmid.
    exact (False_rect _ (parallel_backward_same_side_impossible _ _ _
                           Hcol Hmid Hvb Hva)).
  - unfold left_equal in *.
    lia.
Qed.

Lemma point_in_tri_cyclicity : forall p a b c,
  point_in_triangle p a b c <-> point_in_triangle p b c a.
Proof.
  unfold point_in_triangle, ccw, left_equal, left_than, colinear, parallel, at_mid, backward_or_perp, cross_prod, build_vec;
  simpl in *. intros.
  nia.
Qed.

Lemma point_in_triangle_halfplane_weak : forall p a b c u v,
  point_in_triangle p a b c ->
  left_equal (build_vec u v) (build_vec u a) ->
  left_equal (build_vec u v) (build_vec u b) ->
  left_equal (build_vec u v) (build_vec u c) ->
  left_equal (build_vec u v) (build_vec u p).
Proof.
  intros p a b c u v Htri Hla Hlb Hlc.
  unfold point_in_triangle in Htri.
  destruct Htri as [Htri | [Hcol Hseg]].
  - unfold ccw, left_equal, left_than, cross_prod, build_vec in *.
    simpl in *.
    nia.
  - destruct Hseg as [[Hpa Hmid] | [[Hpb Hmid] | [Hpc Hmid]]].
    + exact (left_equal_segment u v a b p Hla Hlb Hpa Hmid).
    + exact (left_equal_segment u v b c p Hlb Hlc Hpb Hmid).
    + exact (left_equal_segment u v c a p Hlc Hla Hpc Hmid).
Qed.

Definition strict_point_in_triangle (p a b c : point) :=
  ccw c p a /\ ccw b p c /\ ccw a p b.

(** Construct a method to seperate situation on the edges of triangle. *)
Lemma point_in_tri_col : forall p a b c,
  colinear a b c ->
  point_in_triangle p a b c ->
  at_mid p c a \/ at_mid p b c \/ at_mid p a b.
Proof.
  intros.
  unfold point_in_triangle, colinear, parallel, at_mid, backward_or_perp, ccw, left_equal, left_than in *.
  unfold cross_prod, dot_prod in *.
  simpl in *. nia.
Qed.

Lemma point_in_tri_split_weak : forall p a b c,
  ~ ccw c a p ->
  strict_point_in_triangle b c a p ->
  forall q,
  strict_point_in_triangle q b a p ->
  point_in_triangle q c a p.
Proof.
  unfold strict_point_in_triangle, point_in_triangle, ccw, left_equal, left_than, cross_prod, build_vec;
  simpl in *. intros.
  nia.
Qed.

Lemma Z_ge_dec : forall (a b : Z),
  a >= b -> {a > b} + {a = b}.
Proof.
  intros.
  apply Z.ge_le in H.
  apply Z_le_lt_eq_dec in H.
  destruct H.
  - left; nia.
  - right; lia.
Qed.

Lemma dot_prod_squared_zero_dec : forall a b,
  dot_prod (build_vec a b) (build_vec a b) = 0 ->
  a = b.
Proof.
  unfold dot_prod; simpl; intros.
  destruct a; destruct b; simpl in H.
  match goal with
  | H: (?x1 - ?x0) * (?x1 - ?x0) + (?y1 - ?y0) * (?y1 - ?y0) = 0 |- _ =>
      remember (x1 - x0) as x;
      remember (y1 - y0) as y;
      assert (x = 0 /\ y = 0) by nia;
      assert (x0 = x1 /\ y0 = y1) by lia;
      destruct H1; subst; reflexivity
  end.
Qed.

Lemma dot_prod_squared_dec : forall a b,
  {a = b} + {dot_prod (build_vec a b) (build_vec a b) > 0}.
Proof.
  intros;
  pose proof metric_nonneg (build_vec a b);
  remember (dot_prod (build_vec a b) (build_vec a b)).
  apply Z_ge_dec in H; destruct H.
  - right; tauto.
  - left; apply dot_prod_squared_zero_dec; lia.
Qed.

Lemma dot_prod_squared_non_neg : forall a b,
  dot_prod (build_vec a b) (build_vec a b) <= 0 ->
  a = b.
Proof.
  intros.
  pose proof metric_nonneg (build_vec a b).
  assert (dot_prod (build_vec a b) (build_vec a b) = 0). { nia. }
  apply dot_prod_squared_zero_dec; tauto.
Qed.

(** =========================================== *)

(* Print colinear_perm132. *) (** p q r -> p r q *)
(* Print colinear_perm213. *) (** p q r -> q p r *)
(* Print colinear_perm231. *) (** p q r -> q r p *)
(* Print colinear_perm312. *) (** p q r -> r p q *)
(* Print colinear_perm321. *) (** p q r -> r q p *)

(** double colinear, one with at_mid => 4-point colinear ? *)
Lemma mid_colinear_4point : forall a b c d,
  colinear c a b ->
  colinear d a b ->
  at_mid d a b ->
  colinear c a d /\ colinear b c d.
Proof.
  intros ? ? ? ? Hcab Hdab ?;
  pose proof colinear_perm213 _ _ _ Hcab as Hacb;
  pose proof colinear_perm213 _ _ _ Hdab as Hadb;
  unfold colinear, parallel, at_mid, backward_or_perp in *.
  assert (cross_prod (build_vec c a) (build_vec a b) = 0) as Hcab_.
  {
    unfold cross_prod in Hcab; unfold cross_prod; simpl in *; nia.
  }
  assert (cross_prod (build_vec c d) (build_vec a b) = 0) as Hdab_.
  {
    assert (cross_prod (build_vec c d) (build_vec a b) =
            - cross_prod (build_vec a c) (build_vec a b) +
            cross_prod (build_vec a d) (build_vec a b)) as _Hc.
            { unfold cross_prod; simpl; nia. }
    lia.
  }
  assert (cross_prod (build_vec c a) (build_vec c d) = 0).
  {
    pose proof aux2 (build_vec a b) (build_vec c a) (build_vec c d) as H_aux.
    pose proof dot_prod_squared_dec a b as [? | ?].
    * (** A = B *)
      subst.
      pose proof dot_prod_squared_non_neg _ _ H; subst.
      apply cross_prod_self.
    * (** A != B *)
      remember (cross_prod (build_vec c a) (build_vec c d)) as z0;
      remember (dot_prod (build_vec a b) (build_vec a b)) as z1.
      rewrite Hcab_ in H_aux; rewrite Hdab_ in H_aux; simpl in H_aux.
      nia.
  }
  assert (cross_prod (build_vec a d) (build_vec c a) = 0) as Hdca_.
  {
    assert (cross_prod (build_vec a d) (build_vec c a) =
          - cross_prod (build_vec c a) (build_vec c d) +
            cross_prod (build_vec c a) (build_vec c a)). { unfold cross_prod; simpl; nia. }
    pose proof cross_prod_self (build_vec c a).
    lia.
  }
  assert (cross_prod (build_vec c b) (build_vec c a) = 0) as Hbca_.
  {
    unfold cross_prod in Hcab; unfold cross_prod. simpl in *; nia.
  }
  assert (cross_prod (build_vec b c) (build_vec b d) = 0).
  {
    pose proof aux2 (build_vec c a) (build_vec a d) (build_vec c b) as H_aux.
    pose proof dot_prod_squared_dec c a as [? | ?].
    * (** C = A *)
      subst.
      assert (cross_prod (build_vec b a) (build_vec b d) =
              cross_prod (build_vec b d) (build_vec b d) -
              cross_prod (build_vec d a)(build_vec d b)). { unfold cross_prod; simpl; nia. }
      pose proof cross_prod_self (build_vec b d).
      lia.
    * (** C != A *)
      rewrite Hbca_ in H_aux; rewrite Hdca_ in H_aux.
      simpl in H_aux.
      remember (cross_prod (build_vec a d) (build_vec c b)) as z0;
      remember (dot_prod (build_vec c a) (build_vec c a)) as z1.
      assert (z0 = 0). { nia. }
      assert (cross_prod (build_vec b c) (build_vec b d) =
              cross_prod (build_vec b c) (build_vec b c) +
              cross_prod (build_vec c a) (build_vec c b) +
              cross_prod (build_vec a d) (build_vec c b)). { unfold cross_prod; simpl; nia. }
      pose proof cross_prod_self (build_vec b c).
      lia.
  }
  split; tauto.
Qed.

Lemma segment_mid_trans_left : forall q b u v,
  colinear b u v ->
  at_mid b u v ->
  colinear q u b ->
  at_mid q u b ->
  colinear q u v /\ at_mid q u v.
Proof.
  intros q b u v Hub Hbmid Huq Hqmid.
  pose proof mid_colinear_4point u b v q
    (colinear_perm321 _ _ _ Hub) Huq Hqmid as [Hvuq _].
  assert (Hquv : colinear q u v).
  { apply colinear_perm321. exact Hvuq. }
  split.
  - exact Hquv.
  - pose proof metric_nonneg (build_vec q u).
    pose proof metric_nonneg (build_vec q b).
    pose proof metric_nonneg (build_vec u b).
    pose proof metric_nonneg (build_vec u v).
    pose proof metric_nonneg (build_vec b v).
    pose proof metric_nonneg (build_vec q v).
    unfold colinear, parallel, at_mid, backward_or_perp,
           cross_prod, dot_prod, build_vec in *.
    simpl in *.
    nia.
Qed.

Lemma segment_mid_trans_right : forall q b u v,
  colinear b u v ->
  at_mid b u v ->
  colinear q b v ->
  at_mid q b v ->
  colinear q u v /\ at_mid q u v.
Proof.
  intros q b u v Hub Hbmid Hqv Hqmid.
  pose proof mid_colinear_4point b v u q
    (colinear_perm213 _ _ _ Hub) Hqv Hqmid as [_ Hvuq].
  assert (Hquv : colinear q u v).
  { apply colinear_perm321. exact Hvuq. }
  split.
  - exact Hquv.
  - pose proof metric_nonneg (build_vec q u).
    pose proof metric_nonneg (build_vec q b).
    pose proof metric_nonneg (build_vec q v).
    pose proof metric_nonneg (build_vec u b).
    pose proof metric_nonneg (build_vec u v).
    pose proof metric_nonneg (build_vec b v).
    unfold colinear, parallel, at_mid, backward_or_perp,
           cross_prod, dot_prod, build_vec in *.
    simpl in *.
    nia.
Qed.

(** Print aux. *)
(* forall v v1 v2 : vec,
dot_prod v1 v2 * dot_prod v v =
dot_prod v1 v * dot_prod v2 v + cross_prod v1 v * cross_prod v2 v *)
(** Print aux2. *)
(* forall v v1 v2 : vec,
cross_prod v1 v2 * dot_prod v v =
cross_prod v1 v * dot_prod v2 v - cross_prod v2 v * dot_prod v1 v *)

Lemma point_in_tri_col_mid : forall p a b c,
  ~ ccw a b c ->
  colinear p b c ->
  at_mid p b c ->
  point_in_triangle p a b c.
Proof.
  intros.
  pose proof (ccw_trichotomy c b a) as [[? | ?] | ?].
  - clear H. left. split; [tauto|].
    repeat split.
    + (** LE a->b a->p *)
      into_vec_prod.
      pose proof aux2 (build_vec c b) (build_vec b a) (build_vec p b).
      assert (cross_prod (build_vec b a) (build_vec c b) < 0) as _H1.
      {
        assert (cross_prod (build_vec c a) (build_vec c b) =
                cross_prod (build_vec c b) (build_vec c b) +
                cross_prod (build_vec b a) (build_vec c b)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec c b).
        nia.
      }
      assert (dot_prod (build_vec p b) (build_vec c b) >= 0) as _H2.
      {
        assert (dot_prod (build_vec p b) (build_vec c b) =
                dot_prod (build_vec p b) (build_vec p b) -
                dot_prod (build_vec p b) (build_vec p c)).
        { unfold dot_prod; simpl; nia. }
        pose proof metric_nonneg (build_vec p b).
        nia.
      }
      assert (cross_prod (build_vec p b) (build_vec c b) = 0) as _H3.
      {
        assert (cross_prod (build_vec p b) (build_vec c b) =
                cross_prod (build_vec p b) (build_vec p b) -
                cross_prod (build_vec p b) (build_vec p c)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec p b).
        nia.
      }
      assert (cross_prod (build_vec b a) (build_vec p b) *
              dot_prod (build_vec c b) (build_vec c b) <= 0) as _H.
      { nia. }
      clear H; rename _H into H.
      assert (cross_prod (build_vec a b) (build_vec a p) =
              cross_prod (build_vec b a) (build_vec p b)) as _H.
      {
        assert (cross_prod (build_vec a b) (build_vec a p) =
                cross_prod (build_vec b a) (build_vec b a) +
                cross_prod (build_vec b a) (build_vec p b)) as _H.
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec b a).
        nia.
      }
      rewrite _H.
      pose proof dot_prod_squared_dec c b as [? | ?].
      * (** c = b *)
        subst.
        pose proof dot_prod_squared_non_neg p b H1.
        subst.
        unfold cross_prod; simpl; nia.
      * (** c != b *)
        nia.
    + (** LE b->c b->p *)
      pose proof cross_prod_self (build_vec p b).
      into_vec_prod.
      assert (cross_prod (build_vec b c) (build_vec b p) =
              cross_prod (build_vec p b) (build_vec p b) +
              cross_prod (build_vec p b) (build_vec p c)).
      { unfold cross_prod; simpl; nia. }
      rewrite H0, H in H2; simpl; nia.

    + (** LE c->a c->p *)
      into_vec_prod.
      pose proof aux2 (build_vec c b) (build_vec b a) (build_vec c p).
      assert (cross_prod (build_vec b a) (build_vec c b) < 0) as _H1.
      {
        assert (cross_prod (build_vec c a) (build_vec c b) =
                cross_prod (build_vec c b) (build_vec c b) +
                cross_prod (build_vec b a) (build_vec c b)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec c b).
        nia.
      }
      assert (dot_prod (build_vec c p) (build_vec c b) >= 0) as _H2.
      {
        assert (dot_prod (build_vec c p) (build_vec c b) =
                dot_prod (build_vec c p) (build_vec c p) -
                dot_prod (build_vec p b) (build_vec p c)).
        { unfold dot_prod; simpl; nia. }
        pose proof metric_nonneg (build_vec c p).
        nia.
      }
      assert (cross_prod (build_vec c p) (build_vec c b) = 0) as _H3.
      {
        assert (cross_prod (build_vec c p) (build_vec c b) =
                cross_prod (build_vec c p) (build_vec c p) +
                cross_prod (build_vec p b) (build_vec p c)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec c p).
        nia.
      }
      assert (cross_prod (build_vec b a) (build_vec c p) *
              dot_prod (build_vec c b) (build_vec c b) <= 0) as _H.
      { nia. }
      clear H; rename _H into H.
      assert (cross_prod (build_vec c a) (build_vec c p) =
              cross_prod (build_vec b a) (build_vec c p)) as _H.
      {
        assert (cross_prod (build_vec c a) (build_vec c p) =
                cross_prod (build_vec c p) (build_vec c p) -
                cross_prod (build_vec p b) (build_vec p c) +
                cross_prod (build_vec b a) (build_vec c p)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec c p).
        nia.
      }
      rewrite _H; clear _H.
      pose proof dot_prod_squared_dec c b as [? | ?].
      * (** c = b *)
        subst.
        pose proof dot_prod_squared_non_neg p b H1.
        subst.
        unfold cross_prod; simpl; nia.
      * (** c != b *)
        nia.
  - clear H. right. split; [apply colinear_perm321; tauto|].
    right; left. split; tauto.
  - apply ccw_cyclicity in c0; contradiction.
Qed.

(*
ccw r p0 q
H0: colinear p p0 q /\ at_mid p p0 q
-------------------------------------
p in Δp0_r_q = Δr_q_p0
*)
Lemma point_in_tri_col_mid' : forall p a b c,
  ccw a c b ->
  colinear p b c ->
  at_mid p b c ->
  point_in_triangle p a b c.
Proof.
  intros.
  pose proof point_in_tri_col_mid p a b c as _H.
  assert (~ ccw a b c) as Hn_ccw.
  { unfold ccw, left_than, cross_prod in *; simpl in *; nia. }
  specialize (_H Hn_ccw H0 H1); clear Hn_ccw.
  tauto.
Qed.

Lemma point_in_tri_weak_edge : forall p q a b,
  weak_rev_ccw p a b ->
  colinear q p b ->
  at_mid q p b ->
  point_in_triangle q a b p.
Proof.
  intros p q a b Hab Hqcol Hqmid.
  destruct Hab as [Hab | [Hab_col Hab_mid]].
  - apply point_in_tri_col_mid'; try exact Hab.
    + rewrite colinear_comm. exact Hqcol.
    + rewrite at_mid_comm. exact Hqmid.
  - unfold point_in_triangle, weak_rev_ccw, ccw, colinear, at_mid,
           left_equal, left_than, parallel, backward_or_perp, build_vec,
           cross_prod, dot_prod in *; simpl in *.
    nia.
Qed.

Lemma point_in_tri_incl_left_by_edges : forall p a b c q,
  ccw p a c ->
  left_equal (build_vec c a) (build_vec c b) ->
  left_equal (build_vec a p) (build_vec a b) ->
  left_equal (build_vec p c) (build_vec p b) ->
  point_in_triangle q b a p ->
  point_in_triangle q c a p.
Proof.
  intros p a b c q Hpac Hcab Hapb Hpcb Hq.
  left; split; [exact Hpac |].
  destruct Hq as [Hq | [Hq_col Hq_seg]].
  - unfold point_in_triangle, ccw, left_equal, left_than, colinear,
           parallel, at_mid, backward_or_perp, build_vec, cross_prod,
           dot_prod in *; simpl in *; nia.
  - destruct Hq_seg as [[Hcol Hmid] | [[Hcol Hmid] | [Hcol Hmid]]].
    + repeat split.
      * eapply (left_equal_segment c a b a q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment a p b a q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment p c b a q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
    + repeat split.
      * eapply (left_equal_segment c a a p q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment a p a p q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment p c a p q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
    + repeat split.
      * eapply (left_equal_segment c a p b q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment a p p b q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment p c p b q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
Qed.

Lemma point_in_tri_incl_right_by_edges : forall p a b c q,
  ccw p a c ->
  left_equal (build_vec c a) (build_vec c b) ->
  left_equal (build_vec a p) (build_vec a b) ->
  left_equal (build_vec p c) (build_vec p b) ->
  point_in_triangle q c b p ->
  point_in_triangle q c a p.
Proof.
  intros p a b c q Hpac Hcab Hapb Hpcb Hq.
  left; split; [exact Hpac |].
  destruct Hq as [Hq | [Hq_col Hq_seg]].
  - unfold point_in_triangle, ccw, left_equal, left_than, colinear,
           parallel, at_mid, backward_or_perp, build_vec, cross_prod,
           dot_prod in *; simpl in *; nia.
  - destruct Hq_seg as [[Hcol Hmid] | [[Hcol Hmid] | [Hcol Hmid]]].
    + repeat split.
      * eapply (left_equal_segment c a c b q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment a p c b q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment p c c b q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
    + repeat split.
      * eapply (left_equal_segment c a b p q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment a p b p q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment p c b p q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
    + repeat split.
      * eapply (left_equal_segment c a p c q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment a p p c q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
      * eapply (left_equal_segment p c p c q); try eassumption;
        unfold ccw, left_equal, left_than, build_vec, cross_prod in *;
        simpl in *; nia.
Qed.

Local Ltac solve_point_in_tri :=
  unfold point_in_triangle, weak_rev_ccw, ccw, colinear, at_mid,
         left_equal, left_than, parallel, backward_or_perp, build_vec,
         cross_prod, dot_prod in *; simpl in *;
  first
    [ left; repeat split; nia
    | right; split; [nia | left; split; nia]
    | right; split; [nia | right; left; split; nia]
    | right; split; [nia | right; right; split; nia] ].

Lemma point_in_tri_pop_left_weak : forall p a b c q,
  weak_rev_ccw p c b ->
  weak_rev_ccw p c a ->
  weak_rev_ccw p b a ->
  ~ ccw a b c ->
  point_in_triangle q b a p ->
  point_in_triangle q c a p.
Proof.
  intros p a b c q Hcb Hca Hba Hn Hq.
  destruct Hca as [Hca | [Hca_col Hca_mid]].
  - pose proof point_in_tri_weak_pop p a b c Hcb (or_introl Hca) Hba Hn
      as Hbtri.
    destruct Hbtri as [[Hpac [Hcab [Hapb Hpcb]]] | [Hbcol Hbseg]].
    + exact (point_in_tri_incl_left_by_edges p a b c q Hpac Hcab Hapb Hpcb Hq).
    + exfalso.
      unfold ccw, colinear, left_than, parallel, build_vec, cross_prod in *;
      simpl in *; nia.
  - destruct Hcb as [Hcb | [Hcb_col Hcb_mid]];
    destruct Hba as [Hba | [Hba_col Hba_mid]];
    destruct Hq as [Hq | [Hq_col Hq_seg]].
    all: try solve_point_in_tri.
    all: destruct Hq_seg as [[Hq_seg_col Hq_seg_mid] |
                             [[Hq_seg_col Hq_seg_mid] |
                              [Hq_seg_col Hq_seg_mid]]];
         try solve_point_in_tri.
    + pose proof (segment_mid_trans_left q a b p)
        (colinear_perm321 _ _ _ Hba_col) Hba_mid
        Hq_seg_col Hq_seg_mid as [Hqbp_col Hqbp_mid].
      pose proof (segment_mid_trans_right q b c p)
        (colinear_perm321 _ _ _ Hcb_col) Hcb_mid
        Hqbp_col Hqbp_mid as [Hqcp_col Hqcp_mid].
      right. split; [apply colinear_perm231; exact Hca_col|].
      right; right. split.
      * apply colinear_perm132. exact Hqcp_col.
      * apply at_mid_comm. exact Hqcp_mid.
    + pose proof (segment_mid_trans_right q b c p)
        (colinear_perm321 _ _ _ Hcb_col) Hcb_mid
        (colinear_perm132 _ _ _ Hq_seg_col)
        (proj1 (at_mid_comm _ _ _) Hq_seg_mid) as [Hqcp_col Hqcp_mid].
      right. split; [apply colinear_perm231; exact Hca_col|].
      right; right. split.
      * apply colinear_perm132. exact Hqcp_col.
      * apply at_mid_comm. exact Hqcp_mid.
Qed.

Lemma point_in_tri_pop_right_weak : forall p a b c q,
  weak_rev_ccw p c b ->
  weak_rev_ccw p c a ->
  weak_rev_ccw p b a ->
  ~ ccw a b c ->
  point_in_triangle q c b p ->
  point_in_triangle q c a p.
Proof.
  intros p a b c q Hcb Hca Hba Hn Hq.
  destruct Hca as [Hca | [Hca_col Hca_mid]].
  - pose proof point_in_tri_weak_pop p a b c Hcb (or_introl Hca) Hba Hn
      as Hbtri.
    destruct Hbtri as [[Hpac [Hcab [Hapb Hpcb]]] | [Hbcol Hbseg]].
    + exact (point_in_tri_incl_right_by_edges p a b c q Hpac Hcab Hapb Hpcb Hq).
    + exfalso.
      unfold ccw, colinear, left_than, parallel, build_vec, cross_prod in *;
      simpl in *; nia.
  - destruct Hcb as [Hcb | [Hcb_col Hcb_mid]];
    destruct Hba as [Hba | [Hba_col Hba_mid]];
    destruct Hq as [Hq | [Hq_col Hq_seg]].
    all: try solve_point_in_tri.
    all: destruct Hq_seg as [[Hq_seg_col Hq_seg_mid] |
                             [[Hq_seg_col Hq_seg_mid] |
                              [Hq_seg_col Hq_seg_mid]]];
         try solve_point_in_tri.
    + pose proof (segment_mid_trans_left q b c p)
        (colinear_perm321 _ _ _ Hcb_col) Hcb_mid
        Hq_seg_col Hq_seg_mid as [Hqcp_col Hqcp_mid].
      right. split; [apply colinear_perm231; exact Hca_col|].
      right; right. split.
      * apply colinear_perm132. exact Hqcp_col.
      * apply at_mid_comm. exact Hqcp_mid.
    + pose proof (segment_mid_trans_right q b c p)
        (colinear_perm321 _ _ _ Hcb_col) Hcb_mid
        Hq_seg_col Hq_seg_mid as [Hqcp_col Hqcp_mid].
      right. split; [apply colinear_perm231; exact Hca_col|].
      right; right. split.
      * apply colinear_perm132. exact Hqcp_col.
      * apply at_mid_comm. exact Hqcp_mid.
Qed.

(** dot_prod *)

(** =========================================== *)

(** Remove strict is non-trivial ... *)
Lemma point_in_tri_incl : forall p a b c,
  point_in_triangle b c a p ->
  ccw p a c ->
  ccw b p a ->
  forall q,
  point_in_triangle q b a p ->
  point_in_triangle q c a p.
Proof.
  intros p a b c Hb Hpac Hbpa q Hq.
  destruct Hb as [Hb | Hb].
  - destruct Hq as [Hq | Hq].
    + left.
      unfold point_in_triangle, ccw, left_equal, left_than in *.
      unfold cross_prod, build_vec in *.
      simpl in *.
      nia.
    + exfalso.
      destruct Hq as [Hcol _].
      unfold ccw, colinear, left_than, parallel, cross_prod, build_vec in *.
      simpl in *.
      nia.
  - exfalso.
    destruct Hb as [Hcol _].
    unfold ccw, colinear, left_than, parallel, cross_prod, build_vec in *.
    simpl in *.
    nia.
Qed.

Lemma point_in_tri_incl' : forall p a b c,
  point_in_triangle b c a p ->
  ccw c p a ->
  ccw c p b ->
  forall q,
  point_in_triangle q c b p ->
  point_in_triangle q c a p.
Proof.
  intros p a b c H Hcpa Hcpb q Hq.
  rewrite point_in_tri_cyclicity in H.
  rewrite point_in_tri_cyclicity in Hq.
  rewrite point_in_tri_cyclicity.
  exact (point_in_tri_incl c p b a H Hcpa
           (ccw_cyclicity_2 _ _ _ Hcpb) q Hq).
Qed.

(* split first point p0 with convex hull CH *)
Fixpoint point_in_hull_aux (p p0 p1: point) (CH: list point) :=
  match CH with
  (** hull is not empty, proceed from `p1` to `p2` *)
  | p2 :: l => point_in_triangle p p1 p2 p0 \/
               point_in_hull_aux p p0 p2 l
  | nil => False
  end.

Definition point_in_hull (p: point) (CH: list point) :=
  match CH with
  | p0 :: p1 :: p2 :: l => point_in_hull_aux p p0 p1 (p2 :: l)
  | p0 :: p1 :: nil => colinear p p0 p1 /\ at_mid p p0 p1
  | _ => False
  end.

(* Deprecated *)
(* Fixpoint point_in_hull (p p0: point) (CH: list point) :=
  match CH with
  | p1 :: l' =>
    match l' with
    | p2 :: _ => point_in_triangle p p1 p2 p0 \/ point_in_hull p p0 l'
    | _ => colinear p p0 p1 /\ at_mid p p0 p1
    end
  | _ => False
  end. *)

(** l ⊆ (p :: CH) *)
Definition is_max_hull' (p: point) (CH l: list point) :=
  Forall (fun q => point_in_hull q (p :: CH)) l.

Lemma point_in_hull_last_tri : forall p p0 p1 p2,
  point_in_triangle p p1 p2 p0 ->
  forall CH,
  point_in_hull p (p0 :: p1 :: p2 :: CH).
Proof.
  induction CH; simpl; left; tauto.
Qed.

Lemma forall_false_elim : forall a l,
  Forall (fun _ : point => False) (a :: l) -> False.
Proof.
  intros.
  pose proof Forall_inv as H0.
  specialize (H0 _ (fun _ : point => False) a l H).
  tauto.
Qed.

Lemma point_in_hull_cons_iff_weak : forall q p a b l,
  weak_rev_ccw_list p (b :: a :: l) ->
  (
    point_in_hull q (p :: b :: a :: l) <->
    point_in_hull q (p :: a :: l) \/
    point_in_triangle q b a p
  ).
Proof.
  intros q p a b l Hweak.
  induction l; intros.
  - simpl; split; intros H.
    + right. tauto.
    + destruct H as [Hseg | Htri]; [| tauto].
      simpl in Hweak.
      destruct Hweak as [Hb _].
      rewrite Forall_weak_rev_ccw_cons_iff in Hb.
      destruct Hb as [Hba _].
      left.
      destruct Hseg as [Hcol Hmid].
      exact (point_in_tri_weak_edge p q b a Hba Hcol Hmid).
  - split; intros H.
    + pose proof weak_rev_ccw_list_remove_middle p [b; a] [a0] l Hweak as Hweak'.
      specialize (IHl Hweak').
      simpl in H.
      simpl.
      tauto.
    + simpl in H.
      simpl.
      tauto.
Qed.

Lemma is_max_hull'_cons_iff_weak : forall p a b l T,
  weak_rev_ccw_list p (b :: a :: l) ->
  (
    is_max_hull' p (b :: a :: l) T <->
    Forall (fun q : point => point_in_hull q (p :: a :: l) \/
                             point_in_triangle q b a p) T
  ).
Proof.
  unfold is_max_hull'. intros.
  induction T.
  - rewrite !Forall_nil_iff. tauto.
  - rewrite !Forall_cons_iff.
    pose proof point_in_hull_cons_iff_weak a0 p a b l H.
    tauto.
Qed.

(* ===== Moved general lemmas: from Graham_Scan.v ===== *)

Lemma is_max_hull'_pop'_g : forall p a b c l T,
  g_rev_ccw_list p (c :: b :: a :: l) ->
  ~ ccw a b c ->
  is_max_hull' p (c :: b :: a :: l) T ->
  is_max_hull' p (c :: a :: l) T.
Proof.
  unfold is_max_hull' in *.
  intros p a b c l T Hg Hn Hmax.
  simpl in Hg.
  destruct Hg as [Hc [Hb _]].
  rewrite Forall_g_rev_ccw_cons_iff in Hc.
  destruct Hc as [Hcb Hc].
  rewrite Forall_g_rev_ccw_cons_iff in Hc.
  destruct Hc as [Hca _].
  rewrite Forall_g_rev_ccw_cons_iff in Hb.
  destruct Hb as [Hba _].
  apply g_rev_ccw_iff_weak_rev_ccw in Hcb.
  apply g_rev_ccw_iff_weak_rev_ccw in Hca.
  apply g_rev_ccw_iff_weak_rev_ccw in Hba.
  rewrite Forall_forall in Hmax.
  rewrite Forall_forall.
  intros x HIn.
  specialize (Hmax x HIn).
  simpl in Hmax |- *.
  destruct Hmax as [Hcbp | [Hbap | Htail]].
  - left.
    exact (point_in_tri_pop_right_weak p a b c x Hcb Hca Hba Hn Hcbp).
  - left.
    exact (point_in_tri_pop_left_weak p a b c x Hcb Hca Hba Hn Hbap).
  - right. exact Htail.
Qed.

(* ===== Edge-based maximality equivalence ===== *)

(*** ========== Definition ========== ***)

(** Auxiliary recursive function to traverse each edge of hull *)
(* split first point `p0` from the hull *)
(* record two leading hull vertices as `p1` `p2` *)
Fixpoint point_in_hull_edges_aux_ (p p0 p1: point) (CH: list point) :=
  match CH with
  (** hull is not empty, proceed from `p1->p2` to `p2->p3` *)
  | p2 :: l => point_in_hull_edges_aux_ p p0 p2 l /\
               left_equal (build_vec p1 p2) (build_vec p1 p)
  (** `p2` is last point, add the last edge `p2->p0` *)
  | nil => left_equal (build_vec p1 p0) (build_vec p1 p)
  end.

(** Define if point `p` sets inside the hull `CH`. *)
(* split first point `p0` from the hull *)
(* in order to facilitate recursion. *)
Definition point_in_hull_edges (p : point) (CH: list point) :=
  match CH with
  (** hull := `p0 p1 ...`, recurse into _aux *)
  | p0 :: p1 :: p2 :: l => left_equal (build_vec p0 p1) (build_vec p0 p) /\
                     point_in_hull_edges_aux_ p p0 p1 (p2 :: l)
  (** hull := `p0 p1`, check if p is on segment `p0->p1` *)
  | p0 :: p1 :: nil => colinear p p0 p1 /\ at_mid p p0 p1
  (** hull := `p0`, simply eliminate this case *)
  | _ => False
  end.

Definition is_max_hull'_edges (CH l: list point) :=
  Forall (fun q => point_in_hull_edges q CH) l.


(*** ========== Proof ========== ***)

Lemma point_in_triangle_halfplane : forall p a b c u v,
  point_in_triangle p a b c ->
  ccw c b a ->
  left_equal (build_vec u v) (build_vec u a) ->
  left_equal (build_vec u v) (build_vec u b) ->
  left_equal (build_vec u v) (build_vec u c) ->
  left_equal (build_vec u v) (build_vec u p).
Proof.
  intros p a b c u v Htri Hccw Hla Hlb Hlc.
  unfold point_in_triangle in Htri.
  destruct Htri as [Htri | Htri].
  - unfold ccw, left_equal, left_than, cross_prod, build_vec in *.
    simpl in *.
    nia.
  - destruct Htri as [Hcol _].
    unfold ccw, colinear, parallel, left_than, cross_prod, build_vec in *.
    simpl in *.
    nia.
Qed.

Lemma point_in_hull_equiv_two_points : forall p p0 p1,
  point_in_hull p (p0 :: p1 :: nil) <->
  point_in_hull_edges p (p0 :: p1 :: nil).
Proof.
  intros.
  simpl.
  tauto.
Qed.

Lemma point_in_hull_equiv_three_points : forall p p0 p1 p2,
  ccw p1 p0 p2 ->
  point_in_hull p (p0 :: p1 :: p2 :: nil) <->
  point_in_hull_edges p (p0 :: p1 :: p2 :: nil).
Proof.
  intros p p0 p1 p2 Hccw.
  simpl.
  split; intros H.
  - unfold point_in_triangle in H.
    destruct H as [[H | H] | Hfalse].
    + destruct H as [_ [H12 [H20 H01]]].
      repeat split; tauto.
    + destruct H as [Hcol _].
      unfold ccw, colinear, left_than, parallel, cross_prod, build_vec in *.
      simpl in *.
      nia.
    + contradiction.
  - unfold point_in_triangle.
    destruct H as [H01 [H20 H12]].
    left.
    left.
    repeat split; try tauto.
    apply ccw_cyclicity; exact Hccw.
Qed.

Lemma edge_side_propagate : forall p0 p1 p2 p3 q,
  ccw p1 p0 p2 ->
  ccw p1 p0 p3 ->
  ccw p1 p0 q ->
  ccw p2 p0 p3 ->
  ccw p2 p0 q ->
  ccw p3 p0 q ->
  ccw p2 p1 p3 ->
  left_equal (build_vec p2 p3) (build_vec p2 q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  unfold ccw, left_equal, left_than, cross_prod, build_vec.
  simpl.
  intros.
  nia.
Qed.

Lemma edge_side_backward : forall p0 q prev p1 p2,
  ccw q p0 prev ->
  ccw q p0 p1 ->
  ccw q p0 p2 ->
  ccw prev p0 p1 ->
  ccw prev p0 p2 ->
  ccw p1 p0 p2 ->
  ccw p1 prev p2 ->
  left_equal (build_vec prev p1) (build_vec prev q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  unfold ccw, left_equal, left_than, cross_prod, build_vec.
  simpl.
  intros.
  nia.
Qed.

Lemma edge_side_backward_pivot : forall p0 prev p1 p2,
  ccw prev p0 p1 ->
  ccw prev p0 p2 ->
  ccw p1 p0 p2 ->
  ccw p1 prev p2 ->
  left_equal (build_vec prev p1) (build_vec prev p0) ->
  left_equal (build_vec p1 p2) (build_vec p1 p0).
Proof.
  unfold ccw, left_equal, left_than, cross_prod, build_vec.
  simpl.
  intros.
  nia.
Qed.

Lemma edge_prev_endpoint_left : forall a prev p1,
  ccw prev a p1 ->
  left_equal (build_vec prev p1) (build_vec prev a).
Proof.
  unfold ccw, left_equal, left_than, cross_prod, build_vec.
  simpl.
  intros.
  nia.
Qed.

Lemma rev_consec_ccw_app_inv2 : forall l1 l2,
  rev_consec_ccw (l1 ++ l2) ->
  rev_consec_ccw l2.
Proof.
  intros l1 l2 H.
  induction l1 as [| a l1 IH].
  - exact H.
  - simpl in H.
    destruct H as [_ H].
    apply IH.
    exact H.
Qed.

Lemma rev_consec_ccw_edge_at : forall p0 pre prev p1 p2 post,
  rev_consec_ccw (p0 :: pre ++ prev :: p1 :: p2 :: post) ->
  ccw p1 prev p2.
Proof.
  intros p0 pre prev p1 p2 post H.
  assert (rev_consec_ccw (prev :: p1 :: p2 :: post)).
  {
    apply (rev_consec_ccw_app_inv2 (p0 :: pre)).
    exact H.
  }
  simpl in H0.
  tauto.
Qed.

Lemma rev_consec_ccw_edge_at_tail : forall pre prev p1 p2 post,
  rev_consec_ccw (pre ++ prev :: p1 :: p2 :: post) ->
  ccw p1 prev p2.
Proof.
  intros pre prev p1 p2 post H.
  assert (rev_consec_ccw (prev :: p1 :: p2 :: post)).
  {
    apply (rev_consec_ccw_app_inv2 pre).
    exact H.
  }
  simpl in H0.
  tauto.
Qed.

Lemma point_in_hull_halfplane3_weak : forall p u v p0 p1 p2 CH,
  weak_rev_ccw_list p0 (p1 :: p2 :: CH) ->
  rev_consec_ccw (p1 :: p2 :: CH) ->
  (forall q, In q (p0 :: p1 :: p2 :: CH) ->
    left_equal (build_vec u v) (build_vec u q)) ->
  point_in_hull p (p0 :: p1 :: p2 :: CH) ->
  left_equal (build_vec u v) (build_vec u p).
Proof.
  intros p u v p0 p1 p2 CH Hrev Htail Hall Hhull.
  revert p1 p2 Hrev Htail Hall Hhull.
  induction CH as [| p3 CH IH]; intros p1 p2 Hrev Htail Hall Hhull.
  - simpl in Hhull.
    destruct Hhull as [Htri | Hfalse]; [| contradiction].
    eapply point_in_triangle_halfplane_weak; try exact Htri;
      apply Hall; simpl; tauto.
  - pose proof (point_in_hull_cons_iff_weak p p0 p2 p1 (p3 :: CH) Hrev)
      as [Hiff _].
    specialize (Hiff Hhull).
    destruct Hiff as [Hsmall | Htri].
    + assert (Hrev' : weak_rev_ccw_list p0 (p2 :: p3 :: CH)).
      {
        apply (weak_rev_ccw_list_ind' p0 [p1] (p2 :: p3 :: CH)).
        exact Hrev.
      }
      apply (IH p2 p3 Hrev').
      * simpl in Htail.
        destruct Htail as [_ Htail].
        exact Htail.
      * intros q HIn.
        apply Hall.
        simpl in *.
        tauto.
      * exact Hsmall.
    + eapply point_in_triangle_halfplane_weak; try exact Htri;
        apply Hall; simpl; tauto.
Qed.

Lemma point_in_hull_halfplane_general_weak : forall p u v p0 pre p1 p2 post,
  weak_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  (forall q, In q (p0 :: pre ++ p1 :: p2 :: post) ->
    left_equal (build_vec u v) (build_vec u q)) ->
  point_in_hull p (p0 :: pre ++ p1 :: p2 :: post) ->
  left_equal (build_vec u v) (build_vec u p).
Proof.
  intros p u v p0 pre.
  induction pre as [| x pre IH]; intros p1 p2 post Hrev Hconsec Hall Hhull.
  - simpl in Hrev, Hconsec, Hall, Hhull.
    eapply (point_in_hull_halfplane3_weak p u v p0 p1 p2 post Hrev).
    + exact Hconsec.
    + intros q HIn.
      apply Hall.
      simpl.
      tauto.
    + exact Hhull.
  - destruct pre as [| y pre'].
    + simpl in Hrev, Hconsec, Hall, Hhull.
      pose proof (point_in_hull_cons_iff_weak p p0 p1 x (p2 :: post) Hrev)
        as [Hiff _].
      specialize (Hiff Hhull).
      destruct Hiff as [Hsmall | Htri].
      * assert (Hrev' : weak_rev_ccw_list p0 (p1 :: p2 :: post)).
        {
          apply (weak_rev_ccw_list_ind' p0 [x] (p1 :: p2 :: post)).
          exact Hrev.
        }
        eapply (point_in_hull_halfplane3_weak p u v p0 p1 p2 post Hrev').
        -- destruct Hconsec as [_ Hconsec'].
           exact Hconsec'.
        -- intros q HIn.
           apply Hall.
           simpl in *.
           tauto.
        -- exact Hsmall.
      * eapply point_in_triangle_halfplane_weak; try exact Htri;
          apply Hall; simpl; tauto.
    + simpl in Hrev, Hconsec, Hall, Hhull.
      pose proof (point_in_hull_cons_iff_weak p p0 y x (pre' ++ p1 :: p2 :: post) Hrev)
        as [Hiff _].
      specialize (Hiff Hhull).
      destruct Hiff as [Hsmall | Htri].
      * eapply IH.
        -- apply (weak_rev_ccw_list_ind' p0 [x] (y :: pre' ++ p1 :: p2 :: post)).
           exact Hrev.
        -- destruct Hconsec as [_ Hconsec'].
           exact Hconsec'.
        -- intros q HIn.
           apply Hall.
           simpl in *.
           tauto.
        -- exact Hsmall.
      * eapply point_in_triangle_halfplane_weak; try exact Htri;
          apply Hall; simpl; tauto.
Qed.

Lemma weak_rev_ccw_first_edge_halfplane : forall p q r,
  weak_rev_ccw p q r ->
  left_equal (build_vec p q) (build_vec p r).
Proof.
  intros p q r H.
  destruct H as [H | [Hcol Hmid]];
    unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
           parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
    simpl in *; nia.
Qed.

Lemma weak_rev_ccw_final_edge_halfplane : forall p q r,
  weak_rev_ccw p q r ->
  left_equal (build_vec r p) (build_vec r q).
Proof.
  intros p q r H.
  destruct H as [H | [Hcol Hmid]];
    unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
           parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
    simpl in *; nia.
Qed.

Lemma weak_rev_ccw_edge_to_pivot_halfplane : forall p q r,
  weak_rev_ccw p q r ->
  left_equal (build_vec q r) (build_vec q p).
Proof.
  intros p q r H.
  destruct H as [H | [Hcol Hmid]];
    unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
           parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
    simpl in *; nia.
Qed.

Lemma edge_ray_extend : forall q prev p1 p2,
  ccw p1 prev p2 ->
  colinear q prev p1 ->
  forward_or_perp (build_vec p1 prev) (build_vec p1 q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros q prev p1 p2 Hedge Hcol Hfwd.
  assert (Hnz : dot_prod (build_vec p1 prev) (build_vec p1 prev) > 0).
  {
    pose proof left_than_nonzero2 _ _ Hedge as Hnz.
    rewrite nonzero_iff in Hnz.
    exact Hnz.
  }
  pose proof aux2 (build_vec p1 prev) (build_vec p1 p2) (build_vec p1 q)
    as Haux.
  assert (Hcross : cross_prod (build_vec p1 q) (build_vec p1 prev) = 0).
  {
    unfold colinear, parallel, build_vec, cross_prod in *.
    simpl in *.
    nia.
  }
  unfold ccw, left_equal, left_than, forward_or_perp in *.
  rewrite dot_prod_comm with (v1 := build_vec p1 q) (v2 := build_vec p1 prev)
    in Haux.
  nia.
Qed.

Lemma nested_mid_previous : forall p0 q prev p1,
  colinear prev q p0 ->
  at_mid prev q p0 ->
  colinear p1 q p0 ->
  at_mid p1 q p0 ->
  colinear p1 prev p0 ->
  at_mid p1 prev p0 ->
  at_mid prev q p1.
Proof.
  intros.
  pose proof metric_nonneg (build_vec prev q).
  pose proof metric_nonneg (build_vec prev p1).
  pose proof metric_nonneg (build_vec q p0).
  pose proof metric_nonneg (build_vec q p1).
  pose proof metric_nonneg (build_vec prev p0).
  pose proof metric_nonneg (build_vec p1 p0).
  pose proof metric_nonneg (build_vec p1 prev).
  unfold colinear, at_mid, parallel, backward_or_perp,
         build_vec, cross_prod, dot_prod in *.
  simpl in *.
  nia.
Qed.

Lemma weak_previous_forward : forall p0 q prev p1,
  colinear p0 q prev ->
  at_mid prev q p0 ->
  colinear p0 q p1 ->
  at_mid p1 q p0 ->
  colinear p0 prev p1 ->
  at_mid p1 prev p0 ->
  forward_or_perp (build_vec p1 prev) (build_vec p1 q).
Proof.
  intros p0 q prev p1 Hqprev Hqprev_mid Hqp1 Hqp1_mid
    Hprevp1 Hprevp1_mid.
  apply at_mid_fwd2.
  pose proof (nested_mid_previous p0 q prev p1
    (colinear_perm321 _ _ _ Hqprev) Hqprev_mid
    (colinear_perm321 _ _ _ Hqp1) Hqp1_mid
    (colinear_perm321 _ _ _ Hprevp1) Hprevp1_mid) as Hmid.
  exact Hmid.
Qed.

Lemma edge_side_backward_weak : forall p0 q prev p1 p2,
  weak_rev_ccw p0 q prev ->
  weak_rev_ccw p0 q p1 ->
  weak_rev_ccw p0 q p2 ->
  weak_rev_ccw p0 prev p1 ->
  weak_rev_ccw p0 prev p2 ->
  weak_rev_ccw p0 p1 p2 ->
  ccw p1 prev p2 ->
  left_equal (build_vec prev p1) (build_vec prev q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 q prev p1 p2 Hqprev Hqp1 Hqp2 Hprevp1 Hprevp2
    Hp1p2 Hedge Hprev.
  destruct Hqprev as [Hqprev | [Hqprev_col Hqprev_mid]];
  destruct Hqp1 as [Hqp1 | [Hqp1_col Hqp1_mid]];
  destruct Hqp2 as [Hqp2 | [Hqp2_col Hqp2_mid]];
  destruct Hprevp1 as [Hprevp1 | [Hprevp1_col Hprevp1_mid]];
  destruct Hprevp2 as [Hprevp2 | [Hprevp2_col Hprevp2_mid]];
  destruct Hp1p2 as [Hp1p2 | [Hp1p2_col Hp1p2_mid]];
  try (unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
              parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
       simpl in *; nia).
  - eapply edge_ray_extend; try exact Hedge.
    + unfold colinear, parallel, build_vec, cross_prod in *.
      simpl in *.
      nia.
    + eapply weak_previous_forward; eauto.
  - eapply edge_ray_extend; try exact Hedge.
    + unfold colinear, parallel, build_vec, cross_prod in *.
      simpl in *.
      nia.
    + eapply weak_previous_forward; eauto.
Qed.

Lemma edge_side_propagate_weak : forall p0 p1 p2 p3 q,
  weak_rev_ccw p0 p1 p2 ->
  weak_rev_ccw p0 p1 p3 ->
  weak_rev_ccw p0 p1 q ->
  weak_rev_ccw p0 p2 p3 ->
  weak_rev_ccw p0 p2 q ->
  weak_rev_ccw p0 p3 q ->
  ccw p2 p1 p3 ->
  left_equal (build_vec p2 p3) (build_vec p2 q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 p1 p2 p3 q H12 H13 H1q H23 H2q H3q Hedge Hlater.
  destruct H23 as [H23 | [H23col H23mid]].
  - repeat match goal with
    | H : weak_rev_ccw _ _ _ |- _ => destruct H as [H | [H ?]]
    end;
    unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
           parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
    simpl in *; nia.
  - destruct H2q as [H2q | [H2qcol H2qmid]].
    + repeat match goal with
      | H : weak_rev_ccw _ _ _ |- _ => destruct H as [H | [H ?]]
      end;
      unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
             parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
      simpl in *; nia.
    + exact (left_equal_segment p1 p2 p2 p0 q
        ltac:(unfold left_equal, cross_prod, build_vec; simpl; nia)
        (weak_rev_ccw_edge_to_pivot_halfplane p0 p1 p2 H12)
        (colinear_perm321 _ _ _ H2qcol)
        H2qmid).
Qed.

Lemma first_edge_vertices_halfplane_weak : forall p0 p1 CH q,
  weak_rev_ccw_list p0 (p1 :: CH) ->
  In q (p0 :: p1 :: CH) ->
  left_equal (build_vec p0 p1) (build_vec p0 q).
Proof.
  intros p0 p1 CH q Hrev HIn.
  simpl in HIn.
  destruct HIn as [-> | [-> | HIn]].
  - unfold left_equal, cross_prod, build_vec.
    simpl.
    nia.
  - unfold left_equal, cross_prod, build_vec.
    simpl.
    nia.
  - simpl in Hrev.
    destruct Hrev as [Hfor _].
    rewrite Forall_weak_rev_ccw_forall in Hfor.
    exact (weak_rev_ccw_first_edge_halfplane p0 p1 q (Hfor q HIn)).
Qed.

Lemma hull_edge_later_halfplane_weak : forall p0 p1 p2 CH q,
  weak_rev_ccw_list p0 (p1 :: p2 :: CH) ->
  rev_consec_ccw (p1 :: p2 :: CH) ->
  In q CH ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 p1 p2 CH q Hrev Hconsec HIn.
  revert p1 p2 q Hrev Hconsec HIn.
  induction CH as [| p3 CH IH]; intros p1 p2 q Hrev Hconsec HIn.
  - contradiction.
  - simpl in HIn.
    destruct HIn as [-> | HIn].
    + simpl in Hconsec.
      destruct Hconsec as [Hedge _].
      unfold ccw, left_equal, left_than, cross_prod, build_vec in *.
      simpl in *.
      nia.
    + assert (Hrev' : weak_rev_ccw_list p0 (p2 :: p3 :: CH)).
      {
        apply (weak_rev_ccw_list_ind' p0 [p1] (p2 :: p3 :: CH)).
        exact Hrev.
      }
      assert (Hlater : left_equal (build_vec p2 p3) (build_vec p2 q)).
      {
        apply (IH p2 p3 q Hrev').
        - simpl in Hconsec.
          destruct Hconsec as [_ Htail].
          exact Htail.
        - exact HIn.
      }
      eapply (edge_side_propagate_weak p0 p1 p2 p3 q); try exact Hlater.
      * simpl in Hrev.
        destruct Hrev as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev.
        destruct Hrev as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev.
        destruct Hrev as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev'.
        destruct Hrev' as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev'.
        destruct Hrev' as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev'.
        destruct Hrev' as [_ Hrev''].
        simpl in Hrev''.
        destruct Hrev'' as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        exact HIn.
      * simpl in Hconsec.
        tauto.
Qed.


Lemma hull_edge_previous_halfplane_weak : forall p0 pre prev p1 p2 post q,
  weak_rev_ccw_list p0 (pre ++ prev :: p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ prev :: p1 :: p2 :: post) ->
  In q (p0 :: pre) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 pre.
  pattern pre.
  apply rev_ind.
  - intros prev p1 p2 post q Hrev _ HIn.
    simpl in HIn.
    destruct HIn as [Hq | []].
    subst q.
    simpl in Hrev.
    destruct Hrev as [_ Hrev'].
    simpl in Hrev'.
    destruct Hrev' as [Hp1 _].
    rewrite Forall_weak_rev_ccw_forall in Hp1.
    apply weak_rev_ccw_edge_to_pivot_halfplane.
    apply Hp1.
    simpl.
    tauto.
  - intros x l IH prev p1 p2 post q Hrev Hconsec HIn.
    rewrite <- app_assoc in Hrev, Hconsec.
    pose proof (weak_rev_ccw_list_ind' p0 l (x :: prev :: p1 :: p2 :: post)
      Hrev) as Htail.
    pose proof (proj1 (weak_rev_ccw_list_app_iff p0 l
      (x :: prev :: p1 :: p2 :: post)) Hrev) as [_ [_ Hbetween]].
    simpl in Htail.
    destruct Htail as [Hx Hrest].
    rewrite Forall_weak_rev_ccw_forall in Hx.
    simpl in Hrest.
    destruct Hrest as [Hprev Hrest].
    rewrite Forall_weak_rev_ccw_forall in Hprev.
    simpl in Hrest.
    destruct Hrest as [Hp1 _].
    rewrite Forall_weak_rev_ccw_forall in Hp1.
    assert (Hconsec' : rev_consec_ccw
      ((l ++ [x]) ++ prev :: p1 :: p2 :: post)).
    {
      replace (l ++ [x] ++ prev :: p1 :: p2 :: post)
        with ((l ++ [x]) ++ prev :: p1 :: p2 :: post) in Hconsec
        by (rewrite <- app_assoc; reflexivity).
      exact Hconsec.
    }
    assert (Hconsec_tail : rev_consec_ccw
      (l ++ x :: prev :: p1 :: p2 :: post)).
    {
      replace (l ++ x :: prev :: p1 :: p2 :: post)
        with ((l ++ [x]) ++ prev :: p1 :: p2 :: post)
        by (rewrite <- app_assoc; reflexivity).
      exact Hconsec'.
    }
    simpl in HIn.
    destruct HIn as [Hq0 | HIn].
    + subst q.
      apply weak_rev_ccw_edge_to_pivot_halfplane.
      apply Hp1.
      simpl.
      tauto.
    + rewrite in_app_iff in HIn.
      destruct HIn as [HIn | HIn].
      * assert (Hprevedge : left_equal (build_vec prev p1) (build_vec prev q)).
        {
          apply (IH x prev p1 (p2 :: post) q);
            try exact Hrev; try exact Hconsec_tail.
          simpl.
          tauto.
        }
        eapply edge_side_backward_weak; eauto.
        -- apply Hbetween; try exact HIn.
           simpl.
           tauto.
        -- apply Hbetween; try exact HIn.
           simpl.
           tauto.
        -- apply Hbetween; try exact HIn.
           simpl.
           tauto.
        -- apply Hprev.
           simpl.
           tauto.
        -- apply Hprev.
           simpl.
           tauto.
        -- apply Hp1.
           simpl.
           tauto.
        -- apply (rev_consec_ccw_edge_at_tail (l ++ [x]) prev p1 p2 post).
           exact Hconsec'.
      * simpl in HIn.
        destruct HIn as [Hqx | []].
        subst q.
        eapply edge_side_backward_weak; eauto.
        -- apply Hx.
           simpl.
           tauto.
        -- apply Hx.
           simpl.
           tauto.
        -- apply Hx.
           simpl.
           tauto.
        -- apply Hprev.
           simpl.
           tauto.
        -- apply Hprev.
           simpl.
           tauto.
        -- apply Hp1.
           simpl.
           tauto.
        -- apply (rev_consec_ccw_edge_at_tail (l ++ [x]) prev p1 p2 post).
           exact Hconsec'.
        -- apply edge_prev_endpoint_left.
           apply (rev_consec_ccw_edge_at_tail l x prev p1 (p2 :: post)).
           exact Hconsec_tail.
Qed.

Lemma final_edge_vertices_halfplane_weak : forall p0 pre plast q,
  weak_rev_ccw_list p0 (pre ++ plast :: nil) ->
  In q (p0 :: pre ++ plast :: nil) ->
  left_equal (build_vec plast p0) (build_vec plast q).
Proof.
  intros p0 pre plast q Hrev HIn.
  simpl in HIn.
  destruct HIn as [Hq | HIn].
  - subst q.
    unfold left_equal, cross_prod, build_vec.
    simpl.
    nia.
  - rewrite in_app_iff in HIn.
    simpl in HIn.
    destruct HIn as [HIn | [Hq | []]].
    + rewrite (weak_rev_ccw_list_app_iff p0 pre (plast :: nil)) in Hrev.
      destruct Hrev as [_ [_ Hbetween]].
      apply weak_rev_ccw_final_edge_halfplane.
      apply Hbetween; try exact HIn.
      simpl.
      tauto.
    + subst q.
      unfold left_equal, cross_prod, build_vec.
      simpl.
      nia.
Qed.

Lemma edge_all_vertices_halfplane_weak : forall p0 pre p1 p2 post q,
  weak_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  In q (p0 :: pre ++ p1 :: p2 :: post) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 pre p1 p2 post q Hrev Hconsec HIn.
  simpl in HIn.
  destruct HIn as [Hq | HIn].
  - subst q.
    assert (Htail : weak_rev_ccw_list p0 (p1 :: p2 :: post)).
    {
      apply (weak_rev_ccw_list_ind' p0 pre (p1 :: p2 :: post) Hrev).
    }
    simpl in Htail.
    destruct Htail as [Hfor _].
    rewrite Forall_weak_rev_ccw_forall in Hfor.
    apply weak_rev_ccw_edge_to_pivot_halfplane.
    apply Hfor.
    simpl.
    tauto.
  - rewrite in_app_iff in HIn.
    simpl in HIn.
    destruct HIn as [Hpre | [Hq1 | [Hq2 | Hpost]]].
    + destruct (destruct_tail pre) as [Hpre_nil | [prev [pre' Hpre_eq]]].
      * rewrite Hpre_nil in Hpre.
        contradiction.
      * subst pre.
        rewrite in_app_iff in Hpre.
        simpl in Hpre.
        destruct Hpre as [Hpre | [Hqprev | []]].
        -- assert (Hrev' : weak_rev_ccw_list p0
             (pre' ++ prev :: p1 :: p2 :: post)).
           { replace (pre' ++ prev :: p1 :: p2 :: post)
               with ((pre' ++ [prev]) ++ p1 :: p2 :: post)
               by (rewrite <- app_assoc; reflexivity).
             exact Hrev. }
           assert (Hconsec' : rev_consec_ccw
             (pre' ++ prev :: p1 :: p2 :: post)).
           { replace (pre' ++ prev :: p1 :: p2 :: post)
               with ((pre' ++ [prev]) ++ p1 :: p2 :: post)
               by (rewrite <- app_assoc; reflexivity).
             exact Hconsec. }
           eapply hull_edge_previous_halfplane_weak.
           ++ exact Hrev'.
           ++ exact Hconsec'.
           ++ exact (or_intror Hpre).
        -- subst q.
           assert (Hconsec' : rev_consec_ccw
             (pre' ++ prev :: p1 :: p2 :: post)).
           { replace (pre' ++ prev :: p1 :: p2 :: post)
               with ((pre' ++ [prev]) ++ p1 :: p2 :: post)
               by (rewrite <- app_assoc; reflexivity).
             exact Hconsec. }
           apply edge_prev_endpoint_left.
           apply (rev_consec_ccw_edge_at_tail pre' prev p1 p2 post).
           exact Hconsec'.
    + subst q.
      unfold left_equal, cross_prod, build_vec.
      simpl.
      nia.
    + subst q.
      unfold left_equal, cross_prod, build_vec.
      simpl.
      nia.
    + assert (Htail : weak_rev_ccw_list p0 (p1 :: p2 :: post)).
      {
        apply (weak_rev_ccw_list_ind' p0 pre (p1 :: p2 :: post) Hrev).
      }
      assert (Hconsec_tail : rev_consec_ccw (p1 :: p2 :: post)).
      {
        apply (rev_consec_ccw_app_inv2 pre).
        exact Hconsec.
      }
      eapply hull_edge_later_halfplane_weak; eauto.
Qed.
Lemma point_in_hull_edges_aux_from_hull_weak : forall p p0 pre p1 p2 post,
  weak_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  point_in_hull p (p0 :: pre ++ p1 :: p2 :: post) ->
  point_in_hull_edges_aux_ p p0 p1 (p2 :: post).
Proof.
  intros p p0 pre p1 p2 post Hrev Hconsec Hhull.
  revert pre p1 p2 Hrev Hconsec Hhull.
  induction post as [| p3 post IH]; intros pre p1 p2 Hrev Hconsec Hhull.
  - simpl.
    assert (Hconsec_tail : rev_consec_ccw (pre ++ p1 :: p2 :: nil)).
    {
      exact Hconsec.
    }
    assert (Hrev_final : weak_rev_ccw_list p0 ((pre ++ [p1]) ++ p2 :: nil)).
    {
      replace ((pre ++ [p1]) ++ p2 :: nil) with (pre ++ p1 :: p2 :: nil)
        by (rewrite <- app_assoc; reflexivity).
      exact Hrev.
    }
    split.
    + eapply (point_in_hull_halfplane_general_weak p p2 p0 p0 pre p1 p2 nil).
      * exact Hrev.
      * exact Hconsec_tail.
      * intros q HIn.
        eapply final_edge_vertices_halfplane_weak.
        -- exact Hrev_final.
        -- replace (p0 :: (pre ++ [p1]) ++ p2 :: nil)
             with (p0 :: pre ++ p1 :: p2 :: nil)
             by (simpl; rewrite <- app_assoc; reflexivity).
           exact HIn.
      * exact Hhull.
    + eapply (point_in_hull_halfplane_general_weak p p1 p2 p0 pre p1 p2 nil).
      * exact Hrev.
      * exact Hconsec_tail.
      * intros q HIn.
        eapply (edge_all_vertices_halfplane_weak p0 pre p1 p2 nil q).
        -- exact Hrev.
        -- exact Hconsec.
        -- exact HIn.
      * exact Hhull.
  - simpl.
    assert (Hconsec_tail : rev_consec_ccw (pre ++ p1 :: p2 :: p3 :: post)).
    {
      exact Hconsec.
    }
    assert (Hrev' : weak_rev_ccw_list p0 ((pre ++ [p1]) ++ p2 :: p3 :: post)).
    {
      replace ((pre ++ [p1]) ++ p2 :: p3 :: post)
        with (pre ++ p1 :: p2 :: p3 :: post)
        by (rewrite <- app_assoc; reflexivity).
      exact Hrev.
    }
    assert (Hconsec' : rev_consec_ccw
      ((pre ++ [p1]) ++ p2 :: p3 :: post)).
    {
      replace ((pre ++ [p1]) ++ p2 :: p3 :: post)
        with (pre ++ p1 :: p2 :: p3 :: post)
        by (rewrite <- app_assoc; reflexivity).
      exact Hconsec.
    }
    assert (Hhull' : point_in_hull p
      (p0 :: (pre ++ [p1]) ++ p2 :: p3 :: post)).
    {
      replace (p0 :: (pre ++ [p1]) ++ p2 :: p3 :: post)
        with (p0 :: pre ++ p1 :: p2 :: p3 :: post)
        by (simpl; rewrite <- app_assoc; reflexivity).
      exact Hhull.
    }
    split.
    + eapply (IH (pre ++ [p1]) p2 p3 Hrev' Hconsec' Hhull').
    + eapply (point_in_hull_halfplane_general_weak p p1 p2 p0 pre p1 p2
        (p3 :: post)).
      * exact Hrev.
      * exact Hconsec_tail.
      * intros q HIn.
        eapply (edge_all_vertices_halfplane_weak p0 pre p1 p2 (p3 :: post) q).
        -- exact Hrev.
        -- exact Hconsec.
        -- exact HIn.
	      * exact Hhull.
Qed.

Lemma point_in_hull_halfplane_general_g : forall p u v p0 pre p1 p2 post,
  g_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  (forall q, In q (p0 :: pre ++ p1 :: p2 :: post) ->
    left_equal (build_vec u v) (build_vec u q)) ->
  point_in_hull p (p0 :: pre ++ p1 :: p2 :: post) ->
  left_equal (build_vec u v) (build_vec u p).
Proof.
  intros.
  eapply point_in_hull_halfplane_general_weak; eauto.
Qed.

Lemma first_edge_vertices_halfplane_g : forall p0 p1 CH q,
  g_rev_ccw_list p0 (p1 :: CH) ->
  In q (p0 :: p1 :: CH) ->
  left_equal (build_vec p0 p1) (build_vec p0 q).
Proof.
  intros.
  eapply first_edge_vertices_halfplane_weak; eauto.
Qed.

Lemma point_in_hull_edges_aux_from_hull_g : forall p p0 pre p1 p2 post,
  g_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  point_in_hull p (p0 :: pre ++ p1 :: p2 :: post) ->
  point_in_hull_edges_aux_ p p0 p1 (p2 :: post).
Proof.
  intros.
  eapply point_in_hull_edges_aux_from_hull_weak; eauto.
Qed.

Theorem point_in_hull_equiv : forall p p0 CH,
  sort p0 CH ->
  rev_consec_ccw CH ->
  point_in_hull p (p0 :: CH) ->
  point_in_hull_edges p (p0 :: CH).
Proof.
  intros p p0 CH Hsort Hconsec Hhull.
  destruct Hsort as [_ Hrev].
  destruct CH as [| p1 CH'].
  - simpl in Hhull.
    contradiction.
  - destruct CH' as [| p2 post].
    + apply point_in_hull_equiv_two_points.
      exact Hhull.
    + simpl.
      split.
      * assert (Hconsec_tail : rev_consec_ccw (p1 :: p2 :: post)).
        {
          exact Hconsec.
        }
        eapply (point_in_hull_halfplane_general_g p p0 p1 p0 nil p1 p2 post).
        -- exact Hrev.
        -- exact Hconsec_tail.
        -- intros q HIn.
           eapply (first_edge_vertices_halfplane_g p0 p1 (p2 :: post) q).
           ++ exact Hrev.
           ++ exact HIn.
        -- exact Hhull.
      * eapply (point_in_hull_edges_aux_from_hull_g p p0 nil p1 p2 post); eauto.
Qed.

Theorem is_max_hull'_edges_of_max_hull : forall p CH l,
  sort p CH ->
  rev_consec_ccw CH ->
  is_max_hull' p CH l ->
  is_max_hull'_edges (p :: CH) l.
Proof.
  intros p CH l Hsort Hcon Hmax.
  destruct Hsort as [Hleft Hrev].
  unfold is_max_hull'_edges, is_max_hull' in *.
  rewrite !Forall_forall in *.
  intros q HIn.
  eapply point_in_hull_equiv.
  - split; [exact Hleft | exact Hrev].
  - exact Hcon.
  - apply Hmax.
    exact HIn.
Qed.

(* ===== Moved general lemmas: from Graham_Scan_M.v ===== *)

Definition rev_ccw_convex (T : list point) : Prop :=
  forall l1 q l2 r l3 s l4,
    T = l1 ++ q :: l2 ++ r :: l3 ++ s :: l4 ->
    ccw s r q.

Definition is_convex_hull (base T : list point) : Prop :=
  rev_ccw_convex T /\
  is_max_hull'_edges T base.
Lemma gs_ccw_convex_rev_to_rev_ccw_convex : forall T,
  ccw_convex (rev T) ->
  rev_ccw_convex T.
Proof.
  intros T Hconv.
  unfold rev_ccw_convex.
  intros l1 q l2 r l3 s l4 Heq.
  assert (HeqT : rev T = rev (l1 ++ q :: l2 ++ r :: l3 ++ s :: l4)).
  { rewrite Heq. reflexivity. }
  eapply (gs_ccw_convex_forall3_inv (rev T) Hconv
            (rev l4) s (rev l3) r (rev l2) q (rev l1)).
  rewrite HeqT.
  change (l1 ++ q :: l2 ++ r :: l3 ++ s :: l4)
    with (l1 ++ [q] ++ l2 ++ [r] ++ l3 ++ [s] ++ l4).
  repeat rewrite rev_app_distr.
  simpl.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.
Lemma gs_rev_ccw_convex_anchor : forall p CH,
  sort p CH ->
  rev_consec_ccw CH ->
  first_anchor_strict p (rev CH) ->
  rev_ccw_convex (p :: CH).
Proof.
  intros p CH Hsort Hconsec Hanchor.
  destruct Hsort as [_ Hrev].
  apply gs_ccw_convex_rev_to_rev_ccw_convex.
  simpl.
  apply (ccw_convex_app_comm [p] (rev CH)).
  simpl.
  apply ccw_convex_spec.
  - apply g_rev_ccw_list_to_g_ccw_list_rev.
    exact Hrev.
  - apply gs_rev_consec_ccw_anchor_consec; assumption.
Qed.
Lemma gs_rev_ccw_convex_to_ccw_convex_rev : forall T,
  rev_ccw_convex T ->
  ccw_convex (rev T).
Proof.
  intros T Hrev.
  unfold rev_ccw_convex in Hrev.
  apply ccw_convex_forall3.
  intros l1 p l2 q l3 r l4 Heq.
  assert (HeqT : T = rev (l1 ++ p :: l2 ++ q :: l3 ++ r :: l4)).
  { apply rev_inj. rewrite <- Heq. rewrite rev_involutive. reflexivity. }
  eapply Hrev.
  rewrite HeqT.
  change (l1 ++ p :: l2 ++ q :: l3 ++ r :: l4)
    with (l1 ++ [p] ++ l2 ++ [q] ++ l3 ++ [r] ++ l4).
  repeat rewrite rev_app_distr.
  simpl.
  do 5 rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.
Lemma gs_rev_ccw_convex_rotate1 : forall p CH,
  rev_ccw_convex (p :: CH) ->
  rev_ccw_convex (CH ++ [p]).
Proof.
  intros p CH Hconv.
  apply gs_ccw_convex_rev_to_rev_ccw_convex.
  rewrite rev_app_distr.
  change (rev [p]) with [p].
  change ([p] ++ rev CH) with ([p] ++ rev CH).
  apply ccw_convex_app_comm.
  change (rev CH ++ [p]) with (rev (p :: CH)).
  apply gs_rev_ccw_convex_to_ccw_convex_rev.
  exact Hconv.
Qed.
Lemma gs_point_in_hull_anchor : forall p CH,
  CH <> [] ->
  g_rev_ccw_list p CH ->
  point_in_hull p (p :: CH).
Proof.
  intros p CH Hne Hrev.
  destruct CH as [| q CH].
  - contradiction.
  - destruct CH as [| r CH'].
    + simpl.
      split.
      * unfold colinear, parallel, cross_prod, build_vec.
        simpl.
        nia.
      * unfold at_mid, backward_or_perp, dot_prod, build_vec.
        simpl.
        nia.
    + simpl.
      left.
      simpl in Hrev.
      destruct Hrev as [Hfor _].
      rewrite Forall_g_rev_ccw_forall in Hfor.
      apply (point_in_tri_weak_edge p p q r).
      * apply g_rev_ccw_iff_weak_rev_ccw.
        apply Hfor.
        simpl.
        tauto.
      * unfold colinear, parallel, cross_prod, build_vec.
        simpl.
        nia.
      * unfold at_mid, backward_or_perp, dot_prod, build_vec.
        simpl.
        nia.
Qed.
Lemma gs_point_in_hull_edges_anchor : forall p CH,
  sort p CH ->
  rev_consec_ccw CH ->
  CH <> [] ->
  point_in_hull_edges p (p :: CH).
Proof.
  intros p CH Hsort Hconsec Hne.
  destruct Hsort as [Hleft Hrev].
  eapply point_in_hull_equiv.
  - split; [exact Hleft | exact Hrev].
  - exact Hconsec.
  - apply gs_point_in_hull_anchor; assumption.
Qed.
Lemma gs_is_max_hull'_edges_with_anchor : forall p CH l,
  sort p CH ->
  rev_consec_ccw CH ->
  CH <> [] ->
  is_max_hull' p CH l ->
  is_max_hull'_edges (p :: CH) (p :: l).
Proof.
  intros p CH l Hsort Hconsec Hne Hmax.
  unfold is_max_hull'_edges.
  rewrite Forall_cons_iff.
  split.
  - apply gs_point_in_hull_edges_anchor; assumption.
  - eapply is_max_hull'_edges_of_max_hull; eauto.
Qed.
Lemma gs_point_in_hull_edges_aux_snoc_final : forall q p0 p1 l p2,
  point_in_hull_edges_aux_ q p0 p1 l ->
  left_equal (build_vec p0 p2) (build_vec p0 q) ->
  point_in_hull_edges_aux_ q p2 p1 (l ++ [p0]).
Proof.
  intros q p0 p1 l.
  revert p0 p1.
  induction l as [| x l IH]; intros p0 p1 p2 Haux Hlast; simpl in *.
  - split; assumption.
  - destruct Haux as [Haux Hedge].
    split.
    + apply IH; assumption.
    + exact Hedge.
Qed.
Lemma gs_point_in_hull_edges_rotate1 : forall q p0 CH,
  point_in_hull_edges q (p0 :: CH) ->
  point_in_hull_edges q (CH ++ [p0]).
Proof.
  intros q p0 CH Hedges.
  destruct CH as [| p1 CH].
  - simpl in Hedges.
    contradiction.
  - destruct CH as [| p2 post].
    + simpl in *.
      destruct Hedges as [Hcol Hmid].
      split.
      * rewrite colinear_comm.
        exact Hcol.
      * rewrite at_mid_comm.
        exact Hmid.
    + simpl in Hedges.
      destruct Hedges as [Hfirst Haux].
      destruct post as [| p3 post].
      * simpl in *.
        destruct Haux as [Haux Hnext].
        split.
        -- exact Hnext.
        -- split; assumption.
      * simpl in *.
        destruct Haux as [Haux Hnext].
        split.
        -- exact Hnext.
        -- destruct Haux as [Haux Hnext'].
           split.
           ++ apply gs_point_in_hull_edges_aux_snoc_final; assumption.
           ++ exact Hnext'.
Qed.
Lemma gs_is_max_hull'_edges_rotate1 : forall p CH l,
  is_max_hull'_edges (p :: CH) l ->
  is_max_hull'_edges (CH ++ [p]) l.
Proof.
  intros p CH l Hmax.
  unfold is_max_hull'_edges in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply gs_point_in_hull_edges_rotate1.
  apply Hmax.
  exact Hq.
Qed.
Lemma gs_is_max_hull'_edges_cons_rev_tail : forall T p l,
  is_max_hull'_edges T (p :: rev l) ->
  is_max_hull'_edges T (p :: l).
Proof.
  intros T p l Hedges.
  unfold is_max_hull'_edges in *.
  rewrite Forall_cons_iff in *.
  destruct Hedges as [Hp Htail].
  split; [exact Hp |].
  rewrite <- (rev_involutive l).
  apply Forall_rev.
  exact Htail.
Qed.
Lemma gs_point_in_hull_self_edge : forall p a,
  point_in_hull a (p :: a :: nil).
Proof.
  intros p a.
  simpl.
  split.
  - unfold colinear, parallel, cross_prod, build_vec.
    simpl.
    nia.
  - unfold at_mid, backward_or_perp, dot_prod, build_vec.
    simpl.
    nia.
Qed.
Lemma gs_point_in_hull_new_head : forall p a C,
  g_rev_ccw_list p (a :: C) ->
  point_in_hull a (p :: a :: C).
Proof.
  intros p a C Hweak.
  destruct C as [| b C].
  - apply gs_point_in_hull_self_edge.
  - simpl.
    left.
    apply point_in_tri_1.
    simpl in Hweak.
    destruct Hweak as [Ha _].
    rewrite Forall_g_rev_ccw_cons_iff in Ha.
    destruct Ha as [Hab _].
    apply gs_g_rev_ccw_not_ccw_tail.
    exact Hab.
Qed.
Lemma gs_is_max_hull'_push : forall p a C L,
  g_rev_ccw_list p (a :: C) ->
  (C = [] -> L = []) ->
  is_max_hull' p C L ->
  is_max_hull' p (a :: C) (a :: L).
Proof.
  intros p a C L Hweak Hempty Hmax.
  unfold is_max_hull' in *.
  rewrite Forall_cons_iff.
  split.
  - apply gs_point_in_hull_new_head.
    exact Hweak.
  - destruct C as [| b C].
    + specialize (Hempty eq_refl).
      subst L.
      apply Forall_nil.
    + rewrite Forall_forall in *.
      intros q Hq.
      pose proof (Hmax q Hq) as Hq_old.
      pose proof (proj2 (point_in_hull_cons_iff_weak q p b a C Hweak)) as Hlift.
      apply Hlift.
      left.
      exact Hq_old.
Qed.
Lemma gs_point_in_hull_pop_single : forall p a b q,
  g_rev_ccw p a b ->
  ~ ccw p b a ->
  point_in_hull q (p :: a :: b :: nil) ->
  point_in_hull q (p :: a :: nil).
Proof.
  intros p a b q Hweak Hnccw Hhull.
  destruct Hweak as [Hstrict | [Hcol Hmid]].
  - exfalso.
    apply Hnccw.
    apply ccw_cyclicity.
    exact Hstrict.
  - simpl in Hhull |- *.
    destruct Hhull as [Hhull | []].
    unfold point_in_triangle in Hhull.
    destruct Hhull as [Htri | [Htri_col Hseg]].
    + destruct Htri as [Hccw [He1 [He2 He3]]].
      unfold ccw, colinear, at_mid, left_equal, left_than, parallel,
             backward_or_perp, build_vec, cross_prod, dot_prod in *.
      simpl in *.
      nia.
    + destruct Hseg as [[Hqcol Hqmid] |
                        [[Hqcol Hqmid] |
                         [Hqcol Hqmid]]].
      * pose proof (segment_mid_trans_left q b a p
          (colinear_perm321 _ _ _ Hcol) Hmid Hqcol Hqmid)
          as [Hqap_col Hqap_mid].
        split.
        -- apply colinear_perm132.
           exact Hqap_col.
        -- apply at_mid_comm.
           exact Hqap_mid.
      * pose proof (segment_mid_trans_right q b a p
          (colinear_perm321 _ _ _ Hcol) Hmid Hqcol Hqmid)
          as [Hqap_col Hqap_mid].
        split.
        -- apply colinear_perm132.
           exact Hqap_col.
        -- apply at_mid_comm.
           exact Hqap_mid.
      * split; assumption.
Qed.
