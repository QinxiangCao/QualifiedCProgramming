Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
From SimpleC.EE.Applications_human.convex_hull Require Import Geo_Point_Primitives.

Local Open Scope Z_scope.

(** Compatibility layer for point-level geometric predicates.

    [Geo_Point] is the canonical home for these predicates. This file
    keeps the earlier [ConvexHull.Geo_Predicates.*] names without maintaining
    duplicate definitions. *)

Definition colinear : point -> point -> point -> Prop :=
  Geo_Point_Primitives.colinear.

Definition at_mid : point -> point -> point -> Prop :=
  Geo_Point_Primitives.at_mid.

Lemma colinear_comm : forall p q r,
  colinear p q r <-> colinear p r q.
Proof.
  apply Geo_Point_Primitives.colinear_comm.
Qed.

Lemma at_mid_comm : forall p q r,
  at_mid p q r <-> at_mid p r q.
Proof.
  apply Geo_Point_Primitives.at_mid_comm.
Qed.

Definition left_than (u v : vec) : Prop :=
  cross_prod u v > 0.

Definition ccw : point -> point -> point -> Prop :=
  Geo_Point_Primitives.ccw.

Lemma ccw_iff_cross_pos : forall a b c,
  ccw a b c <-> cross_prod (build_vec a b) (build_vec a c) > 0.
Proof.
  intros a b c.
  unfold ccw, Geo_Point_Primitives.ccw, Geo_Vec.left_than.
  rewrite cross_prod_comm.
  split; lia.
Qed.

Definition ccw_dec (a b c : point) : {ccw a b c} + {~ ccw a b c} :=
  Geo_Point_Primitives.ccw_dec a b c.
