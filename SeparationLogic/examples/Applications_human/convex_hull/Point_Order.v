Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
From SimpleC.EE.Applications_human.convex_hull Require Import Geo_Point_Primitives.

Local Open Scope Z_scope.

Definition x : point -> Z := point_x.
Definition y : point -> Z := point_y.

Definition default_point : point := {| point_x := 0; point_y := 0 |}.

Definition point_cmp_xy (a b : point) : Z :=
  if Z_lt_dec (x a) (x b) then -1 else
  if Z_gt_dec (x a) (x b) then 1 else
  if Z_lt_dec (y a) (y b) then -1 else
  if Z_gt_dec (y a) (y b) then 1 else
  0.

Definition point_cross (a b c : point) : Z :=
  cross_prod (build_vec a b) (build_vec a c).

Definition point_dot (a b c : point) : Z :=
  dot_prod (build_vec a b) (build_vec a c).

Definition point_at_mid (pivot a b : point) : Z :=
  point_dot a b pivot.

Definition point_cmp_polar (pivot a b : point) : Z :=
  let cr := point_cross pivot a b in
  if Z_gt_dec cr 0 then -1 else
  if Z_lt_dec cr 0 then 1 else
  let mid := point_at_mid pivot a b in
  if Z_gt_dec mid 0 then 1 else
  if Z_lt_dec mid 0 then -1 else
  point_cmp_xy a b.

Lemma point_cross_gt_0_ccw : forall a b c,
  point_cross a b c > 0 <-> ccw a b c.
Proof.
  intros a b c.
  unfold point_cross, ccw, left_than.
  rewrite cross_prod_comm.
  split; lia.
Qed.

Lemma point_cross_le_0_not_ccw : forall a b c,
  point_cross a b c <= 0 <-> ~ ccw a b c.
Proof.
  intros a b c.
  unfold point_cross, ccw, left_than.
  rewrite cross_prod_comm.
  split; lia.
Qed.

Definition point_bound : Z := 10000.

Definition point_in_bound (p : point) : Prop :=
  -point_bound <= x p <= point_bound /\ -point_bound <= y p <= point_bound.

Lemma point_bound_sub : forall a b,
  point_in_bound a -> point_in_bound b ->
  -20000 <= x a - x b <= 20000 /\ -20000 <= y a - y b <= 20000.
Proof.
  intros a b Ha Hb.
  unfold point_in_bound, point_bound in *.
  destruct Ha as [[Haxl Haxr] [Hayl Hayr]].
  destruct Hb as [[Hbxl Hbxr] [Hbyl Hbyr]].
  split; split; nia.
Qed.
