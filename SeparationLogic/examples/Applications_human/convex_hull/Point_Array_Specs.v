Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
From ListLib.Base Require Import Positional.
From SimpleC.EE.Applications_human.convex_hull Require Import Geo_Point_Primitives Point_Order.

Local Open Scope Z_scope.
Import ListNotations.

Definition points_in_bound (l : list point) : Prop :=
  Forall (fun p => point_in_bound p) l.

Definition point_swap (l : list point) (i j : Z) : list point :=
  replace_Znth j (Znth i l default_point)
    (replace_Znth i (Znth j l default_point) l).

Definition point_mk (x y : Z) : point :=
  {| point_x := x; point_y := y |}.

Definition point_permutation : list point -> list point -> Prop :=
  @Permutation point.

Definition point_same_outside_range (l l1 : list point) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 default_point = Znth k l default_point.

Definition point_sorted_range
    (gp : point) (l : list point) (left right : Z) : Prop :=
  forall i j,
    left <= i -> i <= j -> j <= right ->
    point_cmp_polar gp (Znth i l default_point) (Znth j l default_point) <= 0.

Definition point_polar_partitioned_at
    (gp : point) (l : list point) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => point_cmp_polar gp x (Znth p l default_point) <= 0)
         (sublist low p l) /\
  Forall (fun x => point_cmp_polar gp (Znth p l default_point) x < 0)
         (sublist (p + 1) (high + 1) l).

Definition point_polar_partition_scan_inv
    (gp : point) (before cur : list point)
    (low high : Z) (pivot : point) (i j : Z) : Prop :=
  point_permutation before cur /\
  point_same_outside_range before cur low high /\
  Znth high cur default_point = pivot /\
  (forall k, low <= k <= i ->
     point_cmp_polar gp (Znth k cur default_point) pivot <= 0) /\
  (forall k, i < k < j ->
     point_cmp_polar gp pivot (Znth k cur default_point) < 0).
