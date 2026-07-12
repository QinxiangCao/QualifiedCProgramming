Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
From compcert.lib Require Import Integers.
From AUXLib Require Import int_auto Feq Idents ListLib VMap relations Axioms.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
From SimpleC.EE.Applications_human.convex_hull Require Export Geo_Point.
From SimpleC.EE.Applications_human.convex_hull Require Import Geo_Vec Point_Order Graham_Scan Maximality Graham_Scan_M Reversal.
From SimpleC.EE.Applications_human.convex_hull Require Andrew_Monotone_Chain.
From SimpleC.EE.Applications_human.convex_hull Require Andrew_Monotone_Chain_M.
From FP Require Import PartialOrder_Setoid.
Require Import MonadLib.Monad.
From MonadLib.StateRelMonad Require StateRelBasic StateRelMonad.
From MonadLib.StateRelMonad Require Import StateRelHoare safeexec_lib FixpointLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Import Monad MonadNotation.
Import StateRelBasic StateRelMonad.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope monad_scope.

Notation Point := point.

Notation "p '.(x)'" := (point_x p) (at level 1).
Notation "p '.(y)'" := (point_y p) (at level 1).

Axiom sizeof_point : sizeof_front_end_type (FET_alias "Point") = 8.

Definition sizeof_Point : Z := sizeof_front_end_type (FET_alias "Point").

Notation "'sizeof' ( ""Point"" )" := (sizeof_Point) (at level 1).

Lemma sizeof_Point_eq : sizeof_Point = 8.
Proof.
  unfold sizeof_Point.
  apply sizeof_point.
Qed.

Lemma sizeof_front_end_type_Point :
  sizeof_front_end_type (FET_alias "Point") = sizeof_Point.
Proof.
  reflexivity.
Qed.

Definition store_point (p : addr) (pt : Point) : Assertion :=
  (&((p) # "Point" ->ₛ "x") # Int |-> pt.(x)) **
  (&((p) # "Point" ->ₛ "y") # Int |-> pt.(y)).

Definition undef_point (p : addr) : Assertion :=
  (&((p) # "Point" ->ₛ "x") # Int |->_) **
  (&((p) # "Point" ->ₛ "y") # Int |->_).
  


Definition point_cmp_xy (a b : Point) : Z :=
  if Z_lt_dec (x a) (x b) then -1 else
  if Z_gt_dec (x a) (x b) then 1 else
  if Z_lt_dec (y a) (y b) then -1 else
  if Z_gt_dec (y a) (y b) then 1 else
  0.

Definition point_leftdown (a b : Point) : Prop :=
  x a < x b \/ (x a = x b /\ y a <= y b).

Definition point_cmp_leftdown (a b : Point) : Z :=
  if Z_lt_dec (x a) (x b) then -1 else
  if Z_gt_dec (x a) (x b) then 1 else
  if Z_lt_dec (y a) (y b) then -1 else
  if Z_gt_dec (y a) (y b) then 1 else
  0.

Definition default_point : Point := {| point_x := 0; point_y := 0 |}.

Definition point_leftmost_prefix (l : list Point) (pivot_idx i : Z) : Prop :=
  0 <= pivot_idx < i /\
  i <= Zlength l /\
  forall k,
    0 <= k < i ->
    point_leftdown (Znth pivot_idx l default_point)
                   (Znth k l default_point).

Definition empty_point_stack : list Point := nil.

Definition andrew_monotone_chain_m
  : list Point -> program (list Point) unit :=
  Andrew_Monotone_Chain_M.andrew_monotone_chain.

Definition build_chain
  : list Point -> program (list Point) unit :=
  Andrew_Monotone_Chain_M.build_chain.

Definition build_upper_chain_cont
    (sorted lower : list Point) : program (list Point) unit :=
  upper <- Andrew_Monotone_Chain_M.build_upper_chain sorted ;;
  update' (fun _ => Andrew_Monotone_Chain.andrew_merge sorted lower upper).

#[export] Instance point_list_equiv : Equiv (list Point) := eq.

#[export] Instance point_list_equiv_equivalence :
  Equivalence (@equiv (list Point) point_list_equiv).
Proof.
  constructor; congruence.
Qed.

Definition point_mk (x y : Z) : Point :=
  {| point_x := x; point_y := y |}.

Lemma point_mk_eta : forall p,
  point_mk (point_x p) (point_y p) = p.
Proof.
  intros [px py].
  reflexivity.
Qed.

Definition point_bound : Z := Point_Order.point_bound.

Definition point_in_bound : Point -> Prop := Point_Order.point_in_bound.

Lemma point_cmp_leftdown_eq_cmp_xy : forall a b,
  point_cmp_leftdown a b = point_cmp_xy a b.
Proof.
  intros a b.
  unfold point_cmp_leftdown, point_cmp_xy.
  reflexivity.
Qed.

Lemma point_leftdown_refl : forall a,
  point_leftdown a a.
Proof.
  intros a.
  unfold point_leftdown.
  right; nia.
Qed.

Lemma point_leftdown_trans : forall a b c,
  point_leftdown a b ->
  point_leftdown b c ->
  point_leftdown a c.
Proof.
  intros a b c H1 H2.
  unfold point_leftdown in *.
  destruct H1 as [H1|[H1x H1y]].
  - destruct H2 as [H2|[H2x H2y]]; nia.
  - destruct H2 as [H2|[H2x H2y]].
    + left; nia.
    + right; subst; nia.
Qed.

Lemma point_leftdown_total : forall a b,
  point_leftdown a b \/ point_leftdown b a.
Proof.
  intros a b.
  unfold point_leftdown.
  destruct (Z_lt_dec (x a) (x b)).
  { left; left; nia. }
  destruct (Z_gt_dec (x a) (x b)).
  { right; left; nia. }
  destruct (Z_lt_dec (y a) (y b)).
  { left; right; nia. }
  destruct (Z_gt_dec (y a) (y b)).
  { right; right; nia. }
  left; right; nia.
Qed.

Lemma point_leftdown_antitrans : forall a b,
  point_leftdown a b /\ point_leftdown b a <-> x a = x b /\ y a = y b.
Proof.
  intros a b.
  unfold point_leftdown.
  split.
  - intros [[H1|[H1x H1y]] [H2|[H2x H2y]]]; nia.
  - intros [Hx Hy]; subst.
    split; right; nia.
Qed.

Lemma point_leftdown_lt_impl : forall a b,
  point_leftdown a b -> ~ point_leftdown b a ->
  x a < x b \/ (x a = x b /\ y a < y b).
Proof.
  intros a b H Hnot.
  unfold point_leftdown in *.
  destruct H as [H|[Hx Hy]].
  - left; nia.
  - destruct (Z_lt_dec (y a) (y b)).
    + right; nia.
    + assert (y a = y b) by nia.
      subst.
      exfalso. apply Hnot. right; nia.
Qed.

Lemma point_leftdown_gt_impl : forall a b,
  ~ point_leftdown a b -> point_leftdown b a ->
  x a > x b \/ (x a = x b /\ y a > y b).
Proof.
  intros a b Hnot H.
  unfold point_leftdown in *.
  destruct H as [H|[Hx Hy]].
  - left; nia.
  - destruct (Z_gt_dec (y a) (y b)).
    + right; nia.
    + assert (y a = y b) by nia.
      subst.
      exfalso. apply Hnot. right; nia.
Qed.

Lemma point_cmp_leftdown_lt_point_leftdown : forall a b,
  point_cmp_leftdown a b < 0 ->
  point_leftdown a b.
Proof.
  intros a b Hcmp.
  unfold point_cmp_leftdown, point_leftdown, x, y in *.
  destruct (Z_lt_dec (point_x a) (point_x b)) as [Hxlt | Hxnlt].
  - left; lia.
  - destruct (Z_gt_dec (point_x a) (point_x b)) as [Hxgt | Hxngt].
    + lia.
    + destruct (Z_lt_dec (point_y a) (point_y b)) as [Hylt | Hynlt].
      * right; split; lia.
      * destruct (Z_gt_dec (point_y a) (point_y b)); lia.
Qed.

Lemma point_cmp_leftdown_nonneg_point_leftdown_flip : forall a b,
  0 <= point_cmp_leftdown a b ->
  point_leftdown b a.
Proof.
  intros a b Hcmp.
  unfold point_cmp_leftdown, point_leftdown, x, y in *.
  destruct (Z_lt_dec (point_x a) (point_x b)) as [Hxlt | Hxnlt].
  - lia.
  - destruct (Z_gt_dec (point_x a) (point_x b)) as [Hxgt | Hxngt].
    + left; lia.
    + destruct (Z_lt_dec (point_y a) (point_y b)) as [Hylt | Hynlt].
      * lia.
      * destruct (Z_gt_dec (point_y a) (point_y b)) as [Hygt | Hyngt].
        -- right; split; lia.
        -- right; split; lia.
Qed.

Lemma point_leftmost_prefix_init : forall l,
  1 <= Zlength l ->
  point_leftmost_prefix l 0 1.
Proof.
  intros l Hlen.
  unfold point_leftmost_prefix.
  split; [lia |].
  split; [lia |].
  intros k Hk.
  replace k with 0 by lia.
  apply point_leftdown_refl.
Qed.

Lemma point_leftmost_prefix_step_keep : forall l pivot_idx i,
  point_leftmost_prefix l pivot_idx i ->
  i < Zlength l ->
  point_leftdown (Znth pivot_idx l default_point)
                 (Znth i l default_point) ->
  point_leftmost_prefix l pivot_idx (i + 1).
Proof.
  intros l pivot_idx i Hprefix Hlen Hcur.
  unfold point_leftmost_prefix in *.
  destruct Hprefix as [Hidx [Hi Hmin]].
  split; [lia |].
  split; [lia |].
  intros k Hk.
  destruct (Z.eq_dec k i) as [-> | Hneq].
  - exact Hcur.
  - apply Hmin.
    lia.
Qed.

Lemma point_leftmost_prefix_step_update : forall l pivot_idx i,
  point_leftmost_prefix l pivot_idx i ->
  i < Zlength l ->
  point_leftdown (Znth i l default_point)
                 (Znth pivot_idx l default_point) ->
  point_leftmost_prefix l i (i + 1).
Proof.
  intros l pivot_idx i Hprefix Hlen Hnew.
  unfold point_leftmost_prefix in *.
  destruct Hprefix as [Hidx [Hi Hmin]].
  split; [lia |].
  split; [lia |].
  intros k Hk.
  destruct (Z.eq_dec k i) as [-> | Hneq].
  - apply point_leftdown_refl.
  - eapply point_leftdown_trans.
    + exact Hnew.
    + apply Hmin.
      lia.
Qed.

Lemma leftmost_refl_single : forall p,
  leftmost p [p].
Proof.
  intros p.
  unfold leftmost.
  rewrite Forall_cons_iff.
  split.
  - unfold x, y.
    right; split; lia.
  - apply Forall_nil.
Qed.

Lemma point_leftdown_leftmost_cons : forall p q l,
  point_leftdown p q ->
  leftmost p l ->
  leftmost p (q :: l).
Proof.
  intros p q l Hpq Hleft.
  unfold leftmost in *.
  rewrite Forall_cons_iff.
  split.
  - unfold point_leftdown, x, y in Hpq.
    exact Hpq.
  - exact Hleft.
Qed.

Lemma leftmost_rev : forall p l,
  leftmost p l ->
  leftmost p (rev l).
Proof.
  intros p l Hleft.
  unfold leftmost in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hleft.
  rewrite in_rev.
  exact Hq.
Qed.

Lemma leftmost_permutation : forall p l1 l2,
  Permutation l1 l2 ->
  leftmost p l1 ->
  leftmost p l2.
Proof.
  intros p l1 l2 Hperm Hleft.
  unfold leftmost in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hleft.
  eapply Permutation_in.
  - symmetry.
    exact Hperm.
  - exact Hq.
Qed.

Lemma derivable1_orp_intros_left : forall (A B C S : Assertion),
  S |-- A -> S |-- A || B || C.
Proof.
  intros A B C S HSA.
  eapply derivable1_trans.
  { exact HSA. }
  eapply derivable1_trans.
  { apply (derivable1_orp_intros1 A B). }
  apply (derivable1_orp_intros1 (A || B) C).
Qed.

Lemma derivable1_orp_intros_mid : forall (A B C S : Assertion),
  S |-- B -> S |-- A || B || C.
Proof.
  intros A B C S HSB.
  pose proof (logic_equiv_orp_assoc A B C) as [Heq1 Heq2].
  eapply derivable1_trans.
  2: { apply Heq2. }
  eapply derivable1_trans.
  2: { apply (derivable1_orp_intros2 A (B || C)). }
  eapply derivable1_trans.
  2: { apply (derivable1_orp_intros1 B C). }
  exact HSB.
Qed.

Lemma derivable1_orp_intros_right : forall (A B C S : Assertion),
  S |-- C -> S |-- A || B || C.
Proof.
  intros A B C S HSC.
  eapply derivable1_trans.
  { exact HSC. }
  apply derivable1_orp_intros2.
Qed.

Lemma emp_derives_pure : forall (P : Prop), P -> emp |-- “ P ”.
Proof.
  intros P HP.
  apply (derivable1s_coq_prop_r P emp).
  exact HP.
Qed.

Lemma emp_derives_pure_or3 : forall (P Q R : Prop),
  (P \/ Q \/ R) -> emp |-- “ P ” || “ Q ” || “ R ”.
Proof.
  intros P Q R Hor.
  destruct Hor as [HP | [HQ | HR]].
  - apply emp_derives_pure in HP.
    transitivity (“ P ”).
    { exact HP. }
    transitivity (“ P ” || “ Q ”).
    { apply derivable1_orp_intros1. }
    apply derivable1_orp_intros1.
  - apply emp_derives_pure in HQ.
    transitivity (“ Q ”).
    { exact HQ. }
    transitivity (“ P ” || “ Q ”).
    { apply derivable1_orp_intros2. }
    apply derivable1_orp_intros1.
  - apply emp_derives_pure in HR.
    transitivity (“ R ”).
    { exact HR. }
    apply derivable1_orp_intros2.
Qed.

Lemma andp_derives_coq_prop_and : forall (P Q R : Prop),
  “ P /\ Q /\ R ” |-- “ P ” && “ Q ” && “ R ”.
Proof.
  intros P Q R.
  apply derivable1s_coq_prop_l.
  intros [HP [HQ HR]].
  pose proof (derivable1s_coq_prop_r P truep HP) as HP'.
  pose proof (derivable1s_coq_prop_r Q truep HQ) as HQ'.
  pose proof (derivable1s_coq_prop_r R truep HR) as HR'.
  assert (HPQ : derivable1 truep (“ P ” && “ Q ”)).
  { eapply derivable1s_truep_intros; eauto. }
  eapply derivable1s_truep_intros; eauto.
Qed.

Lemma derivable1_trans : forall x y z,
  derivable1 x y -> derivable1 y z -> derivable1 x z.
Proof.
  intros x y z H1 H2 m H.
  apply H2.
  apply H1.
  exact H.
Qed.

Lemma emp_derives_or3_and : forall (P1 Q1 R1 P2 Q2 R2 P3 Q3 R3 : Prop),
  ((P1 /\ Q1 /\ R1) \/ (P2 /\ Q2 /\ R2) \/ (P3 /\ Q3 /\ R3)) ->
  emp |-- (“ P1 ” && “ Q1 ” && “ R1 ”) ||
          (“ P2 ” && “ Q2 ” && “ R2 ”) ||
          (“ P3 ” && “ Q3 ” && “ R3 ”).
Proof.
  intros P1 Q1 R1 P2 Q2 R2 P3 Q3 R3 Hor.
  destruct Hor as [[HP1 [HQ1 HR1]] | [[HP2 [HQ2 HR2]] | [HP3 [HQ3 HR3]]]].
  - (* branch 1: A1 *)
    apply emp_derives_pure in HP1. apply emp_derives_pure in HQ1. apply emp_derives_pure in HR1.
    assert (Hgoal1 : emp |-- “ P1 ” && “ Q1 ” && “ R1 ”).
    { assert (HPQ : emp |-- “ P1 ” && “ Q1 ”).
      { eapply derivable1s_truep_intros; eauto. }
      eapply derivable1s_truep_intros; eauto. }
    eapply derivable1_trans.
    { exact Hgoal1. }
    eapply derivable1_trans.
    { apply derivable1_orp_intros1. }
    apply derivable1_orp_intros1.
  - (* branch 2: A2 *)
    apply emp_derives_pure in HP2. apply emp_derives_pure in HQ2. apply emp_derives_pure in HR2.
    assert (Hgoal2 : emp |-- “ P2 ” && “ Q2 ” && “ R2 ”).
    { assert (HPQ : emp |-- “ P2 ” && “ Q2 ”).
      { eapply derivable1s_truep_intros; eauto. }
      eapply derivable1s_truep_intros; eauto. }
    eapply derivable1_trans.
    { exact Hgoal2. }
    eapply derivable1_trans.
    { apply derivable1_orp_intros2. }
    apply derivable1_orp_intros1.
  - (* branch 3: A3 *)
    apply emp_derives_pure in HP3. apply emp_derives_pure in HQ3. apply emp_derives_pure in HR3.
    assert (Hgoal3 : emp |-- “ P3 ” && “ Q3 ” && “ R3 ”).
    { assert (HPQ : emp |-- “ P3 ” && “ Q3 ”).
      { eapply derivable1s_truep_intros; eauto. }
      eapply derivable1s_truep_intros; eauto. }
    eapply derivable1_trans.
    { exact Hgoal3. }
    apply derivable1_orp_intros2.
Qed.

Definition point_cross (a b c : Point) : Z :=
  cross_prod (build_vec a b) (build_vec a c).

Definition point_cross_by_value
    (a_x a_y b_x b_y c_x c_y : Z) : Z :=
  (b_x - a_x) * (c_y - a_y) - (b_y - a_y) * (c_x - a_x).

Definition point_dot_by_value
    (a_x a_y b_x b_y c_x c_y : Z) : Z :=
  (b_x - a_x) * (c_x - a_x) + (b_y - a_y) * (c_y - a_y).

Definition point_dot (a b c : Point) : Z :=
  dot_prod (build_vec a b) (build_vec a c).

Definition point_colinear (pivot a b : Point) : Prop :=
  point_cross pivot a b = 0.

Definition point_at_mid (pivot a b : Point) : Z :=
  point_dot a b pivot.

Definition point_cmp_polar (pivot a b : Point) : Z :=
  let cr := point_cross pivot a b in
  if Z_gt_dec cr 0 then -1 else
  if Z_lt_dec cr 0 then 1 else
  let mid := point_at_mid pivot a b in
  if Z_gt_dec mid 0 then  1 else
  if Z_lt_dec mid 0 then -1 else
  point_cmp_xy a b.

Definition point_same (a b : Point) : Prop :=
  x a = x b /\ y a = y b.

Definition point_no_dup_prefix (l : list Point) (n : Z) : Prop :=
  0 <= n <= Zlength l /\
  forall i j,
    0 <= i < j ->
    j < n ->
    ~ point_same (Znth i l default_point) (Znth j l default_point).

Definition point_prefix_has_same (l : list Point) (unique_n read : Z) : Prop :=
  0 <= unique_n <= Zlength l /\
  0 <= read < Zlength l /\
  exists j,
    0 <= j < unique_n /\
    point_same (Znth j l default_point) (Znth read l default_point).

Definition point_dedup_inner_scan_inv
    (l : list Point) (unique_n read scan duplicate : Z) : Prop :=
  (duplicate = 0 /\
   forall k,
     0 <= k < scan ->
     ~ point_same (Znth k l default_point) (Znth read l default_point)) \/
  (duplicate <> 0 /\
   point_prefix_has_same l unique_n read).

Definition point_prefix_represents_range
    (l : list Point) (unique_n lo hi : Z) : Prop :=
  0 <= unique_n <= lo /\
  lo <= hi <= Zlength l /\
  forall k,
    lo <= k < hi ->
    exists j,
      0 <= j < unique_n /\
      point_same (Znth j l default_point) (Znth k l default_point).

Definition point_unique_prefix_represents_all
    (l : list Point) (unique_n : Z) : Prop :=
  0 <= unique_n <= Zlength l /\
  forall k,
    0 <= k < Zlength l ->
    exists j,
      0 <= j < unique_n /\
      point_same (Znth j l default_point) (Znth k l default_point).

Definition point_dedup_scan_inv
    (before cur : list Point) (read unique_n pivot_idx : Z) : Prop :=
  Zlength before = Zlength cur /\
  0 <= unique_n <= read /\
  read <= Zlength cur /\
  @Permutation Point before cur /\
  point_no_dup_prefix cur unique_n /\
  point_prefix_represents_range cur unique_n unique_n read /\
  (unique_n = 0 \/ point_leftmost_prefix cur pivot_idx unique_n).

Definition point_dedup_result
    (before cur : list Point) (unique_n pivot_idx : Z) : Prop :=
  point_dedup_scan_inv before cur (Zlength cur) unique_n pivot_idx /\
  1 <= unique_n <= Zlength cur /\
  point_leftmost_prefix cur pivot_idx unique_n /\
  point_unique_prefix_represents_all cur unique_n.

Definition point_polar_cmp_safe_pair (gp a b : Point) : Prop :=
  point_colinear gp a b ->
  point_at_mid gp a b = 0 ->
  point_cmp_xy a b = 0.

Definition point_polar_cmp_safe_range
    (gp : Point) (l : list Point) (lo hi : Z) : Prop :=
  forall i j,
    lo <= i <= hi ->
    lo <= j <= hi ->
    point_polar_cmp_safe_pair gp
      (Znth i l default_point) (Znth j l default_point).

Definition point_polar_sorted (pivot : Point) (l : list Point) : Prop :=
  forall i j d,
    0 <= i < j ->
    j < Zlength l ->
    point_cmp_polar pivot (Znth i l d) (Znth j l d) <= 0.

Definition sort : Point -> list Point -> Prop := point_polar_sorted.

Definition point_weak_rev_ccw (pivot a b : Point) : Prop :=
  ccw a pivot b \/
  (point_colinear pivot a b /\ at_mid b a pivot).

Definition point_weak_polar_le (pivot a b : Point) : Prop :=
  point_weak_rev_ccw pivot b a.

Definition point_weak_polar_sorted (pivot : Point) (l : list Point) : Prop :=
  forall i j d,
    0 <= i < j ->
    j < Zlength l ->
    point_weak_polar_le pivot (Znth i l d) (Znth j l d).

Definition build_hull : Point -> list Point -> program (list Point) unit :=
  Graham_Scan_M.build_hull.

Definition is_convex_hull (base hull : list Point) : Prop :=
  Maximality.is_convex_hull base hull \/
  Maximality.is_convex_hull base (rev hull).

Definition point_dedup_hull_result (base hull : list Point) : Prop :=
  is_convex_hull base hull \/
  exists p,
    hull = p :: nil /\
    forall q, In q base -> point_same q p.

Lemma is_convex_hull_direct : forall base hull,
  Maximality.is_convex_hull base hull ->
  is_convex_hull base hull.
Proof.
  intros base hull H.
  left.
  exact H.
Qed.

Lemma is_convex_hull_rev_stack : forall base hull,
  is_convex_hull base hull ->
  is_convex_hull base (rev hull).
Proof.
  intros base hull [H | H].
  - right.
    rewrite rev_involutive.
    exact H.
  - left.
    exact H.
Qed.

Definition points_in_bound (l : list Point) : Prop :=
  Forall (fun p => point_in_bound p) l.

Lemma points_in_bound_app_l : forall l1 l2,
  points_in_bound (l1 ++ l2) ->
  points_in_bound l1.
Proof.
  unfold points_in_bound.
  intros l1 l2 H.
  apply Forall_app in H.
  tauto.
Qed.

Definition point_swap (l : list Point) (i j : Z) : list Point :=
  replace_Znth j (Znth i l default_point)
    (replace_Znth i (Znth j l default_point) l).

Lemma point_swap_0_0 : forall l,
  point_swap l 0 0 = l.
Proof.
  intros l.
  unfold point_swap.
  rewrite replace_Znth_Znth.
  rewrite replace_Znth_Znth.
  reflexivity.
Qed.

Definition point_permutation : list Point -> list Point -> Prop :=
  @Permutation Point.

Lemma replace_znth_swap_form : forall {A : Type} (l1 l2 l3 : list A) (xi xj : A),
  replace_Znth (Zlength l1 + 1 + Zlength l2) xi
    (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
  l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xi :: l2 ++ xj :: l3))
    by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0 : replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
               xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xj :: l2 ++ xj :: l3))
    by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := A) (n1 + 1 + Zlength l2) l1 xi)
    by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2)
    by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := (xj :: l3)) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3) by reflexivity.
  rewrite H1.
  reflexivity.
Qed.

Lemma permutation_swap_znth_lt : forall {A : Type} (l : list A) i j (d : A),
  0 <= i /\ i < j /\ j < Zlength l ->
  Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hrange.
  destruct Hrange as [Hi [Hij Hj]].
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr : (nj < List.length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert (Hnat : (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm.
      rewrite Hnat.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_znth_swap_form.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.

Lemma replace_nth_comm_any : forall {A : Type} ni nj (l : list A) (a b : A),
  ni <> nj ->
  replace_nth nj (replace_nth ni l a) b =
  replace_nth ni (replace_nth nj l b) a.
Proof.
  intros A ni nj l a b Hneq.
  revert nj l Hneq.
  induction ni; intros nj l Hneq; destruct l as [| x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal.
      apply IHni.
      intros Heq.
      apply Hneq.
      now f_equal.
Qed.

Lemma replace_znth_comm : forall {A : Type} (l : list A) i j (a b : A),
  0 <= i ->
  0 <= j ->
  i <> j ->
  replace_Znth j b (replace_Znth i a l) =
  replace_Znth i a (replace_Znth j b l).
Proof.
  intros A l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm_any.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma replace_Znth_twice : forall {A : Type} (l : list A) i (a b : A),
  0 <= i < Zlength l ->
  replace_Znth i a (replace_Znth i b l) = replace_Znth i a l.
Proof.
  intros A l i a b Hi.
  unfold replace_Znth.
  assert (Htwice : forall n l,
    replace_nth n (replace_nth n l b) a = replace_nth n l a).
  {
    induction n as [| n IHn]; intros [| x xs]; simpl; auto.
    f_equal. apply IHn.
  }
  apply Htwice.
Qed.

Lemma permutation_swap_znth : forall {A : Type} (l : list A) i j (d : A),
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_znth_lt.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_znth_comm by lia.
      apply permutation_swap_znth_lt.
      lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma point_swap_permutation : forall l i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  point_permutation l (point_swap l i j).
Proof.
  intros l i j Hi Hj.
  unfold point_permutation, point_swap.
  apply permutation_swap_znth; assumption.
Qed.

Definition point_same_outside_range (l l1 : list Point) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 default_point = Znth k l default_point.

Lemma point_swap_Znth_left_index : forall l i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  Znth i (point_swap l i j) default_point = Znth j l default_point.
Proof.
  intros l i j Hi Hj.
  unfold point_swap.
  destruct (Z.eq_dec j i) as [-> | Hji].
  - rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
    reflexivity.
  - rewrite Znth_replace_Znth_Diff with (i := j) (j := i)
      by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
Qed.

Lemma point_swap_Znth_right_index : forall l i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  Znth j (point_swap l i j) default_point = Znth i l default_point.
Proof.
  intros l i j Hi Hj.
  unfold point_swap.
  rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
  reflexivity.
Qed.

Lemma point_swap_Znth_other_index : forall l i j k,
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  0 <= k < Zlength l ->
  k <> i ->
  k <> j ->
  Znth k (point_swap l i j) default_point = Znth k l default_point.
Proof.
  intros l i j k Hi Hj Hk Hki Hkj.
  unfold point_swap.
  rewrite Znth_replace_Znth_Diff with (i := j) (j := k)
    by (try rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff with (i := i) (j := k)
    by lia.
  reflexivity.
Qed.

Lemma point_same_outside_range_point_swap_inside : forall base cur left right i j,
  point_same_outside_range base cur left right ->
  0 <= i < Zlength cur ->
  0 <= j < Zlength cur ->
  left <= i <= right ->
  left <= j <= right ->
  point_same_outside_range base (point_swap cur i j) left right.
Proof.
  intros base cur left right i j Hsame Hi_range Hj_range Hi Hj.
  destruct Hsame as [Hlen Hsame].
  split.
  - unfold point_swap. repeat rewrite Zlength_replace_Znth. exact Hlen.
  - intros k Hk Hout.
    rewrite point_swap_Znth_other_index; try lia.
    apply Hsame; assumption.
Qed.

Definition point_sorted_range
    (gp : Point) (l : list Point) (left right : Z) : Prop :=
  forall i j,
    left <= i -> i <= j -> j <= right ->
    point_cmp_polar gp (Znth i l default_point) (Znth j l default_point) <= 0.

Definition point_xy_sorted_range
    (l : list Point) (left right : Z) : Prop :=
  forall i j,
    left <= i -> i <= j -> j <= right ->
    point_cmp_leftdown (Znth i l default_point)
                       (Znth j l default_point) <= 0.

Definition point_xy_sorted (l : list Point) : Prop :=
  point_xy_sorted_range l 0 (Zlength l - 1).

Definition point_xy_partitioned_at
    (l : list Point) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => point_cmp_leftdown x (Znth p l default_point) <= 0)
         (sublist low p l) /\
  Forall (fun x => point_cmp_leftdown (Znth p l default_point) x < 0)
         (sublist (p + 1) (high + 1) l).

Definition point_xy_partition_scan_inv
    (before cur : list Point)
    (low high : Z) (pivot : Point) (i j : Z) : Prop :=
  point_permutation before cur /\
  point_same_outside_range before cur low high /\
  Znth high cur default_point = pivot /\
  (forall k, low <= k <= i ->
     point_cmp_leftdown (Znth k cur default_point) pivot <= 0) /\
  (forall k, i < k < j ->
     point_cmp_leftdown pivot (Znth k cur default_point) < 0).

Definition point_from_sorted_range
    (sorted : list Point) (lo hi : Z) (p : Point) : Prop :=
  exists idx,
    lo <= idx < hi /\
    p = Znth idx sorted default_point.

Definition point_chain_uses_range
    (sorted chain : list Point) (lo hi : Z) : Prop :=
  0 <= lo /\
  lo <= hi /\
  hi <= Zlength sorted /\
  Forall (point_from_sorted_range sorted lo hi) chain.

Definition point_list_not_all_same (l : list Point) : Prop :=
  exists i j,
    0 <= i < Zlength l /\
    0 <= j < Zlength l /\
    ~ point_same (Znth i l default_point) (Znth j l default_point).

Definition point_chain_indexed_by_range
    (sorted chain : list Point) (lo hi : Z) (idxs : list Z) : Prop :=
  Zlength idxs = Zlength chain /\
  forall pos,
    0 <= pos < Zlength chain ->
    lo <= Znth pos idxs 0 < hi /\
    Znth pos chain default_point =
      Znth (Znth pos idxs 0) sorted default_point.

Definition point_indices_strict_increasing (idxs : list Z) : Prop :=
  forall a b,
    0 <= a -> a < b -> b < Zlength idxs ->
    Znth a idxs 0 < Znth b idxs 0.

Definition point_indices_strict_decreasing (idxs : list Z) : Prop :=
  forall a b,
    0 <= a -> a < b -> b < Zlength idxs ->
    Znth b idxs 0 < Znth a idxs 0.

Definition point_chain_strictly_uses_range
    (sorted chain : list Point) (lo hi : Z) : Prop :=
  exists idxs,
    point_chain_indexed_by_range sorted chain lo hi idxs /\
    point_indices_strict_increasing idxs.

Definition point_chain_rev_strictly_uses_range
    (sorted chain : list Point) (lo hi : Z) : Prop :=
  exists idxs,
    point_chain_indexed_by_range sorted chain lo hi idxs /\
    point_indices_strict_decreasing idxs.

Definition point_chain_starts_at
    (sorted chain : list Point) (idx : Z) : Prop :=
  0 < Zlength chain ->
  Znth 0 chain default_point = Znth idx sorted default_point.

Definition point_chain_ends_at
    (sorted chain : list Point) (idx : Z) : Prop :=
  0 < Zlength chain ->
  Znth (Zlength chain - 1) chain default_point =
    Znth idx sorted default_point.

Definition point_chain_left_turns (chain : list Point) : Prop :=
  forall idx,
    0 <= idx ->
    idx + 2 < Zlength chain ->
    ccw (Znth idx chain default_point)
        (Znth (idx + 1) chain default_point)
        (Znth (idx + 2) chain default_point).

Definition point_chain_left_envelope
    (sorted chain : list Point) (lo hi : Z) : Prop :=
  forall edge_idx point_idx,
    0 <= edge_idx ->
    edge_idx + 1 < Zlength chain ->
    lo <= point_idx < hi ->
    0 <= point_cross
           (Znth edge_idx chain default_point)
           (Znth (edge_idx + 1) chain default_point)
           (Znth point_idx sorted default_point).

Definition andrew_lower_chain_geometry
    (sorted chain : list Point) (read : Z) : Prop :=
  point_chain_uses_range sorted chain 0 read /\
  point_chain_strictly_uses_range sorted chain 0 read /\
  point_chain_starts_at sorted chain 0 /\
  point_chain_left_turns chain /\
  point_chain_left_envelope sorted chain 0 read.

Definition andrew_lower_finished_chain
    (sorted chain : list Point) : Prop :=
  point_chain_uses_range sorted chain 0 (Zlength sorted) /\
  point_chain_strictly_uses_range sorted chain 0 (Zlength sorted) /\
  point_chain_starts_at sorted chain 0 /\
  point_chain_ends_at sorted chain (Zlength sorted - 1) /\
  point_chain_left_turns chain /\
  point_chain_left_envelope sorted chain 0 (Zlength sorted) /\
  points_in_bound chain /\
  point_list_not_all_same sorted /\
  2 <= Zlength chain.

Definition andrew_upper_suffix_geometry
    (sorted chain : list Point) (read lower_n : Z) : Prop :=
  let suffix := sublist lower_n (Zlength chain) chain in
  point_chain_uses_range sorted suffix read (Zlength sorted) /\
  point_chain_rev_strictly_uses_range sorted suffix read (Zlength sorted) /\
  point_chain_left_turns suffix /\
  point_chain_left_envelope sorted suffix read (Zlength sorted).

Definition andrew_complete_hull_shape
    (sorted hull : list Point) : Prop :=
  2 <= Zlength hull <= 2 * Zlength sorted /\
  point_chain_uses_range sorted hull 0 (Zlength sorted) /\
  points_in_bound hull /\
  is_convex_hull sorted hull.

Definition point_drop_last (l : list Point) : list Point :=
  sublist 0 (Zlength l - 1) l.

Lemma point_drop_last_snoc : forall prefix last,
  point_drop_last (prefix ++ last :: nil) = prefix.
Proof.
  intros prefix last.
  unfold point_drop_last.
  replace (Zlength (prefix ++ last :: nil) - 1) with (Zlength prefix).
  - apply sublist_app_exact1.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    pose proof (Zlength_nonneg prefix). lia.
Qed.

Lemma point_drop_last_decompose : forall l,
  0 < Zlength l ->
  exists prefix last, l = prefix ++ last :: nil /\ point_drop_last l = prefix.
Proof.
  intros l Hlen.
  destruct (list_snoc_destruct l) as [Hnil | [last [prefix Hsnoc]]].
  - subst l. rewrite Zlength_nil in Hlen. lia.
  - subst l. exists prefix, last. split; [reflexivity |].
    apply point_drop_last_snoc.
Qed.

Lemma point_drop_last_Zlength : forall l,
  0 < Zlength l ->
  Zlength (point_drop_last l) = Zlength l - 1.
Proof.
  intros l Hlen.
  unfold point_drop_last.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma point_drop_last_Znth : forall l idx d,
  0 <= idx < Zlength l - 1 ->
  Znth idx (point_drop_last l) d = Znth idx l d.
Proof.
  intros l idx d Hidx.
  unfold point_drop_last.
  rewrite Znth_sublist by lia.
  replace (idx + 0) with idx by lia.
  reflexivity.
Qed.

Definition andrew_ccw_complete_hull_shape
    (sorted chain : list Point) : Prop :=
  andrew_complete_hull_shape sorted (rev chain).

Definition andrew_closed_ccw_complete_hull_shape
    (sorted chain : list Point) : Prop :=
  0 < Zlength chain /\
  andrew_ccw_complete_hull_shape sorted (point_drop_last chain).

Definition point_prefix_reverse_state
    (original current : list Point) (len done : Z) : Prop :=
  Zlength original = len /\
  Zlength current = len /\
  0 <= done <= len / 2 /\
  forall idx,
    0 <= idx < len ->
    Znth idx current default_point =
      if Z_lt_dec idx done then
        Znth (len - 1 - idx) original default_point
      else if Z_le_dec (len - done) idx then
        Znth (len - 1 - idx) original default_point
      else
        Znth idx original default_point.

Definition andrew_lower_append_ready
    (sorted chain : list Point) (read : Z) : Prop :=
  read < Zlength sorted ->
  (Zlength chain < 2 \/
   0 < point_cross
         (Znth (Zlength chain - 2) chain default_point)
         (Znth (Zlength chain - 1) chain default_point)
         (Znth read sorted default_point)) ->
  andrew_lower_chain_geometry
    sorted (chain ++ [Znth read sorted default_point]) (read + 1).

Definition andrew_upper_capacity
    (sorted chain : list Point) (read lower_n : Z) : Prop :=
  lower_n <= Zlength sorted /\
  Zlength chain <= lower_n + (Zlength sorted - read) /\
  (1 <= read -> Zlength chain < 2 * Zlength sorted).

Definition andrew_upper_append_ready
    (sorted chain : list Point) (read lower_n : Z) : Prop :=
  0 <= read - 1 ->
  (Zlength chain <= lower_n \/
   0 < point_cross
         (Znth (Zlength chain - 2) chain default_point)
         (Znth (Zlength chain - 1) chain default_point)
         (Znth (read - 1) sorted default_point)) ->
  andrew_upper_suffix_geometry
    sorted (chain ++ [Znth (read - 1) sorted default_point]) (read - 1) lower_n /\
  andrew_upper_capacity
    sorted (chain ++ [Znth (read - 1) sorted default_point]) (read - 1) lower_n /\
  (read - 1 <= 0 ->
     andrew_closed_ccw_complete_hull_shape
       sorted (chain ++ [Znth (read - 1) sorted default_point])).

Definition andrew_lower_scan_inv
    (sorted chain : list Point) (read top : Z) : Prop :=
  0 <= read <= Zlength sorted /\
  top = Zlength chain /\
  0 <= top <= read /\
  points_in_bound chain /\
  Forall (fun p => In p sorted) chain /\
  (Zlength sorted <= read -> 2 <= top).

(* The upper scan's algorithmic geometry is carried by explicit [safeExec]
   continuation clauses.  This invariant stays focused on C-side state facts
   needed for bounds and memory reasoning. *)
Definition andrew_upper_scan_inv
    (sorted chain : list Point) (read top lower_n : Z) : Prop :=
  0 <= read <= Zlength sorted /\
  lower_n <= top <= 2 * Zlength sorted /\
  top = Zlength chain /\
  (read <= 0 -> lower_n < top) /\
  points_in_bound chain /\
  Forall (fun p => In p sorted) chain /\
  andrew_upper_capacity sorted chain read lower_n.

Definition point_polar_partitioned_at
    (gp : Point) (l : list Point) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => point_cmp_polar gp x (Znth p l default_point) <= 0)
         (sublist low p l) /\
  Forall (fun x => point_cmp_polar gp (Znth p l default_point) x < 0)
         (sublist (p + 1) (high + 1) l).

Definition point_polar_partition_scan_inv
    (gp : Point) (before cur : list Point)
    (low high : Z) (pivot : Point) (i j : Z) : Prop :=
  point_permutation before cur /\
  point_same_outside_range before cur low high /\
  Znth high cur default_point = pivot /\
  (forall k, low <= k <= i ->
     point_cmp_polar gp (Znth k cur default_point) pivot <= 0) /\
  (forall k, i < k < j ->
     point_cmp_polar gp pivot (Znth k cur default_point) < 0).

Definition build_hull_c_iter (l : list Point) (i : Z)
  : program (list Point) unit :=
  iter step_p (sublist i (Zlength l) l) tt.

Definition build_hull_c_next (l : list Point) (i : Z) (_ : unit)
  : program (list Point) unit :=
  build_hull_c_iter l (i + 1).

Definition build_hull_c_step (l : list Point) (i : Z)
  : program (list Point) unit :=
  bind (step_fun (Znth i l default_point))
       (build_hull_c_next l i).

Definition build_hull_c_push (l : list Point) (i : Z)
  : program (list Point) unit :=
  T <- get' id ;;
  update' (fun _ => Znth i l default_point :: T) ;;
  build_hull_c_iter l (i + 1).

Definition andrew_upper_remaining_points
    (sorted : list Point) (read : Z) : list Point :=
  rev (sublist 0 read sorted).

Definition andrew_upper_stack_from_chain
    (chain : list Point) (lower_n : Z) : list Point :=
  rev (sublist (lower_n - 1) (Zlength chain) chain).

Definition andrew_upper_cont
    (sorted lower : list Point) (read : Z)
    : program (list Point) unit :=
  iter step_p (andrew_upper_remaining_points sorted read) tt ;;
  T <- get' id ;;
  update' (fun _ => Andrew_Monotone_Chain.andrew_merge sorted lower (rev T)).

Definition andrew_lower_cont
    (sorted : list Point) (read : Z)
    : program (list Point) unit :=
  build_hull_c_iter sorted read ;;
  T <- get' id ;;
  let lower := rev T in
  upper <- Andrew_Monotone_Chain_M.build_upper_chain sorted ;;
  update' (fun _ => Andrew_Monotone_Chain.andrew_merge sorted lower upper).

Lemma pop_fun_continue_hseval : forall p t s T,
  ~ ccw s t p ->
  equiv (t :: s :: T) -@ pop_fun p -⥅ equiv (s :: T) ♯ by_continue tt.
Proof.
  intros p t s T Hnccw.
  unfold hs_eval.
  intros st Hst.
  hnf in Hst. subst st.
  unfold pop_fun.
  exists (s :: T).
  split.
  - unfold_monad; sets_unfold; simpl.
    exists (t :: s :: T), (t :: s :: T).
    split; [split; reflexivity |].
    right.
    exists tt, (t :: s :: T).
    split; [split; [exact Hnccw | reflexivity] |].
    exists tt, (s :: T).
    split; [reflexivity |].
    split; reflexivity.
  - reflexivity.
Qed.

Lemma pop_fun_ccw_break_hseval : forall p t s T,
  ccw s t p ->
  equiv (t :: s :: T) -@ pop_fun p -⥅ equiv (t :: s :: T) ♯ by_break tt.
Proof.
  intros p t s T Hccw.
  unfold hs_eval.
  intros st Hst.
  hnf in Hst. subst st.
  unfold pop_fun.
  exists (t :: s :: T).
  split.
  - unfold_monad; sets_unfold; simpl.
    exists (t :: s :: T), (t :: s :: T).
    split; [split; reflexivity |].
    left.
    exists tt, (t :: s :: T).
    split; [split; [exact Hccw | reflexivity] |].
    split; reflexivity.
  - reflexivity.
Qed.

Lemma pop_fun_nil_break_hseval : forall p,
  equiv nil -@ pop_fun p -⥅ equiv nil ♯ by_break tt.
Proof.
  intros p.
  unfold hs_eval.
  intros st Hst.
  hnf in Hst. subst st.
  unfold pop_fun.
  exists nil.
  split.
  - unfold_monad; sets_unfold; simpl.
    exists nil, nil.
    split; [split; reflexivity |].
    split; reflexivity.
  - reflexivity.
Qed.

Lemma pop_fun_single_break_hseval : forall p t,
  equiv (t :: nil) -@ pop_fun p -⥅ equiv (t :: nil) ♯ by_break tt.
Proof.
  intros p t.
  unfold hs_eval.
  intros st Hst.
  hnf in Hst. subst st.
  unfold pop_fun.
  exists (t :: nil).
  split.
  - unfold_monad; sets_unfold; simpl.
    exists (t :: nil), (t :: nil).
    split; [split; reflexivity |].
    split; reflexivity.
  - reflexivity.
Qed.

Lemma repeat_pop_fun_ccw_break_hseval : forall p t s T,
  ccw s t p ->
  equiv (t :: s :: T) -@
    repeat_break (fun _ : unit => pop_fun p) tt
    -⥅ equiv (t :: s :: T) ♯ tt.
Proof.
  intros p t s T Hccw.
  unfold_loop.
  eapply (hsevalbind_derive'
            (pop_fun p)
            (fun x =>
               match x with
               | by_continue a0 => repeat_break (fun _ : unit => pop_fun p) a0
               | by_break b0 => ret b0
               end)
            (equiv (t :: s :: T)) (equiv (t :: s :: T))
            (by_break tt) (equiv (t :: s :: T)) tt).
  - apply pop_fun_ccw_break_hseval.
    exact Hccw.
  - simpl.
    apply highret_eval2.
Qed.

Lemma repeat_pop_fun_nil_break_hseval : forall p,
  equiv nil -@
    repeat_break (fun _ : unit => pop_fun p) tt
    -⥅ equiv nil ♯ tt.
Proof.
  intros p.
  unfold_loop.
  eapply (hsevalbind_derive'
            (pop_fun p)
            (fun x =>
               match x with
               | by_continue a0 => repeat_break (fun _ : unit => pop_fun p) a0
               | by_break b0 => ret b0
               end)
            (equiv nil) (equiv nil) (by_break tt) (equiv nil) tt).
  - apply pop_fun_nil_break_hseval.
  - simpl.
    apply highret_eval2.
Qed.

Lemma repeat_pop_fun_single_break_hseval : forall p t,
  equiv (t :: nil) -@
    repeat_break (fun _ : unit => pop_fun p) tt
    -⥅ equiv (t :: nil) ♯ tt.
Proof.
  intros p t.
  unfold_loop.
  eapply (hsevalbind_derive'
            (pop_fun p)
            (fun x =>
               match x with
               | by_continue a0 => repeat_break (fun _ : unit => pop_fun p) a0
               | by_break b0 => ret b0
               end)
            (equiv (t :: nil)) (equiv (t :: nil)) (by_break tt)
            (equiv (t :: nil)) tt).
  - apply pop_fun_single_break_hseval.
  - simpl.
    apply highret_eval2.
Qed.

Lemma get_update_push_hseval : forall p stk,
  equiv stk -@
    (T <- get' id;; update' (fun _ : list Point => p :: T))
    -⥅ equiv (p :: stk) ♯ tt.
Proof.
  intros p stk.
  unfold hs_eval.
  intros st Hst.
  hnf in Hst. subst st.
  exists (p :: stk).
  split.
  - unfold_monad; sets_unfold; simpl.
    exists stk, stk.
    split; [split; reflexivity |].
    reflexivity.
  - reflexivity.
Qed.

Lemma step_fun_ccw_push_hseval : forall p t s T,
  ccw s t p ->
  equiv (t :: s :: T) -@ step_fun p
    -⥅ equiv (p :: t :: s :: T) ♯ tt.
Proof.
  intros p t s T Hccw.
  unfold Graham_Scan_M.step_fun.
  eapply (hsevalbind_derive'
            (repeat_break (fun _ : unit => pop_fun p) tt)
            (fun _ => T0 <- get' id;;
                      update' (fun _ : list Point => p :: T0))
            (equiv (t :: s :: T)) (equiv (t :: s :: T)) tt
            (equiv (p :: t :: s :: T)) tt).
  - apply repeat_pop_fun_ccw_break_hseval.
    exact Hccw.
  - apply get_update_push_hseval.
Qed.

Lemma step_fun_nil_push_hseval : forall p,
  equiv nil -@ step_fun p -⥅ equiv (p :: nil) ♯ tt.
Proof.
  intros p.
  unfold Graham_Scan_M.step_fun.
  eapply (hsevalbind_derive'
            (repeat_break (fun _ : unit => pop_fun p) tt)
            (fun _ => T0 <- get' id;;
                      update' (fun _ : list Point => p :: T0))
            (equiv nil) (equiv nil) tt
            (equiv (p :: nil)) tt).
  - apply repeat_pop_fun_nil_break_hseval.
  - apply get_update_push_hseval.
Qed.

Lemma step_fun_single_push_hseval : forall p t,
  equiv (t :: nil) -@ step_fun p -⥅ equiv (p :: t :: nil) ♯ tt.
Proof.
  intros p t.
  unfold Graham_Scan_M.step_fun.
  eapply (hsevalbind_derive'
            (repeat_break (fun _ : unit => pop_fun p) tt)
            (fun _ => T0 <- get' id;;
                      update' (fun _ : list Point => p :: T0))
            (equiv (t :: nil)) (equiv (t :: nil)) tt
            (equiv (p :: t :: nil)) tt).
  - apply repeat_pop_fun_single_break_hseval.
  - apply get_update_push_hseval.
Qed.

Lemma safeExec_bind_assoc_forward :
  forall {A B C : Type} (P : list Point -> Prop)
         (c0 : program (list Point) A)
         (c1 : A -> program (list Point) B)
         (c2 : B -> program (list Point) C) X,
    safeExec P (bind (bind c0 c1) c2) X ->
    safeExec P (bind c0 (fun x => bind (c1 x) c2)) X.
Proof.
  intros.
  eapply safeExec_proequiv.
  - apply bind_assoc.
  - exact H.
Qed.

Lemma safeExec_build_hull_c_step_ccw_push : forall l i t s T X,
  ccw s t (Znth i l default_point) ->
  safeExec (equiv (t :: s :: T)) (build_hull_c_step l i) X ->
  safeExec (equiv (Znth i l default_point :: t :: s :: T))
           (build_hull_c_iter l (i + 1)) X.
Proof.
  intros l i t s T X Hccw Hsafe.
  unfold build_hull_c_step in Hsafe at 1.
  unfold build_hull_c_next in Hsafe.
  eapply (highstepbind_derive
            (Graham_Scan_M.step_fun (Znth i l default_point))
            (fun _ : unit => build_hull_c_iter l (i + 1))
            (equiv (t :: s :: T)) tt
            (equiv (Znth i l default_point :: t :: s :: T))).
  - apply step_fun_ccw_push_hseval.
    exact Hccw.
  - exact Hsafe.
Qed.

Lemma safeExec_build_hull_c_step_nil_push : forall l i X,
  safeExec (equiv nil) (build_hull_c_step l i) X ->
  safeExec (equiv (Znth i l default_point :: nil))
           (build_hull_c_iter l (i + 1)) X.
Proof.
  intros l i X Hsafe.
  unfold build_hull_c_step in Hsafe at 1.
  unfold build_hull_c_next in Hsafe.
  eapply (highstepbind_derive
            (Graham_Scan_M.step_fun (Znth i l default_point))
            (fun _ : unit => build_hull_c_iter l (i + 1))
            (equiv nil) tt
            (equiv (Znth i l default_point :: nil))).
  - apply step_fun_nil_push_hseval.
  - exact Hsafe.
Qed.

Lemma safeExec_build_hull_c_step_single_push : forall l i t X,
  safeExec (equiv (t :: nil)) (build_hull_c_step l i) X ->
  safeExec (equiv (Znth i l default_point :: t :: nil))
           (build_hull_c_iter l (i + 1)) X.
Proof.
  intros l i t X Hsafe.
  unfold build_hull_c_step in Hsafe at 1.
  unfold build_hull_c_next in Hsafe.
  eapply (highstepbind_derive
            (Graham_Scan_M.step_fun (Znth i l default_point))
            (fun _ : unit => build_hull_c_iter l (i + 1))
            (equiv (t :: nil)) tt
            (equiv (Znth i l default_point :: t :: nil))).
  - apply step_fun_single_push_hseval.
  - exact Hsafe.
Qed.

Lemma safeExec_build_hull_c_step_pop : forall l i t s T X,
  ~ ccw s t (Znth i l default_point) ->
  safeExec (equiv (t :: s :: T)) (build_hull_c_step l i) X ->
  safeExec (equiv (s :: T)) (build_hull_c_step l i) X.
Proof.
  intros l i t s T X Hnccw Hsafe.
  unfold build_hull_c_step in Hsafe at 1.
  unfold build_hull_c_next in Hsafe.
  unfold Graham_Scan_M.step_fun in Hsafe at 1.
  prog_nf in Hsafe.
  unfold_loop in Hsafe.
  prog_nf in Hsafe.
  eapply (safeExec_proequiv
            (bind
               (H <- repeat_break
                       (fun _ : unit =>
                          Graham_Scan_M.pop_fun (Znth i l default_point)) tt;;
                T0 <- get' id;;
                update' (fun _ : list Point => Znth i l default_point :: T0))
               (fun _ : unit => build_hull_c_iter l (i + 1)))
            (build_hull_c_step l i)
            (equiv (s :: T)) X).
  - unfold build_hull_c_step, build_hull_c_next, Graham_Scan_M.step_fun.
    reflexivity.
  - eapply safeExec_bind_assoc_forward in Hsafe.
    eapply (highstepbind_derive
              (Graham_Scan_M.pop_fun (Znth i l default_point))
              (fun x =>
                 bind
                   (match x with
                    | by_continue a0 =>
                        repeat_break
                          (fun _ : unit =>
                             Graham_Scan_M.pop_fun (Znth i l default_point)) a0
                    | by_break b0 => ret b0
                    end;;
                    T0 <- get' id;;
                    update' (fun _ : list Point =>
                                Znth i l default_point :: T0))
                   (fun _ : unit => build_hull_c_iter l (i + 1)))
              (equiv (t :: s :: T)) (by_continue tt) (equiv (s :: T))).
    + apply pop_fun_continue_hseval.
      exact Hnccw.
    + exact Hsafe.
Qed.

Lemma Znth_rev_stack_prev : forall (d t s : Point) (T : list Point) top,
  top + 1 = Zlength (rev (t :: s :: T)) ->
  Znth (top - 1 - 0) (rev (t :: s :: T)) d = s.
Proof.
  intros.
  simpl in H |- *.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in H.
  pose proof (Zlength_nonneg (rev T)) as Hrev_nonneg.
  assert (Htop : top = Zlength (rev T) + 1) by lia.
  subst top.
  replace (Zlength (rev T) + 1 - 1 - 0) with (Zlength (rev T)) by lia.
  rewrite app_Znth1.
  - rewrite app_Znth2.
    + replace (Zlength (rev T) - Zlength (rev T)) with 0 by lia.
      reflexivity.
    + lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma Znth_rev_stack_top : forall (d t s : Point) (T : list Point) top,
  top + 1 = Zlength (rev (t :: s :: T)) ->
  Znth (top - 0) (rev (t :: s :: T)) d = t.
Proof.
  intros.
  simpl in H |- *.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in H.
  pose proof (Zlength_nonneg (rev T)) as Hrev_nonneg.
  assert (Htop : top = Zlength (rev T) + 1) by lia.
  subst top.
  replace (Zlength (rev T) + 1 - 0) with (Zlength (rev T ++ [s]))
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite app_Znth2.
  - replace (Zlength (rev T ++ [s]) - Zlength (rev T ++ [s])) with 0 by lia.
    reflexivity.
  - lia.
Qed.

Lemma rev_stack_pop_top : forall (t s : Point) (T : list Point) top,
  top + 1 = Zlength (rev (t :: s :: T)) ->
  top = Zlength (rev (s :: T)).
Proof.
  intros.
  simpl in H |- *.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in H.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma rev_stack_two_len_ge : forall (t s : Point) (T : list Point),
  2 <= Zlength (rev (t :: s :: T)).
Proof.
  intros.
  simpl.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
  pose proof (Zlength_nonneg (rev T)).
  lia.
Qed.

Lemma point_cross_unfold : forall a b c,
  point_cross a b c =
  (x b - x a) * (y c - y a) - (y b - y a) * (x c - x a).
Proof.
  intros.
  unfold point_cross, x, y, cross_prod, build_vec.
  simpl.
  nia.
Qed.

Lemma point_cross_by_value_point : forall a b c,
  point_cross_by_value (x a) (y a) (x b) (y b) (x c) (y c) =
  point_cross a b c.
Proof.
  intros.
  unfold point_cross_by_value.
  symmetry.
  apply point_cross_unfold.
Qed.

Lemma point_dot_unfold : forall a b c,
  point_dot a b c =
  (x b - x a) * (x c - x a) + (y b - y a) * (y c - y a).
Proof.
  intros.
  unfold point_dot, x, y, dot_prod, build_vec.
  simpl.
  nia.
Qed.

Lemma point_dot_by_value_point : forall a b c,
  point_dot_by_value (x a) (y a) (x b) (y b) (x c) (y c) =
  point_dot a b c.
Proof.
  intros.
  unfold point_dot_by_value.
  symmetry.
  apply point_dot_unfold.
Qed.

Lemma point_cross_zero_point_colinear : forall gp pa pb,
  point_cross gp pa pb = 0 ->
  point_colinear gp pa pb.
Proof.
  intros.
  unfold point_colinear.
  assumption.
Qed.

Lemma point_at_mid_by_value : forall gp pa pb gp_x gp_y a_x a_y b_x b_y,
  gp_x = x gp -> gp_y = y gp ->
  a_x = x pa -> a_y = y pa ->
  b_x = x pb -> b_y = y pb ->
  (b_x - a_x) * (gp_x - a_x) + (b_y - a_y) * (gp_y - a_y) = point_at_mid gp pa pb.
Proof.
  intros. subst.
  unfold point_at_mid.
  rewrite point_dot_unfold.
  unfold x, y.
  reflexivity.
Qed.

Lemma point_cross_gt_0_ccw_local : forall a b c,
  point_cross a b c > 0 ->
  ccw a b c.
Proof.
  intros a b c H.
  unfold point_cross, ccw, left_than, cross_prod, build_vec in *.
  simpl in *.
  lia.
Qed.

Lemma point_cross_le_0_not_ccw_local : forall a b c,
  point_cross a b c <= 0 ->
  ~ ccw a b c.
Proof.
  intros a b c H.
  apply Point_Order.point_cross_le_0_not_ccw.
  exact H.
Qed.

Lemma point_cross_zero_point_colinear_swap : forall gp pa pb,
  point_cross gp pa pb = 0 ->
  point_colinear gp pb pa.
Proof.
  intros gp pa pb H.
  unfold point_colinear, point_cross in *.
  rewrite cross_prod_comm.
  lia.
Qed.

Lemma point_at_mid_le_at_mid : forall gp pa pb,
  point_at_mid gp pa pb <= 0 ->
  at_mid pa pb gp.
Proof.
  intros gp pa pb H.
  unfold point_at_mid, point_dot in H.
  unfold at_mid, backward_or_perp.
  unfold dot_prod, build_vec, x, y in *.
  simpl in *.
  lia.
Qed.

Lemma point_cmp_polar_le_point_weak_polar_le : forall gp pa pb,
  point_cmp_polar gp pa pb <= 0 ->
  point_weak_polar_le gp pa pb.
Proof.
  intros gp pa pb Hle.
  unfold point_cmp_polar in Hle.
  unfold point_weak_polar_le, point_weak_rev_ccw.
  destruct (Z_gt_dec (point_cross gp pa pb) 0) as [Hcr_pos | Hcr_not_pos].
  - left.
    apply ccw_cyclicity_2.
    apply point_cross_gt_0_ccw_local.
    exact Hcr_pos.
  - destruct (Z_lt_dec (point_cross gp pa pb) 0) as [Hcr_neg | Hcr_not_neg].
    + lia.
    + assert (Hcr_zero : point_cross gp pa pb = 0) by lia.
      destruct (Z_gt_dec (point_at_mid gp pa pb) 0) as [Hmid_pos | Hmid_not_pos].
      * lia.
      * right.
        split.
        -- apply point_cross_zero_point_colinear_swap.
           exact Hcr_zero.
        -- apply point_at_mid_le_at_mid.
           lia.
Qed.

Lemma point_polar_sorted_point_weak_polar_sorted : forall gp l,
  point_polar_sorted gp l ->
  point_weak_polar_sorted gp l.
Proof.
  unfold point_polar_sorted, point_weak_polar_sorted.
  intros gp l Hsorted i j d Hij Hj.
  apply point_cmp_polar_le_point_weak_polar_le.
  apply Hsorted; assumption.
Qed.

Lemma point_colinear_colinear : forall pivot a b,
  point_colinear pivot a b <-> colinear pivot a b.
Proof.
  intros.
  unfold point_colinear, point_cross, colinear, parallel.
  reflexivity.
Qed.

Lemma point_weak_rev_ccw_g_rev_ccw : forall pivot a b,
  point_weak_rev_ccw pivot a b <-> g_rev_ccw pivot a b.
Proof.
  intros pivot a b.
  unfold point_weak_rev_ccw, g_rev_ccw, weak_rev_ccw.
  split; intros [Hccw | [Hcol Hmid]].
  - left.
    exact Hccw.
  - right.
    split.
    + apply point_colinear_colinear.
      exact Hcol.
    + exact Hmid.
  - left.
    exact Hccw.
  - right.
    split.
    + apply point_colinear_colinear.
      exact Hcol.
    + exact Hmid.
Qed.

Lemma In_Znth_Zlength : forall {A : Type} (l : list A) (x d : A),
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  pose proof (@In_nth A l x d Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    exact Hnth.
Qed.

Lemma Forall_Znth_intro : forall {A : Type} (P : A -> Prop) l d,
  (forall i, 0 <= i < Zlength l -> P (Znth i l d)) ->
  Forall P l.
Proof.
  intros A P l d Hnth.
  rewrite Forall_forall.
  intros x Hin.
  destruct (In_Znth_Zlength l x d Hin) as [i [Hi Hx]].
  rewrite <- Hx.
  apply Hnth.
  exact Hi.
Qed.

Lemma point_leftmost_prefix_leftmost : forall l pivot_idx,
  point_leftmost_prefix l pivot_idx (Zlength l) ->
  leftmost (Znth pivot_idx l default_point) l.
Proof.
  intros l pivot_idx Hprefix.
  unfold point_leftmost_prefix in Hprefix.
  destruct Hprefix as [_ [_ Hmin]].
  unfold leftmost.
  apply Forall_Znth_intro with (d := default_point).
  intros i Hi.
  specialize (Hmin i Hi).
  unfold point_leftdown, x, y in Hmin.
  exact Hmin.
Qed.

Lemma leftmost_sublist : forall p l lo hi,
  0 <= lo <= hi ->
  hi <= Zlength l ->
  leftmost p l ->
  leftmost p (sublist lo hi l).
Proof.
  intros p l lo hi Hlohi Hhi Hleft.
  unfold leftmost in *.
  apply Forall_Znth_intro with (d := default_point).
  intros i Hi.
  rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia.
  rewrite Forall_forall in Hleft.
  apply Hleft.
  unfold Znth.
  apply nth_In.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma point_weak_polar_sorted_cons_tail : forall pivot a l,
  point_weak_polar_sorted pivot (a :: l) ->
  point_weak_polar_sorted pivot l.
Proof.
  unfold point_weak_polar_sorted.
  intros pivot a l Hsorted i j d Hij Hj.
  specialize (Hsorted (i + 1) (j + 1) d).
  rewrite !Znth_cons in Hsorted by lia.
  replace (i + 1 - 1) with i in Hsorted by lia.
  replace (j + 1 - 1) with j in Hsorted by lia.
  apply Hsorted.
  - lia.
  - rewrite Zlength_cons.
    lia.
Qed.

Lemma point_weak_polar_sorted_cons_head : forall pivot a l,
  point_weak_polar_sorted pivot (a :: l) ->
  Forall (fun q => point_weak_rev_ccw pivot q a) l.
Proof.
  unfold point_weak_polar_sorted, point_weak_polar_le.
  intros pivot a l Hsorted.
  apply Forall_Znth_intro with (d := default_point).
  intros i Hi.
  specialize (Hsorted 0 (i + 1) default_point).
  rewrite Znth0_cons in Hsorted.
  rewrite Znth_cons in Hsorted by lia.
  replace (i + 1 - 1) with i in Hsorted by lia.
  apply Hsorted.
  - lia.
  - rewrite Zlength_cons.
    lia.
Qed.

Lemma point_weak_polar_sorted_g_rev_ccw_list_rev : forall pivot l,
  point_weak_polar_sorted pivot l ->
  g_rev_ccw_list pivot (rev l).
Proof.
  intros pivot l.
  induction l as [| a l IH]; simpl; intros Hsorted.
  - exact I.
  - rewrite g_rev_ccw_list_app_iff.
    repeat split.
    + apply IH.
      eapply point_weak_polar_sorted_cons_tail.
      exact Hsorted.
    + apply Forall_nil.
    + intros q r Hq Hr.
      simpl in Hr.
      destruct Hr as [Hr | []].
      subst r.
      apply point_weak_rev_ccw_g_rev_ccw.
      pose proof (point_weak_polar_sorted_cons_head pivot a l Hsorted) as Hall.
      rewrite Forall_forall in Hall.
      apply Hall.
      rewrite in_rev.
      exact Hq.
Qed.

Lemma point_polar_sorted_g_rev_ccw_list_rev : forall pivot l,
  point_polar_sorted pivot l ->
  g_rev_ccw_list pivot (rev l).
Proof.
  intros pivot l Hsorted.
  apply point_weak_polar_sorted_g_rev_ccw_list_rev.
  apply point_polar_sorted_point_weak_polar_sorted.
  exact Hsorted.
Qed.

Lemma point_weak_polar_sorted_pure_sort_rev : forall pivot l,
  leftmost pivot (rev l) ->
  point_weak_polar_sorted pivot l ->
  Convexity.sort pivot (rev l).
Proof.
  intros pivot l Hleft Hsorted.
  split.
  - exact Hleft.
  - apply point_weak_polar_sorted_g_rev_ccw_list_rev.
    exact Hsorted.
Qed.

Lemma point_polar_sorted_pure_sort_rev : forall pivot l,
  leftmost pivot (rev l) ->
  point_polar_sorted pivot l ->
  Convexity.sort pivot (rev l).
Proof.
  intros pivot l Hleft Hsorted.
  apply point_weak_polar_sorted_pure_sort_rev.
  - exact Hleft.
  - apply point_polar_sorted_point_weak_polar_sorted.
    exact Hsorted.
Qed.

Lemma point_weak_polar_sorted_graham_scan_convex_hull : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_weak_polar_sorted pivot l ->
  is_convex_hull (pivot :: l) (graham_scan (rev (pivot :: l))).
Proof.
  intros pivot l Hleft Hne Hsorted.
  apply is_convex_hull_direct.
  apply graham_scan_closed_convex_hull_final.
  - apply point_weak_polar_sorted_pure_sort_rev; assumption.
  - exact Hne.
Qed.

Lemma point_polar_sorted_graham_scan_convex_hull : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_polar_sorted pivot l ->
  is_convex_hull (pivot :: l) (graham_scan (rev (pivot :: l))).
Proof.
  intros pivot l Hleft Hne Hsorted.
  apply point_weak_polar_sorted_graham_scan_convex_hull.
  - exact Hleft.
  - exact Hne.
  - apply point_polar_sorted_point_weak_polar_sorted.
    exact Hsorted.
Qed.

Lemma point_weak_polar_sorted_build_hull_convex_hull : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_weak_polar_sorted pivot l ->
  Hoare (equiv empty_point_stack)
        (build_hull pivot l)
        (fun _ T => is_convex_hull (pivot :: l) T).
Proof.
  intros pivot l Hleft Hne Hsorted.
  unfold build_hull.
  eapply Hoare_conseq_pre.
  2: {
    eapply Hoare_conseq_post.
    2: {
      apply Graham_Scan_M.build_hull_convex_hull_final.
      - apply point_weak_polar_sorted_pure_sort_rev; assumption.
      - exact Hne.
    }
    intros [] T HT.
    apply is_convex_hull_direct.
    exact HT.
  }
  intros T HT.
  unfold empty_point_stack in HT.
  symmetry.
  exact HT.
Qed.

Lemma point_weak_polar_sorted_build_hull_convex_hull_rev_stack : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_weak_polar_sorted pivot l ->
  Hoare (equiv empty_point_stack)
        (build_hull pivot l)
        (fun _ T => is_convex_hull (pivot :: l) (rev T)).
Proof.
  intros pivot l Hleft Hne Hsorted.
  eapply Hoare_conseq_post.
  2: {
    apply point_weak_polar_sorted_build_hull_convex_hull.
    - exact Hleft.
    - exact Hne.
    - exact Hsorted.
  }
  intros [] T HT.
  apply is_convex_hull_rev_stack.
  exact HT.
Qed.

Lemma point_polar_sorted_build_hull_convex_hull_rev_stack : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_polar_sorted pivot l ->
  Hoare (equiv empty_point_stack)
        (build_hull pivot l)
        (fun _ T => is_convex_hull (pivot :: l) (rev T)).
Proof.
  intros pivot l Hleft Hne Hsorted.
  apply point_weak_polar_sorted_build_hull_convex_hull_rev_stack.
  - exact Hleft.
  - exact Hne.
  - apply point_polar_sorted_point_weak_polar_sorted.
    exact Hsorted.
Qed.

Lemma graham_is_convex_hull_base_permutation : forall base1 base2 hull,
  point_permutation base1 base2 ->
  Maximality.is_convex_hull base2 hull ->
  Maximality.is_convex_hull base1 hull.
Proof.
  intros base1 base2 hull Hperm Hhull.
  unfold point_permutation in Hperm.
  unfold Maximality.is_convex_hull in *.
  destruct Hhull as [Hconv Hmax].
  split; [exact Hconv |].
  unfold is_max_hull'_edges in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hmax.
  eapply Permutation_in; eauto.
Qed.

Lemma graham_is_convex_hull_base_nonempty_hull_nonempty : forall base hull p,
  In p base ->
  Maximality.is_convex_hull base hull ->
  1 <= Zlength hull.
Proof.
  intros base hull p Hin Hhull.
  destruct hull as [| h hull_tail].
  - unfold Maximality.is_convex_hull in Hhull.
    destruct Hhull as [_ Hmax].
    unfold is_max_hull'_edges in Hmax.
    rewrite Forall_forall in Hmax.
    specialize (Hmax p Hin).
    simpl in Hmax.
    contradiction.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg hull_tail).
    lia.
Qed.

Lemma is_convex_hull_base_permutation : forall base1 base2 hull,
  point_permutation base1 base2 ->
  is_convex_hull base2 hull ->
  is_convex_hull base1 hull.
Proof.
  intros base1 base2 hull Hperm [Hhull | Hhull].
  - left.
    eapply graham_is_convex_hull_base_permutation; eauto.
  - right.
    eapply graham_is_convex_hull_base_permutation; eauto.
Qed.

Lemma is_convex_hull_base_nonempty_hull_nonempty : forall base hull p,
  In p base ->
  is_convex_hull base hull ->
  1 <= Zlength hull.
Proof.
  intros base hull p Hin [Hhull | Hhull].
  - eapply graham_is_convex_hull_base_nonempty_hull_nonempty; eauto.
  - pose proof
      (graham_is_convex_hull_base_nonempty_hull_nonempty
         base (rev hull) p Hin Hhull) as Hlen.
    rewrite !Zlength_correct in *.
    rewrite length_rev in Hlen.
    exact Hlen.
Qed.

Lemma point_polar_sorted_build_hull_convex_hull : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_polar_sorted pivot l ->
  Hoare (equiv empty_point_stack)
        (build_hull pivot l)
        (fun _ T => is_convex_hull (pivot :: l) T).
Proof.
  intros pivot l Hleft Hne Hsorted.
  apply point_weak_polar_sorted_build_hull_convex_hull.
  - exact Hleft.
  - exact Hne.
  - apply point_polar_sorted_point_weak_polar_sorted.
    exact Hsorted.
Qed.

Lemma store_point_fold : forall p pt,
  (&((p) # "Point" ->ₛ "x") # Int |-> point_x pt) **
  (&((p) # "Point" ->ₛ "y") # Int |-> point_y pt)
  |-- store_point p pt.
Proof.
  intros.
  unfold store_point.
  apply derivable1_refl.
Qed.

Lemma store_point_to_undef_point : forall p pt,
  store_point p pt |-- undef_point p.
Proof.
  intros.
  unfold store_point, undef_point.
  apply derivable1_sepcon_mono.
  - apply store_int_undef_store_int.
  - apply store_int_undef_store_int.
Qed.

Lemma point_cmp_xy_range : forall a b,
  point_cmp_xy a b = -1 \/ point_cmp_xy a b = 0 \/ point_cmp_xy a b = 1.
Proof.
  intros a b.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); nia.
Qed.

Lemma point_cmp_xy_eq_0 : forall a b,
  point_cmp_xy a b = 0 ->
  x a = x b /\ y a = y b.
Proof.
  intros a b Hcmp.
  unfold point_cmp_xy in Hcmp.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); nia.
Qed.

Lemma point_cmp_xy_x_lt : forall a b,
  x a < x b ->
  point_cmp_xy a b = -1.
Proof.
  intros a b Hlt.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_cmp_xy_x_gt : forall a b,
  x a > x b ->
  point_cmp_xy a b = 1.
Proof.
  intros a b Hgt.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_cmp_xy_y_lt : forall a b,
  x a = x b ->
  y a < y b ->
  point_cmp_xy a b = -1.
Proof.
  intros a b Hx Hy.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_cmp_xy_y_gt : forall a b,
  x a = x b ->
  y a > y b ->
  point_cmp_xy a b = 1.
Proof.
  intros a b Hx Hy.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_cmp_xy_eq : forall a b,
  x a = x b ->
  y a = y b ->
  point_cmp_xy a b = 0.
Proof.
  intros a b Hx Hy.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_cmp_xy_gt_flip_lt : forall a b,
  point_cmp_xy a b > 0 ->
  point_cmp_xy b a < 0.
Proof.
  intros a b Hgt.
  unfold point_cmp_xy in *.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b));
  destruct (Z_lt_dec (x b) (x a));
  destruct (Z_gt_dec (x b) (x a));
  destruct (Z_lt_dec (y b) (y a));
  destruct (Z_gt_dec (y b) (y a)); lia.
Qed.

Lemma point_eq_by_xy : forall a b,
  x a = x b ->
  y a = y b ->
  a = b.
Proof.
  intros a b Hx Hy.
  destruct a.
  destruct b.
  simpl in *.
  subst.
  reflexivity.
Qed.

Lemma point_list_cons_sublist_1_by_fields : forall l n tail p d,
  Zlength l = n ->
  1 <= n ->
  tail = sublist 1 n l ->
  x (Znth 0 l d) = x p ->
  y (Znth 0 l d) = y p ->
  l = p :: tail.
Proof.
  intros l n tail p d Hlen Hn Htail Hx Hy.
  subst tail.
  assert (Hzero : 0 <= 0 < Zlength l) by lia.
  assert (Hdecomp : l = sublist 0 1 l ++ sublist 1 n l).
  {
    rewrite <- (sublist_split 0 n 1 l) by lia.
    symmetry.
    apply sublist_self.
    lia.
  }
  rewrite Hdecomp at 1.
  replace (sublist 0 1 l) with (Znth 0 l d :: nil).
  2:{
    replace (sublist 0 1 l) with (sublist 0 (0 + 1) l) by reflexivity.
    symmetry.
    apply sublist_single.
    exact Hzero.
  }
  simpl.
  replace (Znth 0 l d) with p.
  - reflexivity.
  - symmetry.
    apply point_eq_by_xy; assumption.
Qed.

Lemma point_cross_same_right : forall a b,
  point_cross a b b = 0.
Proof.
  intros.
  unfold point_cross.
  rewrite cross_prod_self.
  reflexivity.
Qed.

Module StorePointAsElement <: ELEMENT_STORE.
  Definition A := Point.

  Definition storeA (base : addr) (lo : Z) (a : Point) : Assertion :=
    store_point (base + lo * sizeof_Point) a.

  Definition undefstoreA (base : addr) (lo : Z) : Assertion :=
    undef_point (base + lo * sizeof_Point).

  Definition sizeA := sizeof_Point.

  Lemma store_point_to_align : forall p pt,
    store_point p pt |-- store_align_n sizeA.
  Proof.
    intros.
    unfold store_point, sizeA.
    sep_apply (store_int_align4
      (&((p) # "Point" ->ₛ "x")) (point_x pt)).
    sep_apply (store_int_align4
      (&((p) # "Point" ->ₛ "y")) (point_y pt)).
    sep_apply (store_align4_merge 1 1).
    replace (1 + 1) with 2 by lia.
    sep_apply (store_align4_to_store_align 2).
    rewrite sizeof_Point_eq.
    replace (4 * 2) with 8 by lia.
    reflexivity.
  Qed.

  Lemma undef_point_to_align : forall p,
    undef_point p |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undef_point, sizeA.
    sep_apply (undef_store_int_align4
      (&((p) # "Point" ->ₛ "x"))).
    sep_apply (undef_store_int_align4
      (&((p) # "Point" ->ₛ "y"))).
    sep_apply (store_align4_merge 1 1).
    replace (1 + 1) with 2 by lia.
    sep_apply (store_align4_to_store_align 2).
    rewrite sizeof_Point_eq.
    replace (4 * 2) with 8 by lia.
    reflexivity.
  Qed.

  Lemma store_to_undefstore : forall base lo a,
    storeA base lo a |-- undefstoreA base lo.
  Proof.
    intros.
    apply store_point_to_undef_point.
  Qed.

  Lemma storeA_shift : forall base n lo a,
    storeA (base + n * sizeA) lo a --||-- storeA base (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (base + n * sizeof_Point + lo * sizeof_Point)
      with (base + (lo + n) * sizeof_Point) by lia.
    split; apply derivable1_refl.
  Qed.

  Lemma undefstoreA_shift : forall base n lo,
    undefstoreA (base + n * sizeA) lo --||-- undefstoreA base (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (base + n * sizeof_Point + lo * sizeof_Point)
      with (base + (lo + n) * sizeof_Point) by lia.
    split; apply derivable1_refl.
  Qed.

  Lemma store_to_align : forall base lo a, storeA base lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    apply store_point_to_align.
  Qed.

  Lemma undefstore_to_align : forall base lo, undefstoreA base lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    apply undef_point_to_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    rewrite sizeof_Point_eq.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.
End StorePointAsElement.

Module PointArray := ArrayLib (StorePointAsElement).

Lemma point_array_store_missing_merge_to_full : forall base i n l d,
  0 <= i < n ->
  store_point (base + i * sizeof("Point")) (Znth i l d) **
  PointArray.missing_i base i 0 n l |--
  PointArray.full base n l.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono.
    + unfold StorePointAsElement.storeA.
      apply derivable1_refl.
    + apply derivable1_refl.
  - eapply derivable1_trans.
    + apply (PointArray.missing_i_merge_to_full base i n (Znth i l d) l); lia.
    + rewrite replace_Znth_Znth.
      apply derivable1_refl.
Qed.

Lemma point_array_seg_snoc_store : forall base lo hi l a,
  lo <= hi ->
  PointArray.seg base lo hi l **
  store_point (base + hi * sizeof("Point")) a |--
  PointArray.seg base lo (hi + 1) (l ++ a :: nil).
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono.
    + apply derivable1_refl.
    + unfold StorePointAsElement.storeA.
      apply derivable1_refl.
  - eapply derivable1_trans.
    + apply derivable1_sepcon_mono.
      * apply derivable1_refl.
      * apply PointArray.seg_single.
    + apply (PointArray.seg_merge_to_seg base lo hi (hi + 1) l (a :: nil)); lia.
Qed.

Lemma point_array_store_undef_tail_to_undef_seg : forall base lo hi a,
  lo < hi ->
  store_point (base + lo * sizeof("Point")) a **
  PointArray.undef_seg base (lo + 1) hi |--
  PointArray.undef_seg base lo hi.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono.
    + apply store_point_to_undef_point.
    + apply derivable1_refl.
  - eapply derivable1_trans.
    + apply derivable1_sepcon_mono.
      * unfold StorePointAsElement.undefstoreA.
        apply derivable1_refl.
      * apply derivable1_refl.
    + eapply derivable1_trans.
      * apply derivable1_sepcon_mono.
        -- apply PointArray.undef_seg_single.
        -- apply derivable1_refl.
	      * apply (PointArray.undef_seg_merge_to_undef_seg base lo (lo + 1) hi); lia.
Qed.

Lemma point_array_seg_snoc_store_undef :
  forall (base : addr) (hi bound : Z) (l : list Point) (a : Point),
  0 <= hi ->
  hi + 1 <= bound ->
  store_point (base + hi * sizeof("Point")) a **
  (PointArray.undef_seg base (hi + 1) bound **
   PointArray.seg base 0 hi l) |--
  PointArray.seg base 0 (hi + 1) (l ++ a :: nil) **
  PointArray.undef_seg base (hi + 1) bound.
Proof.
  intros.
  sep_apply (point_array_seg_snoc_store base 0 hi l a); try lia.
  entailer!.
Qed.

Lemma point_array_seg_pop_tail : forall base top hi prefix last,
  top = Zlength prefix ->
  top + 1 <= hi ->
  PointArray.seg base 0 (top + 1) (prefix ++ last :: nil) **
  PointArray.undef_seg base (top + 1) hi |--
  PointArray.seg base 0 top prefix **
  PointArray.undef_seg base top hi.
Proof.
  intros.
  sep_apply (PointArray.seg_split_to_seg base 0 top (top + 1)
               (prefix ++ last :: nil));
    try (pose proof (Zlength_nonneg prefix); lia).
  replace (sublist 0 (top - 0) (prefix ++ last :: nil)) with prefix by
    (replace (top - 0) with (Zlength prefix) by lia;
     rewrite sublist_app_exact1; reflexivity).
  sep_apply (PointArray.seg_to_undef_seg base top (top + 1)
               (sublist (top - 0) (top + 1 - 0) (prefix ++ last :: nil))).
  sep_apply (PointArray.undef_seg_merge_to_undef_seg base top (top + 1) hi);
    try lia.
  entailer!.
Qed.

Lemma point_array_cons_full : forall base n p tail,
  1 <= n ->
  store_point base p **
  PointArray.full (base + sizeof("Point")) (n - 1) tail |--
  PointArray.full base n (p :: tail).
Proof.
  intros base n p tail Hn.
  replace base with (base + 0 * sizeof("Point")) at 1 by lia.
  change (store_point (base + 0 * sizeof("Point")) p)
    with (StorePointAsElement.storeA base 0 p).
  sep_apply (PointArray.seg_single base 0 p).
  sep_apply (PointArray.seg_to_full base 0 1 (p :: nil)).
  replace (base + 0 * sizeof("Point")) with base by lia.
  replace (1 - 0) with 1 by lia.
  replace (base + sizeof("Point")) with (base + 1 * sizeof("Point")) by lia.
  sep_apply (PointArray.full_merge_to_full base 1 n (p :: nil) tail).
  - simpl. apply derivable1_refl.
  - lia.
Qed.

Lemma points_in_bound_Znth : forall l i d,
  points_in_bound l ->
  0 <= i < Zlength l ->
  point_in_bound (Znth i l d).
Proof.
  unfold points_in_bound.
  intros l i d Hbound Hi.
  apply Forall_forall with (x := Znth i l d) in Hbound.
  - exact Hbound.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma points_in_bound_snoc_Znth : forall prefix l i d,
  points_in_bound prefix ->
  points_in_bound l ->
  0 <= i < Zlength l ->
  points_in_bound (prefix ++ Znth i l d :: nil).
Proof.
  unfold points_in_bound.
  intros prefix l i d Hprefix Hl Hi.
  apply Forall_app.
  split; [exact Hprefix |].
  constructor.
  - eapply points_in_bound_Znth; eauto.
  - constructor.
Qed.

Lemma point_in_bound_point_mk_fields : forall p,
  point_in_bound p ->
  point_in_bound (point_mk (point_x p) (point_y p)).
Proof.
  intros [px py] H.
  exact H.
Qed.

Lemma points_in_bound_Znth_point_mk : forall l i d,
  points_in_bound l ->
  0 <= i < Zlength l ->
  point_in_bound (point_mk (point_x (Znth i l d)) (point_y (Znth i l d))).
Proof.
  intros.
  apply point_in_bound_point_mk_fields.
  eapply points_in_bound_Znth; eauto.
Qed.

Lemma points_in_bound_sublist : forall l lo hi,
  points_in_bound l ->
  0 <= lo <= hi ->
  hi <= Zlength l ->
  points_in_bound (sublist lo hi l).
Proof.
  intros l lo hi Hbound Hlohi Hhi.
  unfold points_in_bound in *.
  apply Forall_Znth_intro with (d := default_point).
  intros i Hi.
  rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia.
  eapply points_in_bound_Znth; eauto.
  lia.
Qed.

Lemma point_sorted_range_sublist_point_polar_sorted : forall gp l lo hi tail,
  tail = sublist lo hi l ->
  0 <= lo <= hi ->
  hi <= Zlength l ->
  point_sorted_range gp l lo (hi - 1) ->
  point_polar_sorted gp tail.
Proof.
  intros gp l lo hi tail Htail Hlohi Hhi Hsorted.
  subst tail.
  unfold point_polar_sorted.
  intros i j d Hij Hj.
  rewrite Zlength_sublist in Hj by lia.
  rewrite !Znth_sublist by lia.
  rewrite (Znth_indep l (i + lo) d default_point) by lia.
  rewrite (Znth_indep l (j + lo) d default_point) by lia.
  unfold point_sorted_range in Hsorted.
  apply Hsorted; lia.
Qed.

Lemma point_sorted_range_tail_point_polar_sorted : forall gp l n tail,
  tail = sublist 1 n l ->
  Zlength l = n ->
  2 <= n ->
  point_sorted_range gp l 1 (n - 1) ->
  point_polar_sorted gp tail.
Proof.
  intros gp l n tail Htail Hlen Hn Hsorted.
  eapply point_sorted_range_sublist_point_polar_sorted; eauto; lia.
Qed.

Lemma Forall_replace_Znth_preserve : forall {A : Type} (P : A -> Prop) l i v,
  Forall P l ->
  P v ->
  Forall P (replace_Znth i v l).
Proof.
  intros A P l i v Hforall Hv.
  unfold replace_Znth.
  remember (Z.to_nat i) as n eqn:Hn.
  clear i Hn.
  revert n.
  induction Hforall as [| a l Ha Htail IH]; intros n; simpl.
  - constructor.
  - destruct n; simpl.
    + constructor; auto.
    + constructor; auto.
Qed.

Lemma Zlength_point_swap : forall l i j,
  Zlength (point_swap l i j) = Zlength l.
Proof.
  intros.
  unfold point_swap.
  repeat rewrite Zlength_replace_Znth.
  reflexivity.
Qed.

Lemma points_in_bound_point_swap : forall l i j,
  points_in_bound l ->
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  points_in_bound (point_swap l i j).
Proof.
  unfold points_in_bound, point_swap.
  intros l i j Hbound Hi Hj.
  apply Forall_replace_Znth_preserve.
  - apply Forall_replace_Znth_preserve.
    + exact Hbound.
    + eapply points_in_bound_Znth; eauto.
  - eapply points_in_bound_Znth; eauto.
Qed.

Lemma point_swap_Znth_left : forall l j,
  0 <= j < Zlength l ->
  Znth 0 (point_swap l 0 j) default_point = Znth j l default_point.
Proof.
  intros l j Hj.
  assert (H0 : 0 <= 0 < Zlength l) by lia.
  unfold point_swap.
  destruct (Z.eq_dec j 0) as [-> | Hj0].
  - assert (Hlen_inner :
        Zlength (replace_Znth 0 (Znth 0 l default_point) l) = Zlength l).
    { rewrite Zlength_replace_Znth; reflexivity. }
    rewrite Znth_replace_Znth_Same by (rewrite Hlen_inner; lia).
    reflexivity.
  - assert (Hlen_inner :
        Zlength (replace_Znth 0 (Znth j l default_point) l) = Zlength l).
    { rewrite Zlength_replace_Znth; reflexivity. }
    rewrite Znth_replace_Znth_Diff.
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
    + rewrite Hlen_inner; lia.
    + rewrite Hlen_inner; lia.
    + lia.
Qed.

Lemma point_swap_Znth_right : forall l j,
  0 <= j < Zlength l ->
  Znth j (point_swap l 0 j) default_point = Znth 0 l default_point.
Proof.
  intros l j Hj.
  unfold point_swap.
  assert (Hlen_inner :
      Zlength (replace_Znth 0 (Znth j l default_point) l) = Zlength l).
  { rewrite Zlength_replace_Znth; reflexivity. }
  rewrite Znth_replace_Znth_Same by (rewrite Hlen_inner; lia).
  reflexivity.
Qed.

Lemma point_swap_Znth_other : forall l j k,
  0 <= j < Zlength l ->
  0 <= k < Zlength l ->
  k <> 0 ->
  k <> j ->
  Znth k (point_swap l 0 j) default_point = Znth k l default_point.
Proof.
  intros l j k Hj Hk Hk0 Hkj.
  unfold point_swap.
  assert (Hlen_inner :
      Zlength (replace_Znth 0 (Znth j l default_point) l) = Zlength l).
  { rewrite Zlength_replace_Znth; reflexivity. }
  rewrite Znth_replace_Znth_Diff.
  rewrite Znth_replace_Znth_Diff by lia.
  reflexivity.
  - rewrite Hlen_inner; lia.
  - rewrite Hlen_inner; lia.
  - lia.
Qed.

Lemma point_leftmost_prefix_leftmost_point_swap : forall l pivot_idx n,
  Zlength l = n ->
  point_leftmost_prefix l pivot_idx n ->
  leftmost (Znth 0 (point_swap l 0 pivot_idx) default_point)
           (point_swap l 0 pivot_idx).
Proof.
  intros l pivot_idx n Hlen Hprefix.
  unfold point_leftmost_prefix in Hprefix.
  destruct Hprefix as [Hidx [Hin Hmin]].
  assert (Hpivot : 0 <= pivot_idx < Zlength l) by lia.
  rewrite point_swap_Znth_left by exact Hpivot.
  unfold leftmost.
  apply Forall_Znth_intro with (d := default_point).
  intros k Hk.
  rewrite Zlength_point_swap in Hk.
  destruct (Z.eq_dec k 0) as [-> | Hk0].
  - rewrite point_swap_Znth_left by exact Hpivot.
    unfold point_leftdown, x, y in Hmin.
    specialize (Hmin pivot_idx).
    apply Hmin.
    lia.
  - destruct (Z.eq_dec k pivot_idx) as [-> | Hkp].
    + rewrite point_swap_Znth_right by exact Hpivot.
      specialize (Hmin 0).
      unfold point_leftdown, x, y in Hmin.
      apply Hmin.
      lia.
    + rewrite point_swap_Znth_other by (try exact Hpivot; try exact Hk; lia).
      specialize (Hmin k).
      unfold point_leftdown, x, y in Hmin.
      apply Hmin.
      lia.
Qed.

Lemma point_leftmost_prefix_sorted_tail_leftmost : forall l pivot_idx n pts_pivot pts_sorted tail_sorted pivot0,
  Zlength l = n ->
  point_leftmost_prefix l pivot_idx n ->
  pts_pivot = point_swap l 0 pivot_idx ->
  pivot0 = Znth 0 pts_pivot default_point ->
  Zlength pts_sorted = n ->
  tail_sorted = sublist 1 n pts_sorted ->
  point_permutation pts_pivot pts_sorted ->
  leftmost pivot0 (rev tail_sorted).
Proof.
  intros l pivot_idx n pts_pivot pts_sorted tail_sorted pivot0
         Hlen Hprefix Hpivot_list Hpivot0 Hsorted_len Htail Hperm.
  subst pts_pivot pivot0 tail_sorted.
  assert (Hn_pos : 1 <= n).
  { unfold point_leftmost_prefix in Hprefix; lia. }
  apply leftmost_rev.
  apply leftmost_sublist.
  - lia.
  - lia.
  - eapply leftmost_permutation.
    + exact Hperm.
    + eapply point_leftmost_prefix_leftmost_point_swap; eauto.
Qed.

Lemma point_cmp_polar_refl : forall gp a,
  point_cmp_polar gp a a = 0.
Proof.
  intros gp a.
  unfold point_cmp_polar.
  rewrite point_cross_same_right.
  destruct (Z_gt_dec 0 0); [lia |].
  destruct (Z_lt_dec 0 0); [lia |].
  unfold point_at_mid, point_dot, dot_prod, build_vec, x, y.
  simpl.
  replace ((point_x a - point_x a) * (point_x gp - point_x a) +
           (point_y a - point_y a) * (point_y gp - point_y a)) with 0.
  2: lia.
  destruct (Z_gt_dec 0 0); [lia |].
  destruct (Z_lt_dec 0 0); [lia |].
  apply point_cmp_xy_eq; reflexivity.
Qed.

Lemma point_cmp_xy_gt_flip : forall a b,
  point_cmp_xy a b > 0 ->
  point_cmp_xy b a < 0.
Proof.
  intros a b Hcmp.
  unfold point_cmp_xy, x, y in *.
  repeat
    match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b)
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b)
    end;
    lia.
Qed.

Lemma Znth_In_range : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma point_cross_swap : forall gp a b,
  point_cross gp b a = - point_cross gp a b.
Proof.
  intros gp a b.
  unfold point_cross, cross_prod, build_vec, x, y.
  simpl.
  ring.
Qed.

Lemma point_cmp_polar_mid_pos_flip_under_leftdown : forall gp a b,
  point_leftdown gp a ->
  point_leftdown gp b ->
  point_cross gp a b = 0 ->
  point_at_mid gp a b > 0 ->
  point_cmp_polar gp b a < 0.
Proof.
  intros [gx gy] [ax ay] [bx by0] Hga Hgb Hcr Hmid.
  unfold point_cmp_polar, point_leftdown, point_cross, point_at_mid,
    point_dot, cross_prod, dot_prod, build_vec, point_cmp_xy, x, y in *.
  simpl in *.
  destruct Hga as [Hgax | [Hgax Hgay]];
  destruct Hgb as [Hgbx | [Hgbx Hgby]].
  - repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end;
      try lia.
    all:
      assert (Hid :
        (ax - gx) * ((ax - bx) * (gx - bx) + (ay - by0) * (gy - by0)) +
        (bx - gx) * ((bx - ax) * (gx - ax) + (by0 - ay) * (gy - ay)) = 0);
      [ transitivity ((by0 - ay) *
          ((ax - gx) * (by0 - gy) - (bx - gx) * (ay - gy)));
        [ ring | rewrite Hcr; ring ]
      | nia ].
  - subst bx.
    assert (by0 = gy) by nia.
    subst by0.
    repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end;
      nia.
  - subst ax.
    assert (ay = gy) by nia.
    subst ay.
    nia.
  - subst ax bx.
    repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end;
      try lia.
    all:
      try solve [
        assert (gy < ay) by
          (destruct (Z_lt_ge_dec gy ay);
           [ lia | assert (gy = ay) by lia; subst; nia ]);
        try assert (gy < by0) by
          (destruct (Z_lt_ge_dec gy by0);
           [ lia | assert (gy = by0) by lia; subst; nia ]);
        nia ].
Qed.

Lemma point_cmp_polar_mid_zero_xy_gt_flip_under_leftdown : forall gp a b,
  point_leftdown gp a ->
  point_leftdown gp b ->
  point_cross gp a b = 0 ->
  point_at_mid gp a b = 0 ->
  point_cmp_xy a b > 0 ->
  point_cmp_polar gp b a < 0.
Proof.
  intros [gx gy] [ax ay] [bx by0] Hga Hgb Hcr Hmid Hxy.
  unfold point_cmp_polar, point_leftdown, point_cross, point_at_mid,
    point_dot, cross_prod, dot_prod, build_vec, point_cmp_xy, x, y in *.
  simpl in *.
  destruct Hga as [Hgax | [Hgax Hgay]];
  destruct Hgb as [Hgbx | [Hgbx Hgby]].
  - repeat
      match goal with
      | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b)
      | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b)
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end;
      try lia.
    all:
      assert (Hid :
        (ax - gx) * ((ax - bx) * (gx - bx) + (ay - by0) * (gy - by0)) +
        (bx - gx) * ((bx - ax) * (gx - ax) + (by0 - ay) * (gy - ay)) = 0);
      [ transitivity ((by0 - ay) *
          ((ax - gx) * (by0 - gy) - (bx - gx) * (ay - gy)));
        [ ring | rewrite Hcr; ring ]
      | nia ].
  - subst bx.
    assert (by0 = gy) by nia.
    subst by0.
    repeat
      match goal with
      | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b)
      | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b)
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end;
      nia.
  - subst ax.
    assert (ay = gy) by nia.
    subst ay.
    repeat
      match goal with
      | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b)
      | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b)
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end;
      nia.
  - subst ax bx.
    repeat
      match goal with
      | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b)
      | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b)
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end;
      try lia.
    all:
      try solve [
        assert (gy < ay) by
          (destruct (Z_lt_ge_dec gy ay);
           [ lia | assert (gy = ay) by lia; subst; nia ]);
        nia ].
Qed.

Lemma point_cmp_polar_gt_flip_under_leftdown : forall gp a b,
  point_leftdown gp a ->
  point_leftdown gp b ->
  point_cmp_polar gp a b > 0 ->
  point_cmp_polar gp b a < 0.
Proof.
  intros gp a b Hga Hgb Hcmp.
  unfold point_cmp_polar in Hcmp.
  destruct (Z_gt_dec (point_cross gp a b) 0) as [Hcr_pos | Hcr_not_pos].
  - lia.
  - destruct (Z_lt_dec (point_cross gp a b) 0) as [Hcr_neg | Hcr_not_neg].
    + unfold point_cmp_polar.
      rewrite point_cross_swap.
      destruct (Z_gt_dec (- point_cross gp a b) 0); lia.
    + assert (Hcr_zero : point_cross gp a b = 0) by lia.
      destruct (Z_gt_dec (point_at_mid gp a b) 0) as [Hmid_pos | Hmid_not_pos].
      * eapply point_cmp_polar_mid_pos_flip_under_leftdown; eauto.
      * destruct (Z_lt_dec (point_at_mid gp a b) 0) as [Hmid_neg | Hmid_not_neg].
        -- lia.
        -- assert (Hmid_zero : point_at_mid gp a b = 0) by lia.
           eapply point_cmp_polar_mid_zero_xy_gt_flip_under_leftdown; eauto.
Qed.

Lemma point_cmp_polar_gt_flip_under_leftmost : forall gp l a b,
  leftmost gp l ->
  In a l ->
  In b l ->
  point_cmp_polar gp a b > 0 ->
  point_cmp_polar gp b a < 0.
Proof.
  intros gp l a b Hleft Ha Hb Hcmp.
  unfold leftmost in Hleft.
  rewrite Forall_forall in Hleft.
  eapply point_cmp_polar_gt_flip_under_leftdown.
  - unfold point_leftdown.
    apply Hleft.
    exact Ha.
  - unfold point_leftdown.
    apply Hleft.
    exact Hb.
  - exact Hcmp.
Qed.

Lemma Forall_permutation_point :
  forall (P : Point -> Prop) l l1,
    point_permutation l l1 ->
    Forall P l ->
    Forall P l1.
Proof.
  intros P l l1 Hperm Hforall.
  unfold point_permutation in Hperm.
  rewrite Forall_forall in *.
  intros x Hin.
  apply Hforall.
  eapply Permutation_in.
  - apply Permutation_sym. exact Hperm.
  - exact Hin.
Qed.

Lemma Forall_Znth_point :
  forall (P : Point -> Prop) l i,
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l default_point).
Proof.
  intros P l i Hforall Hrange.
  rewrite Forall_forall in Hforall.
  apply Hforall.
  apply Znth_In_range.
  exact Hrange.
Qed.

Lemma sublist_eq_from_Znth_point :
  forall l1 l2 lo hi,
    Zlength l1 = Zlength l2 ->
    0 <= lo <= hi ->
    hi <= Zlength l1 ->
    (forall k, lo <= k < hi ->
       Znth k l1 default_point = Znth k l2 default_point) ->
    sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros l1 l2 lo hi Hlen Hlohi Hhi Hpoint.
  apply (proj2 (list_eq_ext (sublist lo hi l1)
                            (sublist lo hi l2) default_point)).
  split.
  - rewrite Zlength_sublist by lia.
    rewrite Zlength_sublist by (rewrite <- Hlen; lia).
    lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    { rewrite Zlength_sublist in Hi by lia. exact Hi. }
    rewrite (@Znth_sublist_lt Point default_point lo hi l1 i) by lia.
    rewrite (@Znth_sublist_lt Point default_point lo hi l2 i)
      by (try rewrite <- Hlen; lia).
    apply Hpoint.
    lia.
Qed.

Lemma list_decompose_sublist_point :
  forall (l : list Point) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    l = sublist 0 lo l ++ sublist lo hi l ++ sublist hi (Zlength l) l.
Proof.
  intros l lo hi Hlohi Hhi.
  rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
  rewrite (sublist_split 0 (Zlength l) lo l) by lia.
  rewrite (sublist_split lo (Zlength l) hi l) by lia.
  reflexivity.
Qed.

Lemma point_same_outside_range_refl :
  forall l left right,
    point_same_outside_range l l left right.
Proof.
  intros l left right.
  split.
  - reflexivity.
  - intros; reflexivity.
Qed.

Lemma point_same_outside_range_trans :
  forall l l1 l2 left right,
    point_same_outside_range l l1 left right ->
    point_same_outside_range l1 l2 left right ->
    point_same_outside_range l l2 left right.
Proof.
  intros l l1 l2 left right [Hlen1 Heq1] [Hlen2 Heq2].
  split.
  - rewrite Hlen1. exact Hlen2.
  - intros k Hk Hout.
    assert (Hk1 : 0 <= k < Zlength l1) by (rewrite <- Hlen1; exact Hk).
    rewrite (Heq2 k Hk1 Hout).
    apply Heq1; assumption.
Qed.

Lemma point_same_outside_range_weaken :
  forall l l1 left1 right1 left2 right2,
    left2 <= left1 ->
    right1 <= right2 ->
    point_same_outside_range l l1 left1 right1 ->
    point_same_outside_range l l1 left2 right2.
Proof.
  intros l l1 left1 right1 left2 right2 Hleft Hright [Hlen Heq].
  split.
  - exact Hlen.
  - intros k Hk Hout.
    apply Heq; try assumption.
    destruct Hout as [Hout | Hout].
    + left. lia.
    + right. lia.
Qed.

Lemma point_same_outside_range_prefix :
  forall l l1 left right,
    point_same_outside_range l l1 left right ->
    0 <= left <= Zlength l ->
    sublist 0 left l1 = sublist 0 left l.
Proof.
  intros l l1 left right [Hlen Heq] Hrange.
  apply sublist_eq_from_Znth_point.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + lia.
    + left. lia.
Qed.

Lemma point_same_outside_range_suffix :
  forall l l1 left right,
    point_same_outside_range l l1 left right ->
    0 <= right + 1 <= Zlength l ->
    sublist (right + 1) (Zlength l1) l1 =
    sublist (right + 1) (Zlength l) l.
Proof.
  intros l l1 left right [Hlen Heq] Hrange.
  rewrite <- Hlen.
  apply sublist_eq_from_Znth_point.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + rewrite Hlen. lia.
    + right. lia.
Qed.

Lemma point_permutation_middle_of_same_outside :
  forall l l1 left right,
    point_permutation l l1 ->
    point_same_outside_range l l1 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength l ->
    point_permutation (sublist left (right + 1) l)
                     (sublist left (right + 1) l1).
Proof.
  intros l l1 left right Hperm Hsame Hlr Hright.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen _].
  pose proof (point_same_outside_range_prefix _ _ _ _ Hsame0 ltac:(lia))
    as Hpre.
  pose proof (point_same_outside_range_suffix _ _ _ _ Hsame0 ltac:(lia))
    as Hsuf.
  rewrite (list_decompose_sublist_point l left (right + 1)) in Hperm
    by lia.
  assert (Hright1 : right + 1 <= Zlength l1) by (rewrite <- Hlen; lia).
  rewrite (list_decompose_sublist_point l1 left (right + 1)) in Hperm
    by lia.
  rewrite Hpre, Hsuf in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.

Lemma Forall_sublist_by_Znth_point :
  forall (P : Point -> Prop) l lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> P (Znth k l default_point)) ->
    Forall P (sublist lo hi l).
Proof.
  intros P l lo hi Hlohi Hhi Hpoint.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert lo hi Hlohi Hhi Hpoint Hn.
  induction n; intros lo hi Hlohi Hhi Hpoint Hn.
  - assert (hi = lo) by lia.
    subst hi.
    rewrite (@Zsublist_nil Point l lo lo) by lia.
    constructor.
  - assert (lo < hi) by lia.
    rewrite (sublist_split lo hi (lo + 1) l) by lia.
    rewrite (@sublist_single Point default_point lo l) by lia.
    constructor.
    + simpl. apply Hpoint. lia.
    + apply IHn with (lo := lo + 1) (hi := hi).
      * lia.
      * exact Hhi.
      * intros k Hk. apply Hpoint. lia.
      * assert (Z.to_nat (hi - (lo + 1)) = n) as Hn' by lia.
        symmetry. exact Hn'.
Qed.

Lemma Forall_sublist_lookup_point :
  forall (P : Point -> Prop) l lo hi k,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    Forall P (sublist lo hi l) ->
    lo <= k < hi ->
    P (Znth k l default_point).
Proof.
  intros P l lo hi k Hlohi Hhi Hforall Hk.
  pose proof (Forall_Znth_point P (sublist lo hi l) (k - lo) Hforall)
    as Hz.
  assert (Hrange : 0 <= k - lo < Zlength (sublist lo hi l)).
  { rewrite Zlength_sublist by lia. lia. }
  specialize (Hz Hrange).
  rewrite (@Znth_sublist_lt Point default_point lo hi l (k - lo)) in Hz
    by lia.
  replace (lo + (k - lo)) with k in Hz by lia.
  exact Hz.
Qed.

Lemma point_polar_partitioned_at_preserved_by_left :
  forall gp l l1 left right p,
    point_permutation l l1 ->
    0 <= left ->
    point_same_outside_range l l1 left (p - 1) ->
    right < Zlength l ->
    point_polar_partitioned_at gp l left right p ->
    point_polar_partitioned_at gp l1 left right p.
Proof.
  intros gp l l1 left right p Hperm Hleft0 Hsame Hrightlen Hpart.
  destruct Hsame as [Hlen Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 default_point = Znth p l default_point).
  {
    apply Heq.
    - lia.
    - right. lia.
  }
  split; [lia|].
  split.
  - rewrite Hpiv.
    eapply (Forall_permutation_point
              (fun x => point_cmp_polar gp x (Znth p l default_point) <= 0)
              (sublist left p l)
              (sublist left p l1)).
    + assert (Hmid :
          point_permutation (sublist left (p - 1 + 1) l)
                           (sublist left (p - 1 + 1) l1)).
      {
        eapply point_permutation_middle_of_same_outside
          with (left := left) (right := p - 1).
        - exact Hperm.
        - exact (conj Hlen Heq).
        - lia.
        - lia.
      }
      replace (p - 1 + 1) with p in Hmid by lia.
      exact Hmid.
    + exact Hleft.
  - rewrite Hpiv.
    apply Forall_sublist_by_Znth_point; try lia.
    intros k Hk.
    rewrite Heq by (try lia; right; lia).
    eapply (Forall_sublist_lookup_point
              (fun x => point_cmp_polar gp (Znth p l default_point) x < 0)
              l (p + 1) (right + 1) k); try eassumption; lia.
Qed.

Lemma point_polar_partitioned_at_preserved_by_right :
  forall gp l l1 left right p,
    point_permutation l l1 ->
    0 <= left ->
    point_same_outside_range l l1 (p + 1) right ->
    right < Zlength l ->
    point_polar_partitioned_at gp l left right p ->
    point_polar_partitioned_at gp l1 left right p.
Proof.
  intros gp l l1 left right p Hperm Hleft0 Hsame Hrightlen Hpart.
  destruct Hsame as [Hlen Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 default_point = Znth p l default_point).
  {
    apply Heq.
    - lia.
    - left. lia.
  }
  split; [lia|].
  split.
  - rewrite Hpiv.
    assert (Hsub : sublist left p l1 = sublist left p l).
    {
      apply sublist_eq_from_Znth_point.
      - symmetry. exact Hlen.
      - lia.
      - lia.
      - intros k Hk.
        apply Heq.
        + lia.
        + left. lia.
    }
    rewrite Hsub.
    exact Hleft.
  - rewrite Hpiv.
    eapply (Forall_permutation_point
              (fun x => point_cmp_polar gp (Znth p l default_point) x < 0)
              (sublist (p + 1) (right + 1) l)
              (sublist (p + 1) (right + 1) l1)).
    + eapply point_permutation_middle_of_same_outside
        with (left := p + 1) (right := right).
      * exact Hperm.
      * exact (conj Hlen Heq).
      * lia.
      * lia.
    + exact Hright.
Qed.

Lemma point_cmp_polar_lt_le : forall gp a b,
  point_cmp_polar gp a b < 0 ->
  point_cmp_polar gp a b <= 0.
Proof.
  intros; lia.
Qed.

Lemma point_sorted_range_degenerate :
  forall gp l left right,
    left >= right ->
    point_sorted_range gp l left right.
Proof.
  intros gp l left right Hge i j Hi Hij Hj.
  assert (i = j) by lia.
  subst j.
  rewrite point_cmp_polar_refl.
  lia.
Qed.

Lemma point_sorted_range_from_left_boundary :
  forall gp l left right p,
    0 <= left ->
    p >= right ->
    right < Zlength l ->
    point_polar_partitioned_at gp l left right p ->
    point_sorted_range gp l left (p - 1) ->
    point_sorted_range gp l left right.
Proof.
  intros gp l left right p Hleft0 Hp Hrightlen Hpart Hsorted.
  intros i j Hi Hij Hj.
  destruct Hpart as [Hbounds [Hleftpart _]].
  assert (p = right) by lia.
  subst p.
  destruct (Z.eq_dec j right) as [-> | Hjneq].
  - destruct (Z.eq_dec i right) as [-> | Hineq].
    + rewrite point_cmp_polar_refl. lia.
    + eapply Forall_sublist_lookup_point
        with (lo := left) (hi := right); try eassumption; lia.
  - apply Hsorted; lia.
Qed.

Lemma point_sorted_range_from_right_boundary :
  forall gp l left right p,
    0 <= left ->
    p <= left ->
    right < Zlength l ->
    point_polar_partitioned_at gp l left right p ->
    point_sorted_range gp l (p + 1) right ->
    point_sorted_range gp l left right.
Proof.
  intros gp l left right p Hleft0 Hp Hrightlen Hpart Hsorted.
  intros i j Hi Hij Hj.
  destruct Hpart as [Hbounds [_ Hrightpart]].
  assert (p = left) by lia.
  subst p.
  destruct (Z.eq_dec i left) as [-> | Hineq].
  - destruct (Z.eq_dec j left) as [-> | Hjneq].
    + rewrite point_cmp_polar_refl. lia.
    + apply point_cmp_polar_lt_le.
      eapply (Forall_sublist_lookup_point
                (fun x => point_cmp_polar gp (Znth left l default_point) x < 0)
                l (left + 1) (right + 1) j); try eassumption; lia.
  - apply Hsorted; lia.
Qed.

Lemma point_sorted_range_ext :
  forall gp l l1 left right,
    0 <= left ->
    right < Zlength l ->
    Zlength l = Zlength l1 ->
    (forall k, left <= k <= right ->
       Znth k l1 default_point = Znth k l default_point) ->
    point_sorted_range gp l left right ->
    point_sorted_range gp l1 left right.
Proof.
  intros gp l l1 left right Hleft0 Hrightlen Hlen Heq Hsorted i j Hi Hij Hj.
  rewrite (Heq i) by lia.
  rewrite (Heq j) by lia.
  apply Hsorted; lia.
Qed.

Lemma point_cmp_xy_le_colinear_mid_leftdown :
  forall gp a b,
    point_leftdown gp a ->
    point_leftdown gp b ->
    point_cross gp a b = 0 ->
    point_at_mid gp a b = 0 ->
    point_cmp_xy a b <= 0.
Proof.
  intros gp a b Ha Hb Hcross Hmid.
  unfold point_leftdown in *.
  unfold point_cmp_xy.
  unfold point_cross, point_at_mid, point_dot, cross_prod, dot_prod,
    build_vec, x, y in *.
  simpl in *.
  destruct Ha as [Ha | [Ha_x Ha_y]];
  destruct Hb as [Hb | [Hb_x Hb_y]];
  repeat match goal with
  | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); simpl in H
  | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); simpl in H
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); simpl
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); simpl
  end; try nia.
  - assert (Hid :
      (a.(x) - gp.(x)) *
        ((b.(x) - a.(x)) * (gp.(x) - a.(x)) +
         (b.(y) - a.(y)) * (gp.(y) - a.(y))) =
      ((a.(x) - gp.(x)) - (b.(x) - gp.(x))) *
        ((a.(x) - gp.(x)) * (a.(x) - gp.(x)) +
         (a.(y) - gp.(y)) * (a.(y) - gp.(y))) -
      (a.(y) - gp.(y)) *
        ((a.(x) - gp.(x)) * (b.(y) - gp.(y)) -
         (b.(x) - gp.(x)) * (a.(y) - gp.(y)))) by ring.
    rewrite Hmid in Hid.
    rewrite Hcross in Hid.
    pose proof (Z.square_nonneg (a.(x) - gp.(x))).
    pose proof (Z.square_nonneg (a.(y) - gp.(y))).
    nia.
  - assert (Hid :
      (a.(y) - gp.(y)) *
        ((b.(x) - a.(x)) * (gp.(x) - a.(x)) +
         (b.(y) - a.(y)) * (gp.(y) - a.(y))) =
      ((a.(y) - gp.(y)) - (b.(y) - gp.(y))) *
        ((a.(x) - gp.(x)) * (a.(x) - gp.(x)) +
         (a.(y) - gp.(y)) * (a.(y) - gp.(y))) +
      (a.(x) - gp.(x)) *
        ((a.(x) - gp.(x)) * (b.(y) - gp.(y)) -
         (b.(x) - gp.(x)) * (a.(y) - gp.(y)))) by ring.
    rewrite Hmid in Hid.
    rewrite Hcross in Hid.
    pose proof (Z.square_nonneg (a.(x) - gp.(x))).
    pose proof (Z.square_nonneg (a.(y) - gp.(y))).
    nia.
  - assert (b.(y) = gp.(y)) by nia.
    pose proof (Z.square_nonneg (a.(x) - gp.(x))).
    pose proof (Z.square_nonneg (a.(y) - gp.(y))).
    nia.
Qed.

Lemma point_weak_polar_le_point_cmp_polar_le_under_leftdown :
  forall gp a b,
    point_leftdown gp a ->
    point_leftdown gp b ->
    point_weak_polar_le gp a b ->
    point_cmp_polar gp a b <= 0.
Proof.
  intros gp a b Ha Hb Hab.
  unfold point_weak_polar_le, point_weak_rev_ccw in Hab.
  destruct Hab as [Hccw | [Hcol Hmid]].
  - unfold point_cmp_polar.
    unfold ccw, left_than, point_cross, cross_prod, build_vec,
      point_at_mid, point_dot, point_cmp_xy, x, y in *.
    simpl in *.
    repeat match goal with
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); simpl in H
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); simpl in H
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); simpl
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); simpl
    end; nia.
  - assert (Hcross : point_cross gp a b = 0).
    {
      unfold point_colinear, point_cross in Hcol.
      unfold point_cross.
      rewrite cross_prod_comm.
      lia.
    }
    assert (Hmid_le : point_at_mid gp a b <= 0).
    {
      unfold at_mid, backward_or_perp in Hmid.
      unfold dot_prod, build_vec in Hmid.
      unfold point_at_mid, point_dot, dot_prod, build_vec, x, y.
      simpl in *.
      lia.
    }
    unfold point_cmp_polar.
    rewrite Hcross.
    destruct (Z_gt_dec 0 0); [lia |].
    destruct (Z_lt_dec 0 0); [lia |].
    destruct (Z_gt_dec (point_at_mid gp a b) 0); [lia |].
    destruct (Z_lt_dec (point_at_mid gp a b) 0); [lia |].
    apply (point_cmp_xy_le_colinear_mid_leftdown gp); try assumption.
    lia.
Qed.

Lemma point_weak_polar_le_trans_under_leftdown :
  forall gp a b c,
    point_leftdown gp a ->
    point_leftdown gp b ->
    point_leftdown gp c ->
    point_weak_polar_le gp a b ->
    point_weak_polar_le gp b c ->
    point_weak_polar_le gp a c.
Proof.
  intros gp a b c Ha Hb Hc Hab Hbc.
  unfold point_leftdown in *.
  unfold point_weak_polar_le, point_weak_rev_ccw in *.
  destruct Hab as [Hab_ccw | [Hab_col Hab_mid]];
  destruct Hbc as [Hbc_ccw | [Hbc_col Hbc_mid]].
  - repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [? | [? ?]]
    | H : _ /\ _ |- _ => destruct H as [? ?]
    end;
    try solve
      [ left;
        set (s := {| point_x := gp.(x); point_y := gp.(y) - 1 |});
        assert (Hsa : ccw gp s a)
          by (subst s; unfold ccw, left_than, cross_prod, build_vec; simpl; nia);
        assert (Hsb : ccw gp s b)
          by (subst s; unfold ccw, left_than, cross_prod, build_vec; simpl; nia);
        assert (Hsc : ccw gp s c)
          by (subst s; unfold ccw, left_than, cross_prod, build_vec; simpl; nia);
        assert (Hgab : ccw gp a b) by (apply ccw_cyclicity; exact Hab_ccw);
        assert (Hgbc : ccw gp b c) by (apply ccw_cyclicity; exact Hbc_ccw);
        apply ccw_cyclicity_2;
        eapply (ccw_transitivity a b c s gp);
        eauto
      | unfold point_colinear, point_cross, at_mid, point_dot,
          ccw, left_than, colinear, parallel, backward_or_perp,
          build_vec, cross_prod, dot_prod, x, y in *;
        simpl in *; left; nia
      | unfold point_colinear, point_cross, at_mid, point_dot,
          ccw, left_than, colinear, parallel, backward_or_perp,
          build_vec, cross_prod, dot_prod, x, y in *;
        simpl in *; right; split; nia
      | unfold point_colinear, point_cross, at_mid, point_dot,
          ccw, left_than, colinear, parallel, backward_or_perp,
          build_vec, cross_prod, dot_prod, x, y in *;
        simpl in *; assert (a.(y) = gp.(y)) by nia; left; nia
      | unfold point_colinear, point_cross, at_mid, point_dot,
          ccw, left_than, colinear, parallel, backward_or_perp,
          build_vec, cross_prod, dot_prod, x, y in *;
        simpl in *; assert (b.(y) = gp.(y)) by nia; left; nia
      | unfold point_colinear, point_cross, at_mid, point_dot,
          ccw, left_than, colinear, parallel, backward_or_perp,
          build_vec, cross_prod, dot_prod, x, y in *;
        simpl in *; assert (c.(y) = gp.(y)) by nia; left; nia
      | unfold point_colinear, point_cross, at_mid, point_dot,
          ccw, left_than, colinear, parallel, backward_or_perp,
          build_vec, cross_prod, dot_prod, x, y in *;
        simpl in *; exfalso; nia ].
  - unfold point_colinear, point_cross, at_mid, point_dot,
      ccw, left_than, colinear, parallel, backward_or_perp,
      build_vec, cross_prod, dot_prod, x, y in *;
    simpl in *;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [? | [? ?]]
    | H : _ /\ _ |- _ => destruct H as [? ?]
    end;
    try solve
      [ left; nia
      | right; split; nia
      | assert (a.(y) = gp.(y)) by nia; right; split; nia
      | assert (b.(y) = gp.(y)) by nia; right; split; nia
      | assert (c.(y) = gp.(y)) by nia; right; split; nia
      | assert (a.(y) = gp.(y)) by nia; left; nia
      | assert (b.(y) = gp.(y)) by nia; left; nia
      | assert (c.(y) = gp.(y)) by nia; left; nia
      | assert (gp.(y) < b.(y)) by nia;
        assert (b.(y) <= c.(y)) by nia;
        left; nia
      | assert (c.(y) = gp.(y)) by nia;
        assert ((gp.(x) - b.(x)) * (gp.(x) - b.(x)) > 0) by nia;
        pose proof (Z.square_nonneg (gp.(y) - b.(y)));
        exfalso; nia
      | exfalso; nia ].
  - unfold point_colinear, point_cross, at_mid, point_dot,
      ccw, left_than, colinear, parallel, backward_or_perp,
      build_vec, cross_prod, dot_prod, x, y in *;
    simpl in *;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [? | [? ?]]
    | H : _ /\ _ |- _ => destruct H as [? ?]
    end;
    try solve
      [ left; nia
      | right; split; nia
      | assert (a.(y) = gp.(y)) by nia; right; split; nia
      | assert (b.(y) = gp.(y)) by nia; right; split; nia
      | assert (c.(y) = gp.(y)) by nia; right; split; nia
      | assert (a.(y) = gp.(y)) by nia; left; nia
      | assert (b.(y) = gp.(y)) by nia; left; nia
      | assert (c.(y) = gp.(y)) by nia; left; nia
      | assert (gp.(y) < b.(y)) by nia;
        assert (b.(y) <= a.(y)) by nia;
        left; nia
      | assert (a.(y) = gp.(y)) by nia;
        assert ((gp.(x) - b.(x)) * (gp.(x) - b.(x)) > 0) by nia;
        pose proof (Z.square_nonneg (gp.(y) - b.(y)));
        exfalso; nia
      | exfalso; nia ].
  - right.
    assert (Hbca_col : colinear b c gp).
    { apply colinear_perm321.
      apply point_colinear_colinear. exact Hbc_col. }
    assert (Habg_col : colinear a b gp).
    { apply colinear_perm321.
      apply point_colinear_colinear. exact Hab_col. }
    pose proof (segment_mid_trans_right a b c gp
                  Hbca_col Hbc_mid Habg_col Hab_mid)
      as [Hacg_col Hacg_mid].
    split.
    + apply point_colinear_colinear.
      apply colinear_perm321. exact Hacg_col.
    + exact Hacg_mid.
Qed.

Lemma point_cmp_polar_le_lt_trans_under_leftdown :
  forall gp a b c,
    point_leftdown gp a ->
    point_leftdown gp b ->
    point_leftdown gp c ->
    point_cmp_polar gp a b <= 0 ->
    point_cmp_polar gp b c < 0 ->
    point_cmp_polar gp a c <= 0.
Proof.
  intros gp a b c Ha Hb Hc Hab Hbc.
  apply (point_weak_polar_le_point_cmp_polar_le_under_leftdown gp a c);
    try assumption.
  eapply (point_weak_polar_le_trans_under_leftdown gp a b c);
    try eassumption.
  - apply point_cmp_polar_le_point_weak_polar_le.
    exact Hab.
  - apply point_cmp_polar_le_point_weak_polar_le.
    lia.
Qed.

Lemma point_cmp_polar_le_lt_trans_under_leftmost :
  forall gp l a b c,
    leftmost gp l ->
    In a l ->
    In b l ->
    In c l ->
    point_cmp_polar gp a b <= 0 ->
    point_cmp_polar gp b c < 0 ->
    point_cmp_polar gp a c <= 0.
Proof.
  intros gp l a b c Hleft Ha Hb Hc Hab Hbc.
  eapply point_cmp_polar_le_lt_trans_under_leftdown; try eassumption.
  - unfold leftmost in Hleft.
    rewrite Forall_forall in Hleft.
    unfold point_leftdown.
    apply Hleft; exact Ha.
  - unfold leftmost in Hleft.
    rewrite Forall_forall in Hleft.
    unfold point_leftdown.
    apply Hleft; exact Hb.
  - unfold leftmost in Hleft.
    rewrite Forall_forall in Hleft.
    unfold point_leftdown.
    apply Hleft; exact Hc.
Qed.

Lemma point_sorted_range_partition_merge :
  forall gp l left right p,
    0 <= left ->
    right < Zlength l ->
    left <= p <= right ->
    leftmost gp l ->
    point_polar_partitioned_at gp l left right p ->
    point_sorted_range gp l left (p - 1) ->
    point_sorted_range gp l (p + 1) right ->
    point_sorted_range gp l left right.
Proof.
  intros gp l left right p Hleft0 Hrightlen Hp_range Hleftmost Hpart
    Hsorted_left Hsorted_right.
  intros i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j p) as [Hj_left | Hj_not_left].
  - apply Hsorted_left; lia.
  - destruct (Z_le_gt_dec i p) as [Hi_not_right | Hi_right].
    + destruct Hpart as [_ [Hleftpart Hrightpart]].
      destruct (Z.eq_dec i p) as [-> | Hi_neq].
      * destruct (Z.eq_dec j p) as [-> | Hj_neq].
        -- rewrite point_cmp_polar_refl. lia.
        -- apply point_cmp_polar_lt_le.
           eapply (Forall_sublist_lookup_point
                     (fun x => point_cmp_polar gp (Znth p l default_point) x < 0)
                     l (p + 1) (right + 1) j);
             try eassumption; lia.
      * assert (Hip :
          point_cmp_polar gp (Znth i l default_point)
            (Znth p l default_point) <= 0).
        {
          eapply (Forall_sublist_lookup_point
                    (fun x => point_cmp_polar gp x
                       (Znth p l default_point) <= 0)
                    l left p i);
            try eassumption; lia.
        }
        destruct (Z.eq_dec j p) as [-> | Hj_neq].
        -- exact Hip.
        -- assert (Hpj :
             point_cmp_polar gp (Znth p l default_point)
               (Znth j l default_point) < 0).
           {
             eapply (Forall_sublist_lookup_point
                       (fun x =>
                          point_cmp_polar gp (Znth p l default_point) x < 0)
                       l (p + 1) (right + 1) j);
               try eassumption; lia.
           }
           eapply point_cmp_polar_le_lt_trans_under_leftmost
             with (l := l) (b := Znth p l default_point);
             try eassumption.
           ++ apply Znth_In_range. lia.
           ++ apply Znth_In_range. lia.
           ++ apply Znth_In_range. lia.
    + apply Hsorted_right; lia.
Qed.

Lemma point_polar_cmp_safe_range_point_swap :
  forall gp l lo hi i j,
    point_polar_cmp_safe_range gp l lo hi ->
    0 <= lo ->
    lo <= i <= hi ->
    lo <= j <= hi ->
    hi < Zlength l ->
    point_polar_cmp_safe_range gp (point_swap l i j) lo hi.
Proof.
  intros gp l lo hi i j Hrange Hlo Hi Hj Hhi.
  unfold point_polar_cmp_safe_range in *.
  assert (Hlookup : forall k,
    lo <= k <= hi ->
    exists k',
      lo <= k' <= hi /\
      Znth k (point_swap l i j) default_point = Znth k' l default_point).
  {
    intros k Hk.
    destruct (Z.eq_dec k i) as [Hki | Hki].
    - subst k.
      exists j. split; [lia |].
      apply point_swap_Znth_left_index; lia.
    - destruct (Z.eq_dec k j) as [Hkj | Hkj].
      + subst k.
        exists i. split; [lia |].
        apply point_swap_Znth_right_index; lia.
      + exists k. split; [lia |].
        apply point_swap_Znth_other_index; lia.
  }
  intros p q Hp Hq.
  destruct (Hlookup p Hp) as [p' [Hp' Hp_eq]].
  destruct (Hlookup q Hq) as [q' [Hq' Hq_eq]].
  rewrite Hp_eq, Hq_eq.
  apply Hrange; assumption.
Qed.

Lemma point_polar_cmp_safe_range_subrange_permutation :
  forall gp l l1 lo hi sublo subhi,
    point_polar_cmp_safe_range gp l lo hi ->
    point_permutation l l1 ->
    point_same_outside_range l l1 sublo subhi ->
    lo <= sublo ->
    subhi <= hi ->
    0 <= lo ->
    0 <= sublo <= subhi + 1 ->
    hi < Zlength l ->
    point_polar_cmp_safe_range gp l1 lo hi.
Proof.
  intros gp l l1 lo hi sublo subhi Hrange Hperm Hsame
    Hlo_sub Hsub_hi Hlo0 Hsub_bounds Hhi_len.
  destruct Hsame as [Hlen Hsame_eq].
  unfold point_polar_cmp_safe_range in *.
  assert (Hlookup : forall k,
    lo <= k <= hi ->
    exists k',
      lo <= k' <= hi /\
      Znth k l1 default_point = Znth k' l default_point).
  {
    intros k Hk.
    assert (Hk_l : 0 <= k < Zlength l) by lia.
    assert (Hk_l1 : 0 <= k < Zlength l1) by (rewrite <- Hlen; lia).
    destruct (Z_lt_ge_dec k sublo) as [Hleft | Hge].
    - exists k. split; [lia |].
      apply Hsame_eq; [assumption | left; lia].
    - destruct (Z_le_gt_dec k subhi) as [Hinside | Hright].
      + assert (Hmidperm :
          point_permutation (sublist sublo (subhi + 1) l)
                            (sublist sublo (subhi + 1) l1)).
        {
          eapply point_permutation_middle_of_same_outside.
          - exact Hperm.
          - split; [exact Hlen | exact Hsame_eq].
          - exact Hsub_bounds.
          - lia.
        }
        assert (Hsubidx :
          0 <= k - sublo < Zlength (sublist sublo (subhi + 1) l1)).
        {
          rewrite Zlength_sublist by (rewrite <- Hlen; lia).
          lia.
        }
        pose proof (Znth_In_range
          (sublist sublo (subhi + 1) l1) (k - sublo)
          default_point Hsubidx) as Hin_l1.
        rewrite Znth_sublist in Hin_l1 by lia.
        replace (k - sublo + sublo) with k in Hin_l1 by lia.
        assert (Hin_l :
          In (Znth k l1 default_point)
             (sublist sublo (subhi + 1) l)).
        {
          eapply Permutation_in.
          - apply Permutation_sym. exact Hmidperm.
          - exact Hin_l1.
        }
        destruct (In_Znth_Zlength
          (sublist sublo (subhi + 1) l)
          (Znth k l1 default_point) default_point Hin_l)
          as [off [Hoff Hoff_eq]].
        assert (Hoff_bound : 0 <= off < subhi + 1 - sublo).
        {
          rewrite Zlength_sublist in Hoff by lia.
          exact Hoff.
        }
        exists (sublo + off). split.
        * lia.
        * rewrite <- Hoff_eq.
          rewrite Znth_sublist by lia.
          replace (off + sublo) with (sublo + off) by lia.
          reflexivity.
      + exists k. split; [lia |].
        apply Hsame_eq; [assumption | right; lia].
  }
  intros i j Hi Hj.
  destruct (Hlookup i Hi) as [i' [Hi' Hi_eq]].
  destruct (Hlookup j Hj) as [j' [Hj' Hj_eq]].
  rewrite Hi_eq, Hj_eq.
  apply Hrange; assumption.
Qed.

Lemma point_dedup_inner_scan_inv_no_duplicate :
  forall l unique_n read scan duplicate,
    point_dedup_inner_scan_inv l unique_n read scan duplicate ->
    duplicate = 0 ->
    forall k,
      0 <= k < scan ->
      ~ point_same (Znth k l default_point) (Znth read l default_point).
Proof.
  intros l unique_n read scan duplicate Hinner Hdup k Hk.
  unfold point_dedup_inner_scan_inv in Hinner.
  destruct Hinner as [[_ Hnone] | [Hnz _]].
  - apply Hnone. exact Hk.
  - lia.
Qed.

Lemma point_no_dup_prefix_extend_from_inner :
  forall before cur read unique_n pivot_idx scan duplicate,
    point_dedup_scan_inv before cur read unique_n pivot_idx ->
    point_dedup_inner_scan_inv cur unique_n read scan duplicate ->
    read = unique_n ->
    read < Zlength cur ->
    scan >= unique_n ->
    duplicate = 0 ->
    point_no_dup_prefix cur (unique_n + 1).
Proof.
  intros before cur read unique_n pivot_idx scan duplicate
    Hscan Hinner Hread Hread_lt Hscan_ge Hdup.
  subst read.
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [Hlen [Huniq_read [Hread_len
    [Hperm [Hnodup [Hrepr Hpiv]]]]]].
  unfold point_no_dup_prefix in *.
  destruct Hnodup as [Hprefix_bounds Hnodup].
  split; [lia |].
  intros i j Hij Hj.
  destruct (Z_lt_ge_dec j unique_n) as [Hj_old | Hj_new].
  - apply Hnodup; lia.
  - assert (j = unique_n) by lia.
    subst j.
    apply (point_dedup_inner_scan_inv_no_duplicate
      cur unique_n unique_n scan duplicate Hinner Hdup i); lia.
Qed.

Lemma point_no_dup_prefix_point_swap_extend_from_inner :
  forall before cur read unique_n pivot_idx scan duplicate,
    point_dedup_scan_inv before cur read unique_n pivot_idx ->
    point_dedup_inner_scan_inv cur unique_n read scan duplicate ->
    read <> unique_n ->
    read < Zlength cur ->
    scan >= unique_n ->
    duplicate = 0 ->
    point_no_dup_prefix (point_swap cur unique_n read) (unique_n + 1).
Proof.
  intros before cur read unique_n pivot_idx scan duplicate
    Hscan Hinner Hread_ne Hread_lt Hscan_ge Hdup.
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [Hlen [Huniq_read [Hread_len
    [Hperm [Hnodup [Hrepr Hpiv]]]]]].
  unfold point_no_dup_prefix in *.
  destruct Hnodup as [Hprefix_bounds Hnodup].
  assert (Huniq_range : 0 <= unique_n < Zlength cur) by lia.
  assert (Hread_range : 0 <= read < Zlength cur) by lia.
  split; [rewrite Zlength_point_swap; lia |].
  intros i j Hij Hj Hsame.
  assert (Hi_range : 0 <= i < Zlength cur) by lia.
  assert (Hj_range : 0 <= j < Zlength cur) by lia.
  destruct (Z.eq_dec j unique_n) as [Hj_unique | Hj_not_unique].
  - subst j.
    rewrite point_swap_Znth_left_index in Hsame by lia.
    destruct (Z.eq_dec i read) as [Hi_read | Hi_not_read].
    + subst i; lia.
    + rewrite point_swap_Znth_other_index in Hsame by lia.
      eapply point_dedup_inner_scan_inv_no_duplicate; eauto; lia.
  - assert (j < unique_n) by lia.
    rewrite point_swap_Znth_other_index in Hsame by lia.
    destruct (Z.eq_dec i read) as [Hi_read | Hi_not_read].
    + subst i; lia.
    + rewrite point_swap_Znth_other_index in Hsame by lia.
      exact ((Hnodup i j ltac:(lia) ltac:(lia)) Hsame).
Qed.

Lemma point_dedup_accept_transition_scan_inv :
  forall before cur read unique_n pivot_idx,
    Zlength before = Zlength cur ->
    read < Zlength cur ->
    point_permutation before cur ->
    point_no_dup_prefix cur (unique_n + 1) ->
    point_prefix_represents_range cur (unique_n + 1) (unique_n + 1) (read + 1) ->
    point_leftmost_prefix cur pivot_idx (unique_n + 1) ->
    point_dedup_scan_inv before cur (read + 1) (unique_n + 1) pivot_idx.
Proof.
  intros before cur read unique_n pivot_idx Hlen Hread_lt Hperm Hnodup
    Hrepr Hleft.
  unfold point_dedup_scan_inv.
  unfold point_prefix_represents_range in Hrepr.
  destruct Hrepr as [Huniq_bounds [Hrange_bounds Hrepr]].
  split; [exact Hlen |].
  split; [lia |].
  split; [lia |].
  split; [exact Hperm |].
  split; [exact Hnodup |].
  split.
  - unfold point_prefix_represents_range.
    repeat split; try lia.
    exact Hrepr.
  - right. exact Hleft.
Qed.

Lemma point_dedup_duplicate_advance_scan_inv :
  forall before cur read unique_n pivot_idx scan duplicate,
    point_dedup_scan_inv before cur read unique_n pivot_idx ->
    point_dedup_inner_scan_inv cur unique_n read scan duplicate ->
    0 <= scan < unique_n ->
    point_same (Znth scan cur default_point) (Znth read cur default_point) ->
    read < Zlength cur ->
    point_dedup_scan_inv before cur (read + 1) unique_n pivot_idx.
Proof.
  intros before cur read unique_n pivot_idx scan duplicate Hscan Hinner
    Hscan_bounds Hsame Hread_lt.
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [Hlen [Huniq_read [Hread_len
    [Hperm [Hnodup [Hrepr Hpiv]]]]]].
  unfold point_prefix_represents_range in Hrepr.
  destruct Hrepr as [Huniq_lo [Hlo_hi Hrepr]].
  unfold point_dedup_scan_inv.
  split; [exact Hlen |].
  split; [lia |].
  split; [lia |].
  split; [exact Hperm |].
  split; [exact Hnodup |].
  split.
  - unfold point_prefix_represents_range.
    repeat split; try lia.
    intros k Hk.
    destruct (Z.eq_dec k read) as [-> | Hkread].
    + exists scan.
      split; [lia | exact Hsame].
    + apply Hrepr.
      lia.
  - exact Hpiv.
Qed.

Lemma point_dedup_duplicate_seen_advance_scan_inv :
  forall before cur read unique_n pivot_idx scan duplicate,
    point_dedup_scan_inv before cur read unique_n pivot_idx ->
    point_dedup_inner_scan_inv cur unique_n read scan duplicate ->
    duplicate <> 0 ->
    read < Zlength cur ->
    point_dedup_scan_inv before cur (read + 1) unique_n pivot_idx.
Proof.
  intros before cur read unique_n pivot_idx scan duplicate Hscan Hinner
    Hdup Hread_lt.
  unfold point_dedup_inner_scan_inv in Hinner.
  destruct Hinner as [[Hzero _] | [_ Hsame_prefix]]; [lia |].
  unfold point_prefix_has_same in Hsame_prefix.
  destruct Hsame_prefix as [_ [_ [j [Hj Hsame]]]].
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [Hlen [Huniq_read [Hread_len
    [Hperm [Hnodup [Hrepr Hpiv]]]]]].
  unfold point_prefix_represents_range in Hrepr.
  destruct Hrepr as [Huniq_lo [Hlo_hi Hrepr]].
  unfold point_dedup_scan_inv.
  split; [exact Hlen |].
  split; [lia |].
  split; [lia |].
  split; [exact Hperm |].
  split; [exact Hnodup |].
  split.
  - unfold point_prefix_represents_range.
    repeat split; try lia.
    intros k Hk.
    destruct (Z.eq_dec k read) as [-> | Hkread].
    + exists j. split; [lia | exact Hsame].
    + apply Hrepr. lia.
  - exact Hpiv.
Qed.

Lemma point_dedup_scan_inv_finish_result :
  forall before cur read unique_n pivot_idx,
    point_dedup_scan_inv before cur read unique_n pivot_idx ->
    1 <= Zlength cur ->
    read >= Zlength cur ->
    point_dedup_result before cur unique_n pivot_idx /\
    pivot_idx < unique_n /\
    1 <= unique_n.
Proof.
  intros before cur read unique_n pivot_idx Hscan Hlen_pos Hread_ge.
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [Hlen [Huniq_read [Hread_len
    [Hperm [Hnodup [Hrepr Hpiv]]]]]].
  assert (Hread_eq : read = Zlength cur) by lia.
  destruct Hpiv as [Hzero | Hleft].
  - subst unique_n.
    unfold point_prefix_represents_range in Hrepr.
    destruct Hrepr as [Huniq_lo [Hlo_hi Hrepr]].
    assert (Hbad : False).
    {
      assert (Hk : 0 <= 0 < read) by lia.
      specialize (Hrepr 0 Hk).
      destruct Hrepr as [j [Hj _]].
      lia.
    }
    contradiction.
  - pose proof Hleft as Hleft_whole.
    destruct Hleft as [Hpiv_bounds [Huniq_len Hleft_min]].
    assert (Hunique_all : point_unique_prefix_represents_all cur unique_n).
    {
      unfold point_unique_prefix_represents_all.
      split; [lia |].
      intros k Hk.
      destruct (Z_lt_ge_dec k unique_n) as [Hk_prefix | Hk_suffix].
      - exists k.
        split; [lia |].
        unfold point_same; split; reflexivity.
      - unfold point_prefix_represents_range in Hrepr.
        destruct Hrepr as [Huniq_lo [Hlo_hi Hrepr]].
        rewrite Hread_eq in Hrepr.
        apply Hrepr.
        lia.
    }
    subst read.
    split.
    + unfold point_dedup_result.
      split.
      * unfold point_dedup_scan_inv.
        split; [exact Hlen |].
        split; [lia |].
        split; [lia |].
        split; [exact Hperm |].
        split; [exact Hnodup |].
        split; [exact Hrepr |].
        right. exact Hleft_whole.
      * split; [lia |].
        split; [exact Hleft_whole | exact Hunique_all].
    + split; lia.
Qed.

Lemma point_prefix_represents_range_point_swap_accept :
  forall before cur read unique_n pivot_idx,
    point_dedup_scan_inv before cur read unique_n pivot_idx ->
    read <> unique_n ->
    read < Zlength cur ->
    point_prefix_represents_range
      (point_swap cur unique_n read)
      (unique_n + 1) (unique_n + 1) (read + 1).
Proof.
  intros before cur read unique_n pivot_idx Hscan Hneq Hread_lt.
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [Hlen [Huniq_read [Hread_len
    [Hperm [Hnodup [Hrepr Hpiv]]]]]].
  assert (Huniq_range : 0 <= unique_n < Zlength cur) by lia.
  assert (Hread_range : 0 <= read < Zlength cur) by lia.
  assert (Hlt : unique_n < read) by lia.
  unfold point_prefix_represents_range in *.
  destruct Hrepr as [Huniq_lo [Hlo_hi Hrepr]].
  repeat split; try rewrite Zlength_point_swap; try lia.
  intros k Hk.
  destruct (Z.eq_dec k read) as [-> | Hkread].
  - destruct (Hrepr unique_n ltac:(lia)) as [j [Hj Hsame]].
    exists j. split; [lia |].
    rewrite point_swap_Znth_other_index by lia.
    rewrite point_swap_Znth_right_index by lia.
    exact Hsame.
  - destruct (Hrepr k ltac:(lia)) as [j [Hj Hsame]].
    exists j. split; [lia |].
    rewrite point_swap_Znth_other_index by lia.
    rewrite point_swap_Znth_other_index by lia.
    exact Hsame.
Qed.

Lemma point_leftmost_prefix_point_swap_preserve_before :
  forall l pivot_idx n i j,
    point_leftmost_prefix l pivot_idx n ->
    n <= i ->
    n <= j ->
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    point_leftmost_prefix (point_swap l i j) pivot_idx n.
Proof.
  intros l pivot_idx n i j Hprefix Hni Hnj Hi Hj.
  unfold point_leftmost_prefix in *.
  destruct Hprefix as [Hidx [Hn Hmin]].
  split; [lia |].
  split; [rewrite Zlength_point_swap; lia |].
  intros k Hk.
  rewrite point_swap_Znth_other_index by lia.
  rewrite point_swap_Znth_other_index by lia.
  apply Hmin; lia.
Qed.

Definition points_not_all_same (l : list Point) : Prop :=
  exists i j,
    0 <= i < Zlength l /\
    0 <= j < Zlength l /\
    i <> j /\
    ~ point_same (Znth i l default_point) (Znth j l default_point).

Lemma point_same_sym : forall a b,
  point_same a b ->
  point_same b a.
Proof.
  unfold point_same.
  intros a b [Hx Hy].
  split; congruence.
Qed.

Lemma point_same_trans : forall a b c,
  point_same a b ->
  point_same b c ->
  point_same a c.
Proof.
  unfold point_same.
  intros a b c [Habx Haby] [Hbcx Hbcy].
  split; congruence.
Qed.

Lemma dedup_not_all_same_unique_n_ge_2 : forall base out n pivot,
  point_dedup_result base out n pivot ->
  points_not_all_same base ->
  2 <= n.
Proof.
  intros base out n pivot Hdedup Hnot_all.
  destruct Hdedup as [Hscan [Hn_bounds [_ Hrepr_all]]].
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [_ [_ [_ [Hperm _]]]].
  destruct Hnot_all as [i [j [Hi [Hj [_ Hdiff]]]]].
  destruct (Z_lt_ge_dec n 2) as [Hn_lt | Hn_ge]; [| lia].
  assert (Hn_eq : n = 1) by lia.
  subst n.
  assert (Hin_i_base : In (Znth i base default_point) base)
    by (apply Znth_In_range; lia).
  assert (Hin_j_base : In (Znth j base default_point) base)
    by (apply Znth_In_range; lia).
  assert (Hin_i_out : In (Znth i base default_point) out).
  {
    eapply Permutation_in.
    - exact Hperm.
    - exact Hin_i_base.
  }
  assert (Hin_j_out : In (Znth j base default_point) out).
  {
    eapply Permutation_in.
    - exact Hperm.
    - exact Hin_j_base.
  }
  destruct (In_Znth_Zlength out (Znth i base default_point) default_point
              Hin_i_out)
    as [oi [Hoi Hoi_eq]].
  destruct (In_Znth_Zlength out (Znth j base default_point) default_point
              Hin_j_out)
    as [oj [Hoj Hoj_eq]].
  unfold point_unique_prefix_represents_all in Hrepr_all.
  destruct Hrepr_all as [_ Hrepr_all].
  destruct (Hrepr_all oi Hoi) as [ri [Hri Hsame_i]].
  destruct (Hrepr_all oj Hoj) as [rj [Hrj Hsame_j]].
  assert (Hri0 : ri = 0) by lia.
  assert (Hrj0 : rj = 0) by lia.
  subst ri rj.
  rewrite Hoi_eq in Hsame_i.
  rewrite Hoj_eq in Hsame_j.
  exfalso.
  apply Hdiff.
  eapply point_same_trans.
  - apply point_same_sym.
    exact Hsame_i.
  - exact Hsame_j.
Qed.

(* Helper imports migrated from andrew_monotone_chain__vc_proving_r2_full_partial_merged_proof_manual.v. *)
Require Import Coq.Strings.Ascii.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
From SimpleC.SL Require Import Mem SeparationLogic.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.

(* Helper lemmas migrated from andrew_monotone_chain__vc_proving_r2_full_partial_merged_proof_manual.v. *)

Lemma point_mk_eta_worker : forall p : Point, point_mk p.(x) p.(y) = p.
Proof.
  intros p; destruct p as [px py]; reflexivity.
Qed.

Lemma point_cmp_leftdown_gt_flip_worker : forall a b : Point,
  point_cmp_leftdown a b > 0 -> point_cmp_leftdown b a < 0.
Proof.
  intros a b H.
  destruct a as [ax ay]; destruct b as [bx by_].
  unfold point_cmp_leftdown in *; simpl in *.
  repeat match goal with
  | |- context[Z_lt_dec ?x ?y] => destruct (Z_lt_dec x y)
  | |- context[Z_gt_dec ?x ?y] => destruct (Z_gt_dec x y)
  | H0 : context[Z_lt_dec ?x ?y] |- _ => destruct (Z_lt_dec x y)
  | H0 : context[Z_gt_dec ?x ?y] |- _ => destruct (Z_gt_dec x y)
  end; lia.
Qed.

Lemma point_xy_partition_scan_inv_init :
  forall (pts : list Point) (low high n : Z) (d : Point),
    0 <= low ->
    low <= high ->
    high < n ->
    Zlength pts = n ->
    point_xy_partition_scan_inv pts pts low high
      (point_mk (Znth high pts d).(x) (Znth high pts d).(y))
      (low - 1) low.
Proof.
  intros pts low high n d Hlow Hle Hhigh Hlen.
  unfold point_xy_partition_scan_inv.
  split; [apply Permutation_refl|].
  split; [apply point_same_outside_range_refl|].
  split.
  - rewrite (Znth_indep pts high default_point d) by lia.
    symmetry; apply point_mk_eta_worker.
  - split; intros k Hk; lia.
Qed.

Lemma point_xy_partition_scan_inv_accept_noswap :
  forall (before cur : list Point) (low high : Z) (pivot : Point)
    (i j retval : Z) (d : Point),
    i + 1 = j ->
    retval <= 0 ->
    retval =
      point_cmp_leftdown
        (point_mk (Znth j cur d).(x) (Znth j cur d).(y)) pivot ->
    0 <= j < Zlength cur ->
    point_xy_partition_scan_inv before cur low high pivot i j ->
    point_xy_partition_scan_inv before cur low high pivot (i + 1) (j + 1).
Proof.
  intros before cur low high pivot i j retval d Hij Hret Hcmp Hj Hinv.
  unfold point_xy_partition_scan_inv in *.
  destruct Hinv as [Hperm [Houtside [Hpivot [Hacc Hrej]]]].
  split; [exact Hperm|].
  split; [exact Houtside|].
  split; [exact Hpivot|].
  split.
  - intros k Hk.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + rewrite (Znth_indep cur j default_point d) by lia.
      rewrite (point_mk_eta_worker (Znth j cur d)) in Hcmp.
      rewrite <- Hcmp; lia.
    + apply Hacc; lia.
  - intros k Hk; lia.
Qed.

Lemma point_xy_partition_scan_inv_reject_step :
  forall (before cur : list Point) (low high : Z) (pivot : Point)
    (i j retval : Z) (d : Point),
    retval > 0 ->
    retval =
      point_cmp_leftdown
        (point_mk (Znth j cur d).(x) (Znth j cur d).(y)) pivot ->
    0 <= j < Zlength cur ->
    point_xy_partition_scan_inv before cur low high pivot i j ->
    point_xy_partition_scan_inv before cur low high pivot i (j + 1).
Proof.
  intros before cur low high pivot i j retval d Hret Hcmp Hj Hinv.
  unfold point_xy_partition_scan_inv in *.
  destruct Hinv as [Hperm [Houtside [Hpivot [Hacc Hrej]]]].
  split; [exact Hperm|].
  split; [exact Houtside|].
  split; [exact Hpivot|].
  split; [exact Hacc|].
  intros k Hk.
  destruct (Z.eq_dec k j) as [-> | Hneq].
  - rewrite (Znth_indep cur j default_point d) by lia.
    rewrite (point_mk_eta_worker (Znth j cur d)) in Hcmp.
    apply point_cmp_leftdown_gt_flip_worker.
    rewrite <- Hcmp; lia.
  - apply Hrej; lia.
Qed.

Lemma point_xy_partition_scan_inv_accept_swap :
  forall (before cur : list Point) (low high : Z) (pivot : Point)
    (i j retval : Z) (d : Point),
    i + 1 <> j ->
    retval <= 0 ->
    retval =
      point_cmp_leftdown
        (point_mk (Znth j cur d).(x) (Znth j cur d).(y)) pivot ->
    j < high ->
    high < Zlength cur ->
    0 <= low ->
    low - 1 <= i ->
    i < j ->
    j <= high ->
    point_xy_partition_scan_inv before cur low high pivot i j ->
    point_xy_partition_scan_inv before (point_swap cur (i + 1) j)
      low high pivot (i + 1) (j + 1).
Proof.
  intros before cur low high pivot i j retval d Hijneq Hret Hcmp
    Hjhigh Hhighlen Hlow Hlowi Hij Hjh Hinv.
  assert (Hijlt : i + 1 < j) by lia.
  assert (Hi1_range : 0 <= i + 1 < Zlength cur) by lia.
  assert (Hj_range : 0 <= j < Zlength cur) by lia.
  assert (Hhigh_range : 0 <= high < Zlength cur) by lia.
  assert (Hcmp_cur_j :
    point_cmp_leftdown (Znth j cur default_point) pivot <= 0).
  {
    rewrite (Znth_indep cur j default_point d) by lia.
    rewrite (point_mk_eta_worker (Znth j cur d)) in Hcmp.
    rewrite <- Hcmp; lia.
  }
  unfold point_xy_partition_scan_inv in *.
  destruct Hinv as [Hperm [Houtside [Hpivot [Hacc Hrej]]]].
  split.
  - eapply Permutation_trans; [exact Hperm|].
    apply point_swap_permutation; lia.
  - split.
    + apply point_same_outside_range_point_swap_inside; try exact Houtside; lia.
    + split.
      * rewrite point_swap_Znth_other_index by lia.
        exact Hpivot.
      * split.
        -- intros k Hk.
           destruct (Z.eq_dec k (i + 1)) as [-> | Hneq].
           ++ rewrite point_swap_Znth_left_index by lia.
              exact Hcmp_cur_j.
           ++ rewrite point_swap_Znth_other_index by lia.
              apply Hacc; lia.
        -- intros k Hk.
           destruct (Z.eq_dec k j) as [-> | Hneqj].
           ++ rewrite point_swap_Znth_right_index by lia.
              apply Hrej; lia.
           ++ rewrite point_swap_Znth_other_index by lia.
              apply Hrej; lia.
Qed.

Lemma worker_partition_finish_swap_partitioned :
  forall (before cur : list Point) (low high i j : Z) (pivot : Point),
    0 <= low ->
    low <= high ->
    high < Zlength cur ->
    low - 1 <= i ->
    i < j ->
    j <= high ->
    j >= high ->
    i + 1 <> high ->
    point_xy_partition_scan_inv before cur low high pivot i j ->
    point_xy_partitioned_at (point_swap cur (i + 1) high) low high (i + 1).
Proof.
  intros before cur low high i j pivot Hlow Hlow_high Hhigh_len Hlow_i
         Hi_j Hj_high Hhigh_j Hi1_neq Hinv.
  assert (Hj : j = high) by lia.
  subst j.
  destruct Hinv as [_ [_ [Hpivot [Hleft Hright]]]].
  assert (Hi1_range : 0 <= i + 1 < Zlength cur) by lia.
  assert (Hhigh_range : 0 <= high < Zlength cur) by lia.
  assert (Hi1_high : i + 1 < high) by lia.
  assert (Hpivot_swap :
            Znth (i + 1) (point_swap cur (i + 1) high) default_point = pivot).
  {
    rewrite point_swap_Znth_left_index by lia.
    exact Hpivot.
  }
  unfold point_xy_partitioned_at.
  split.
  - lia.
  - split.
    + eapply Forall_sublist_by_Znth_point.
      * lia.
      * rewrite Zlength_point_swap; lia.
      * intros k Hk.
        rewrite Hpivot_swap.
        rewrite point_swap_Znth_other_index by lia.
        apply Hleft; lia.
    + eapply Forall_sublist_by_Znth_point.
      * lia.
      * rewrite Zlength_point_swap; lia.
      * intros k Hk.
        rewrite Hpivot_swap.
        destruct (Z.eq_dec k high) as [-> | Hk_high].
        -- rewrite point_swap_Znth_right_index by lia.
           apply Hright; lia.
        -- rewrite point_swap_Znth_other_index by lia.
           apply Hright; lia.
Qed.

Lemma worker_partition_finish_noswap_partitioned :
  forall (before cur : list Point) (low high i j : Z) (pivot : Point),
    0 <= low ->
    low <= high ->
    high < Zlength cur ->
    low - 1 <= i ->
    i < j ->
    j <= high ->
    j >= high ->
    i + 1 = high ->
    point_xy_partition_scan_inv before cur low high pivot i j ->
    point_xy_partitioned_at cur low high (i + 1).
Proof.
  intros before cur low high i j pivot Hlow Hlow_high Hhigh_len Hlow_i
         Hi_j Hj_high Hhigh_j Hi1_eq Hinv.
  assert (Hj : j = high) by lia.
  subst j.
  destruct Hinv as [_ [_ [Hpivot [Hleft _]]]].
  assert (Hpivot_at : Znth (i + 1) cur default_point = pivot).
  {
    rewrite Hi1_eq.
    exact Hpivot.
  }
  unfold point_xy_partitioned_at.
  split.
  - lia.
  - split.
    + eapply Forall_sublist_by_Znth_point.
      * lia.
      * lia.
      * intros k Hk.
        rewrite Hpivot_at.
        apply Hleft; lia.
    + eapply Forall_sublist_by_Znth_point.
      * lia.
      * lia.
      * intros k Hk; lia.
Qed.

Lemma point_cmp_leftdown_le_point_leftdown : forall a b,
  point_cmp_leftdown a b <= 0 ->
  point_leftdown a b.
Proof.
  intros a b Hcmp.
  unfold point_cmp_leftdown, point_leftdown in *.
  destruct (Z_lt_dec (Point_Order.x a) (Point_Order.x b)); [left; lia |].
  destruct (Z_gt_dec (Point_Order.x a) (Point_Order.x b)); [lia |].
  destruct (Z_lt_dec (Point_Order.y a) (Point_Order.y b)); [right; lia |].
  destruct (Z_gt_dec (Point_Order.y a) (Point_Order.y b)); lia.
Qed.

Lemma point_leftdown_point_cmp_leftdown_le : forall a b,
  point_leftdown a b ->
  point_cmp_leftdown a b <= 0.
Proof.
  intros a b H.
  unfold point_cmp_leftdown, point_leftdown in *.
  destruct H as [H | [H H0]].
  - destruct (Z_lt_dec (Point_Order.x a) (Point_Order.x b)); lia.
  - destruct (Z_lt_dec (Point_Order.x a) (Point_Order.x b)); [lia |].
    destruct (Z_gt_dec (Point_Order.x a) (Point_Order.x b)); [lia |].
    destruct (Z_lt_dec (Point_Order.y a) (Point_Order.y b)); [lia |].
    destruct (Z_gt_dec (Point_Order.y a) (Point_Order.y b)); lia.
Qed.

Lemma point_cmp_leftdown_le_trans : forall a b c,
  point_cmp_leftdown a b <= 0 ->
  point_cmp_leftdown b c <= 0 ->
  point_cmp_leftdown a c <= 0.
Proof.
  intros a b c Hab Hbc.
  apply point_leftdown_point_cmp_leftdown_le.
  eapply point_leftdown_trans.
  - apply point_cmp_leftdown_le_point_leftdown; exact Hab.
  - apply point_cmp_leftdown_le_point_leftdown; exact Hbc.
Qed.

Lemma point_cmp_leftdown_le_lt_trans : forall a b c,
  point_cmp_leftdown a b <= 0 ->
  point_cmp_leftdown b c < 0 ->
  point_cmp_leftdown a c <= 0.
Proof.
  intros a b c Hab Hbc.
  apply point_leftdown_point_cmp_leftdown_le.
  eapply point_leftdown_trans.
  - apply point_cmp_leftdown_le_point_leftdown; exact Hab.
  - apply point_cmp_leftdown_lt_point_leftdown; exact Hbc.
Qed.

Lemma point_xy_sorted_range_degenerate :
  forall l left right,
    right <= left ->
    point_xy_sorted_range l left right.
Proof.
  intros l left right Hle i j Hi Hij Hj.
  assert (i = j) by lia.
  subst j.
  apply point_leftdown_point_cmp_leftdown_le.
  apply point_leftdown_refl.
Qed.

Lemma point_xy_sorted_range_from_left_boundary :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    left <= p <= right ->
    right <= p ->
    point_xy_partitioned_at l left right p ->
    point_xy_sorted_range l left (p - 1) ->
    point_xy_sorted_range l left right.
Proof.
  intros l left right p Hleft0 Hrightlen Hp_range Hrightp Hpart Hsorted.
  intros i j Hi Hij Hj.
  destruct Hpart as [_ [Hleftpart _]].
  destruct (Z_lt_ge_dec j p) as [Hjleft | Hjge].
  - apply Hsorted; lia.
  - assert (j = p) by lia.
    subst j.
    destruct (Z.eq_dec i p) as [-> | Hip].
    + apply point_leftdown_point_cmp_leftdown_le.
      apply point_leftdown_refl.
    + eapply (Forall_sublist_lookup_point
                (fun x => point_cmp_leftdown x (Znth p l default_point) <= 0)
                l left p i);
        try eassumption; lia.
Qed.

Lemma point_xy_sorted_range_from_right_boundary :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    left <= p <= right ->
    p <= left ->
    point_xy_partitioned_at l left right p ->
    point_xy_sorted_range l (p + 1) right ->
    point_xy_sorted_range l left right.
Proof.
  intros l left right p Hleft0 Hrightlen Hp_range Hpleft Hpart Hsorted.
  intros i j Hi Hij Hj.
  destruct Hpart as [_ [_ Hrightpart]].
  assert (p = left) by lia.
  subst p.
  destruct (Z.eq_dec i left) as [-> | Hileft].
  - destruct (Z.eq_dec j left) as [-> | Hjleft].
    + apply point_leftdown_point_cmp_leftdown_le.
      apply point_leftdown_refl.
    + apply Z.lt_le_incl.
      eapply (Forall_sublist_lookup_point
                (fun x => point_cmp_leftdown (Znth left l default_point) x < 0)
                l (left + 1) (right + 1) j);
        try eassumption; lia.
  - apply Hsorted; lia.
Qed.

Lemma point_xy_sorted_range_partition_merge :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    left <= p <= right ->
    point_xy_partitioned_at l left right p ->
    point_xy_sorted_range l left (p - 1) ->
    point_xy_sorted_range l (p + 1) right ->
    point_xy_sorted_range l left right.
Proof.
  intros l left right p Hleft0 Hrightlen Hp_range Hpart Hsorted_left Hsorted_right.
  intros i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j p) as [Hjleft | Hjnotleft].
  - apply Hsorted_left; lia.
  - destruct (Z_le_gt_dec i p) as [Hinotright | Hiright].
    + destruct Hpart as [_ [Hleftpart Hrightpart]].
      destruct (Z.eq_dec i p) as [-> | Hip].
      * destruct (Z.eq_dec j p) as [-> | Hjp].
        -- apply point_leftdown_point_cmp_leftdown_le.
           apply point_leftdown_refl.
        -- apply Z.lt_le_incl.
           eapply (Forall_sublist_lookup_point
                     (fun x => point_cmp_leftdown (Znth p l default_point) x < 0)
                     l (p + 1) (right + 1) j);
             try eassumption; lia.
      * assert (Hipcmp :
          point_cmp_leftdown (Znth i l default_point)
                             (Znth p l default_point) <= 0).
        {
          eapply (Forall_sublist_lookup_point
                    (fun x => point_cmp_leftdown x (Znth p l default_point) <= 0)
                    l left p i);
            try eassumption; lia.
        }
        destruct (Z.eq_dec j p) as [-> | Hjp].
        -- exact Hipcmp.
        -- assert (Hpjcmp :
             point_cmp_leftdown (Znth p l default_point)
                                (Znth j l default_point) < 0).
           {
             eapply (Forall_sublist_lookup_point
                       (fun x => point_cmp_leftdown (Znth p l default_point) x < 0)
                       l (p + 1) (right + 1) j);
               try eassumption; lia.
           }
           eapply point_cmp_leftdown_le_lt_trans; eassumption.
    + apply Hsorted_right; lia.
Qed.

Lemma Znth_In_sublist_point :
  forall l lo hi k,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    lo <= k < hi ->
    In (Znth k l default_point) (sublist lo hi l).
Proof.
  intros l lo hi k Hlohi Hhi Hk.
  pose proof (Znth_In_range (sublist lo hi l) (k - lo) default_point) as Hin.
  assert (Hrange : 0 <= k - lo < Zlength (sublist lo hi l)).
  {
    rewrite Zlength_sublist by lia.
    lia.
  }
  specialize (Hin Hrange).
  rewrite Znth_sublist in Hin by lia.
  replace (k - lo + lo) with k in Hin by lia.
  exact Hin.
Qed.

Lemma point_xy_sorted_range_partition_merge_after_subsorts :
  forall base mid out left right p,
    0 <= left ->
    right < Zlength base ->
    left <= p <= right ->
    point_xy_partitioned_at base left right p ->
    point_permutation base mid ->
    point_same_outside_range base mid left (p - 1) ->
    point_xy_sorted_range mid left (p - 1) ->
    point_permutation mid out ->
    point_same_outside_range mid out (p + 1) right ->
    point_xy_sorted_range out (p + 1) right ->
    point_xy_sorted_range out left right.
Proof.
  intros base mid out left right p Hleft0 Hrightlen Hp_range Hpart
    Hperm_left Hsame_left Hsorted_left Hperm_right Hsame_right Hsorted_right.
  destruct Hpart as [_ [Hpart_left Hpart_right]].
  pose proof Hsame_left as Hsame_left_full.
  pose proof Hsame_right as Hsame_right_full.
  destruct Hsame_left as [Hlen_mid Hsame_left].
  destruct Hsame_right as [Hlen_out Hsame_right].
  assert (Hrightlen_mid : right < Zlength mid) by (rewrite <- Hlen_mid; lia).
  assert (Hrightlen_out : right < Zlength out) by (rewrite <- Hlen_out; lia).
  assert (Hp_mid : Znth p mid default_point = Znth p base default_point).
  {
    apply Hsame_left; [lia | right; lia].
  }
  assert (Hp_out : Znth p out default_point = Znth p mid default_point).
  {
    apply Hsame_right; [lia | left; lia].
  }
  assert (Hleft_lookup : forall k,
    left <= k < p ->
    point_cmp_leftdown (Znth k out default_point)
                       (Znth p out default_point) <= 0).
  {
    intros k Hk.
    rewrite Hsame_right by (lia || left; lia).
    rewrite Hp_out, Hp_mid.
    rewrite Forall_forall in Hpart_left.
    apply Hpart_left.
    assert (Hmidperm :
      point_permutation (sublist left p base) (sublist left p mid)).
    {
      replace p with ((p - 1) + 1) by lia.
      eapply (point_permutation_middle_of_same_outside base mid left (p - 1));
        try eassumption; lia.
    }
    eapply Permutation_in.
    - apply Permutation_sym. exact Hmidperm.
    - apply Znth_In_sublist_point; try lia.
  }
  assert (Hright_lookup : forall k,
    p < k <= right ->
    point_cmp_leftdown (Znth p out default_point)
                       (Znth k out default_point) < 0).
  {
    intros k Hk.
    rewrite Hp_out, Hp_mid.
    rewrite Forall_forall in Hpart_right.
    apply Hpart_right.
    assert (Hrightperm :
      point_permutation (sublist (p + 1) (right + 1) mid)
                        (sublist (p + 1) (right + 1) out)).
    {
      eapply (point_permutation_middle_of_same_outside mid out (p + 1) right);
        try eassumption; lia.
    }
    assert (Hright_eq :
      sublist (p + 1) (right + 1) mid =
      sublist (p + 1) (right + 1) base).
    {
      apply sublist_eq_from_Znth_point.
      - symmetry. exact Hlen_mid.
      - lia.
      - rewrite <- Hlen_mid; lia.
      - intros t Ht.
        apply Hsame_left; [lia | right; lia].
    }
    assert (Hin_out :
      In (Znth k out default_point) (sublist (p + 1) (right + 1) out)).
    {
      apply Znth_In_sublist_point; try lia.
    }
    assert (Hin_mid :
      In (Znth k out default_point) (sublist (p + 1) (right + 1) mid)).
    {
      eapply Permutation_in.
      - apply Permutation_sym. exact Hrightperm.
      - exact Hin_out.
    }
    rewrite Hright_eq in Hin_mid.
    exact Hin_mid.
  }
  intros i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j p) as [Hjleft | Hjnotleft].
  - rewrite Hsame_right by (lia || left; lia).
    rewrite Hsame_right by (lia || left; lia).
    apply Hsorted_left; lia.
  - destruct (Z_le_gt_dec i p) as [Hinotright | Hiright].
    + destruct (Z.eq_dec i p) as [-> | Hip].
      * destruct (Z.eq_dec j p) as [-> | Hjp].
        -- apply point_leftdown_point_cmp_leftdown_le.
           apply point_leftdown_refl.
        -- apply Z.lt_le_incl.
           apply Hright_lookup; lia.
      * destruct (Z.eq_dec j p) as [-> | Hjp].
        -- apply Hleft_lookup; lia.
        -- eapply point_cmp_leftdown_le_lt_trans.
           ++ apply Hleft_lookup; lia.
           ++ apply Hright_lookup; lia.
    + apply Hsorted_right; lia.
Qed.

Lemma points_not_all_same_to_point_list_not_all_same :
  forall l, points_not_all_same l -> point_list_not_all_same l.
Proof.
  unfold points_not_all_same, point_list_not_all_same.
  intros l [i [j [Hi [Hj [_ Hneq]]]]].
  exists i, j. repeat split; try lia; auto.
Qed.

Lemma andrew_lower_scan_inv_nil :
  forall sorted,
    2 <= Zlength sorted ->
    points_in_bound sorted ->
    points_not_all_same sorted ->
    andrew_lower_scan_inv sorted nil 0 0.
Proof.
  intros sorted Hlen Hbound Hnas.
  unfold andrew_lower_scan_inv.
  repeat split; try lia; try constructor.
Qed.

Lemma sublist_cons_z :
  forall {A : Type} (d : A) (lo hi : Z) (l : list A),
    0 <= lo < hi ->
    hi <= Zlength l ->
    sublist lo hi l = Znth lo l d :: sublist (lo + 1) hi l.
Proof.
  intros A d lo hi l Hlo Hhi.
  rewrite (sublist_split lo hi (lo + 1) l) by lia.
  rewrite (sublist_single d) by lia.
  reflexivity.
Qed.

Lemma point_array_seg_pop_tail_at_k :
  forall (base : addr) (k hi : Z) (prefix : list Point) (last : Point),
    k - 1 = Zlength prefix ->
    k <= hi ->
    PointArray.seg base 0 k (prefix ++ last :: nil) **
    PointArray.undef_seg base k hi
    |-- PointArray.seg base 0 (k - 1) prefix **
        PointArray.undef_seg base (k - 1) hi.
Proof.
  intros base k hi prefix last Hlen Hhi.
  replace k with ((k - 1) + 1) by lia.
  replace (k - 1 + 1 - 1) with (k - 1) by lia.
  apply point_array_seg_pop_tail; lia.
Qed.

Lemma points_not_all_same_permutation_worker :
  forall l l', point_permutation l l' ->
  points_not_all_same l -> points_not_all_same l'.
Proof.
  unfold point_permutation, points_not_all_same.
  intros l l' Hperm [i [j [Hi [Hj [Hij Hdiff]]]]].
  pose proof (Znth_In_range l i default_point Hi) as Hin_i.
  pose proof (Znth_In_range l j default_point Hj) as Hin_j.
  pose proof (Permutation_in (Znth i l default_point) Hperm Hin_i) as Hin_i'.
  pose proof (Permutation_in (Znth j l default_point) Hperm Hin_j) as Hin_j'.
  destruct (In_Znth_Zlength l' (Znth i l default_point) default_point Hin_i') as [i' [Hi' Hzi]].
  destruct (In_Znth_Zlength l' (Znth j l default_point) default_point Hin_j') as [j' [Hj' Hzj]].
  exists i', j'. split; [exact Hi'|]. split; [exact Hj'|]. split.
  - intro Heq. subst j'. apply Hdiff. rewrite <- Hzi. rewrite <- Hzj.
    unfold point_same; auto.
  - intro Hsame. apply Hdiff. rewrite <- Hzi. rewrite <- Hzj. exact Hsame.
Qed.

Lemma points_not_all_same_non_singleton_worker :
  forall l, points_not_all_same l -> Andrew_Monotone_Chain.point_list_non_singleton l.
Proof.
  intros l Hnot.
  unfold points_not_all_same in Hnot.
  destruct l as [|p [|q rest]].
  - destruct Hnot as [i [j [Hi [Hj [Hij Hdiff]]]]].
    rewrite Zlength_nil in Hi. lia.
  - destruct Hnot as [i [j [Hi [Hj [Hij Hdiff]]]]].
    rewrite Zlength_cons, Zlength_nil in Hi, Hj. lia.
  - unfold Andrew_Monotone_Chain.point_list_non_singleton. eauto.
Qed.

Lemma leftdown_from_cmp_le_worker :
  forall a b, point_cmp_leftdown a b <= 0 -> Andrew_Monotone_Chain.leftdown a b.
Proof.
  intros a b Hcmp.
  destruct a as [ax ay].
  destruct b as [bx by_].
  unfold point_cmp_leftdown in Hcmp.
  unfold Andrew_Monotone_Chain.leftdown.
  simpl in *.
  destruct (Z_lt_dec ax bx) as [Hlt | Hnlt].
  - left; lia.
  - destruct (Z_gt_dec ax bx) as [Hgt | Hngt].
    + lia.
    + destruct (Z_lt_dec ay by_) as [Hylt | Hynlt].
      * right; split; lia.
      * destruct (Z_gt_dec ay by_) as [Hygt | Hyngt].
        -- lia.
        -- right; split; lia.
Qed.

Lemma public_point_xy_sorted_to_andrew_worker :
  forall l, point_xy_sorted l -> Andrew_Monotone_Chain.point_xy_sorted l.
Proof.
  unfold point_xy_sorted.
  intros l Hsort.
  destruct l as [|p rest]; simpl; [auto|].
  revert p Hsort.
  induction rest as [|q rest IH]; intros p Hsort; simpl; [auto|].
  split.
  - apply leftdown_from_cmp_le_worker.
    specialize (Hsort 0 1 ltac:(lia) ltac:(lia)
      ltac:(rewrite !Zlength_cons; pose proof (Zlength_nonneg rest); lia)).
    simpl in Hsort.
    exact Hsort.
  - apply IH.
    unfold point_xy_sorted_range in *.
    intros i j Hi Hij Hj.
    assert (Hcmp := Hsort (i + 1) (j + 1)
      ltac:(lia) ltac:(lia)
      ltac:(rewrite !Zlength_cons; rewrite Zlength_cons in Hj; lia)).
    rewrite (Znth_cons default_point (i + 1) p (q :: rest)) in Hcmp by lia.
    rewrite (Znth_cons default_point (j + 1) p (q :: rest)) in Hcmp by lia.
    replace (i + 1 - 1) with i in Hcmp by lia.
    replace (j + 1 - 1) with j in Hcmp by lia.
    exact Hcmp.
Qed.

Lemma point_chain_uses_range_drop_last : forall sorted chain lo hi,
  0 < Zlength chain ->
  point_chain_uses_range sorted chain lo hi ->
  point_chain_uses_range sorted (point_drop_last chain) lo hi.
Proof.
  intros sorted chain lo hi Hlen Huse.
  unfold point_chain_uses_range in *.
  destruct Huse as [Hlo [Hlohi [Hhi Hforall]]].
  repeat split; try assumption.
  apply Forall_Znth_intro with (d := default_point).
  intros idx Hidx.
  rewrite point_drop_last_Zlength in Hidx by lia.
  rewrite point_drop_last_Znth by lia.
  eapply Forall_Znth_point; eauto.
  lia.
Qed.

Lemma Forall_point_drop_last : forall (P : Point -> Prop) chain,
  0 < Zlength chain ->
  Forall P chain ->
  Forall P (point_drop_last chain).
Proof.
  intros P chain Hlen Hforall.
  apply Forall_Znth_intro with (d := default_point).
  intros idx Hidx.
  rewrite point_drop_last_Zlength in Hidx by lia.
  rewrite point_drop_last_Znth by lia.
  eapply Forall_Znth_point; eauto.
  lia.
Qed.

Lemma points_in_bound_drop_last : forall chain,
  0 < Zlength chain ->
  points_in_bound chain ->
  points_in_bound (point_drop_last chain).
Proof.
  intros chain Hlen Hbound.
  unfold points_in_bound in *.
  apply Forall_point_drop_last; assumption.
Qed.

Lemma point_chain_strictly_uses_range_drop_last : forall sorted chain lo hi,
  0 < Zlength chain ->
  point_chain_strictly_uses_range sorted chain lo hi ->
  point_chain_strictly_uses_range sorted (point_drop_last chain) lo hi.
Proof.
  intros sorted chain lo hi Hlen Hstrict.
  unfold point_chain_strictly_uses_range in *.
  destruct Hstrict as [idxs [Hindexed Hinc]].
  unfold point_chain_indexed_by_range in Hindexed.
  destruct Hindexed as [Hidx_len Hlookup].
  exists (sublist 0 (Zlength idxs - 1) idxs).
  split.
  - unfold point_chain_indexed_by_range.
    split.
    + rewrite point_drop_last_Zlength by lia.
      rewrite Zlength_sublist by lia.
      lia.
    + intros pos Hpos.
      rewrite point_drop_last_Zlength in Hpos by lia.
      specialize (Hlookup pos ltac:(lia)) as [Hrange Hpoint].
      split; [|].
      * rewrite Znth_sublist by lia.
        replace (pos + 0) with pos by lia.
        exact Hrange.
      * rewrite point_drop_last_Znth by lia.
        rewrite Znth_sublist by lia.
        replace (pos + 0) with pos by lia.
        exact Hpoint.
  - unfold point_indices_strict_increasing in *.
    intros a b Ha Hab Hb.
    rewrite Zlength_sublist in Hb by lia.
    rewrite !Znth_sublist by lia.
    replace (a + 0) with a by lia.
    replace (b + 0) with b by lia.
    apply Hinc; lia.
Qed.

Lemma point_chain_starts_at_drop_last : forall sorted chain idx,
  1 < Zlength chain ->
  point_chain_starts_at sorted chain idx ->
  point_chain_starts_at sorted (point_drop_last chain) idx.
Proof.
  intros sorted chain idx Hlen Hstart.
  unfold point_chain_starts_at in *.
  intros Hdrop_nonempty.
  rewrite point_drop_last_Znth by lia.
  apply Hstart.
  lia.
Qed.

Lemma point_chain_left_turns_drop_last : forall chain,
  0 < Zlength chain ->
  point_chain_left_turns chain ->
  point_chain_left_turns (point_drop_last chain).
Proof.
  intros chain Hlen Hturn.
  unfold point_chain_left_turns in *.
  intros idx Hidx Hidx_len.
  rewrite point_drop_last_Zlength in Hidx_len by lia.
  rewrite !point_drop_last_Znth by lia.
  apply Hturn; lia.
Qed.

Lemma point_chain_left_envelope_drop_last : forall sorted chain lo hi,
  0 < Zlength chain ->
  point_chain_left_envelope sorted chain lo hi ->
  point_chain_left_envelope sorted (point_drop_last chain) lo hi.
Proof.
  intros sorted chain lo hi Hlen Henv.
  unfold point_chain_left_envelope in *.
  intros edge_idx point_idx Hedge HedgeLen Hpoint.
  rewrite point_drop_last_Zlength in HedgeLen by lia.
  rewrite !point_drop_last_Znth by lia.
  apply Henv; lia.
Qed.

Lemma andrew_lower_chain_geometry_drop_last : forall sorted chain read,
  1 < Zlength chain ->
  andrew_lower_chain_geometry sorted chain read ->
  andrew_lower_chain_geometry sorted (point_drop_last chain) read.
Proof.
  intros sorted chain read Hlen Hgeom.
  unfold andrew_lower_chain_geometry in *.
  destruct Hgeom as [Huse [Hstrict [Hstart [Hturn Henv]]]].
  split; [apply point_chain_uses_range_drop_last; try lia; exact Huse |].
  split; [apply point_chain_strictly_uses_range_drop_last; try lia; exact Hstrict |].
  split; [apply point_chain_starts_at_drop_last; try lia; exact Hstart |].
  split; [apply point_chain_left_turns_drop_last; try lia; exact Hturn |].
  apply point_chain_left_envelope_drop_last; try lia; exact Henv.
Qed.

Lemma safeExec_andrew_lower_cont_pop : forall sorted read t s T X,
  0 <= read ->
  read < Zlength sorted ->
  ~ ccw s t (Znth read sorted default_point) ->
  safeExec (equiv (t :: s :: T)) (andrew_lower_cont sorted read) X ->
  safeExec (equiv (s :: T)) (andrew_lower_cont sorted read) X.
Proof.
  intros sorted read t s T X Hread_nonneg Hread_lt Hnccw Hsafe.
  unfold andrew_lower_cont in *.
  unfold build_hull_c_iter in Hsafe at 1.
  rewrite (sublist_split read (Zlength sorted) (read + 1) sorted) in Hsafe
    by (pose proof (Zlength_nonneg sorted); lia).
  rewrite (sublist_single default_point read sorted) in Hsafe by lia.
  simpl in Hsafe.
  unfold Graham_Scan_M.step_p at 1 in Hsafe.
  unfold build_hull_c_iter.
  rewrite (sublist_split read (Zlength sorted) (read + 1) sorted)
    by (pose proof (Zlength_nonneg sorted); lia).
  rewrite (sublist_single default_point read sorted) by lia.
  simpl.
  unfold Graham_Scan_M.step_p at 1.
  unfold Graham_Scan_M.step_fun in Hsafe at 1.
  prog_nf in Hsafe.
  unfold_loop in Hsafe.
  prog_nf in Hsafe.
  unfold Graham_Scan_M.step_fun at 1.
  prog_nf.
  unfold_loop.
  prog_nf.
  eapply (@safeExec_proequiv (list Point) unit
    (repeat_break
       (fun _ : unit => pop_fun (Znth read sorted default_point)) tt ;;
     x0 <- (T0 <- get' id ;;
            update'
              (fun _ : list Point => Znth read sorted default_point :: T0)) ;;
     iter step_p (sublist (read + 1) (Zlength sorted) sorted) x0 ;;
     T0 <- get' id ;;
     upper <- Andrew_Monotone_Chain_M.build_upper_chain sorted ;;
     update'
       (fun _ : list Point =>
          Andrew_Monotone_Chain.andrew_merge sorted (rev T0) upper))
    _ (equiv (s :: T)) X).
  - unfold_loop. prog_nf. hnf; intros; split; intros; assumption.
  - eapply (highstepbind_derive
            (pop_fun (Znth read sorted default_point))
            (fun x =>
               match x with
               | by_continue a0 =>
                   repeat_break
                     (fun _ : unit => pop_fun (Znth read sorted default_point)) a0
               | by_break b0 => return b0
               end ;;
               x0 <- (T0 <- get' id ;;
                      update'
                        (fun _ : list Point =>
                           Znth read sorted default_point :: T0)) ;;
               iter step_p (sublist (read + 1) (Zlength sorted) sorted) x0 ;;
               T0 <- get' id ;;
               upper <- Andrew_Monotone_Chain_M.build_upper_chain sorted ;;
               update'
                 (fun _ : list Point =>
                    Andrew_Monotone_Chain.andrew_merge sorted (rev T0) upper))
            (equiv (t :: s :: T)) (by_continue tt) (equiv (s :: T))).
    + apply pop_fun_continue_hseval.
      exact Hnccw.
    + exact Hsafe.
Qed.

Lemma safeExec_andrew_lower_cont_drop_last : forall sorted chain read top X,
  point_cross (Znth (top - 2) chain default_point)
              (Znth (top - 1) chain default_point)
              (Znth read sorted default_point) <= 0 ->
  2 <= top ->
  0 <= read ->
  top = Zlength chain ->
  read < Zlength sorted ->
  safeExec (equiv (rev chain)) (andrew_lower_cont sorted read) X ->
  safeExec (equiv (rev (point_drop_last chain)))
           (andrew_lower_cont sorted read) X.
Proof.
  intros sorted chain read top X Hcross Htop_ge Hread_nonneg Htop Hread_lt Hsafe.
  destruct (rev chain) as [| t [| s T]] eqn:Hrev.
  - apply (f_equal (@rev Point)) in Hrev.
    rewrite rev_involutive in Hrev.
    simpl in Hrev.
    subst chain.
    rewrite Zlength_nil in Htop. lia.
  - apply (f_equal (@rev Point)) in Hrev.
    rewrite rev_involutive in Hrev.
    simpl in Hrev.
    subst chain.
    rewrite Zlength_cons, Zlength_nil in Htop. lia.
  - assert (Hchain : chain = rev (t :: s :: T)).
    {
      rewrite <- (rev_involutive chain).
      rewrite Hrev.
      reflexivity.
    }
    subst chain.
    change (point_drop_last (rev (t :: s :: T))) with
      (point_drop_last (rev (s :: T) ++ t :: nil)).
    rewrite point_drop_last_snoc.
    rewrite rev_involutive.
    assert (Hlen_for_rev : top - 1 + 1 = Zlength (rev (t :: s :: T))) by lia.
    assert (Hnccw : ~ ccw s t (Znth read sorted default_point)).
    {
      replace (Znth (top - 2) (rev (t :: s :: T)) default_point)
        with (Znth (top - 1 - 1 - 0) (rev (t :: s :: T)) default_point)
        in Hcross by (f_equal; lia).
      replace (Znth (top - 1) (rev (t :: s :: T)) default_point)
        with (Znth (top - 1 - 0) (rev (t :: s :: T)) default_point)
        in Hcross by (f_equal; lia).
      rewrite (Znth_rev_stack_prev default_point t s T (top - 1)) in Hcross
        by exact Hlen_for_rev.
      rewrite (Znth_rev_stack_top default_point t s T (top - 1)) in Hcross
        by exact Hlen_for_rev.
      apply point_cross_le_0_not_ccw_local.
      exact Hcross.
    }
    eapply safeExec_andrew_lower_cont_pop; eauto.
Qed.

Lemma safeExec_andrew_lower_cont_short_push :
  forall sorted chain read top X,
    top = Zlength chain ->
    top < 2 ->
    0 <= read ->
    read < Zlength sorted ->
    safeExec (equiv (rev chain)) (andrew_lower_cont sorted read) X ->
    safeExec
      (equiv (rev (chain ++ Znth read sorted default_point :: nil)))
      (andrew_lower_cont sorted (read + 1)) X.
Proof.
  intros sorted chain read top X Htop Htop_lt Hread_nonneg Hread_lt Hsafe.
  unfold andrew_lower_cont in *.
  unfold build_hull_c_iter in Hsafe at 1.
  rewrite (sublist_split read (Zlength sorted) (read + 1) sorted) in Hsafe
    by (pose proof (Zlength_nonneg sorted); lia).
  rewrite (sublist_single default_point read sorted) in Hsafe by lia.
  simpl in Hsafe.
  unfold Graham_Scan_M.step_p at 1 in Hsafe.
  eapply safeExec_bind_assoc_forward in Hsafe.
  unfold build_hull_c_iter.
  destruct chain as [| t [| s T]]; simpl in *.
  - eapply (highstepbind_derive
              (Graham_Scan_M.step_fun (Znth read sorted default_point))
              (fun b0 : unit =>
                 iter step_p (sublist (read + 1) (Zlength sorted) sorted) b0 ;;
                 T <- get' id ;;
                 upper <- Andrew_Monotone_Chain_M.build_upper_chain sorted ;;
                 update'
                   (fun _ : list Point =>
                      Andrew_Monotone_Chain.andrew_merge sorted (rev T) upper))
              (equiv nil) tt
              (equiv (Znth read sorted default_point :: nil))).
    + apply step_fun_nil_push_hseval.
    + exact Hsafe.
  - eapply (highstepbind_derive
              (Graham_Scan_M.step_fun (Znth read sorted default_point))
              (fun b0 : unit =>
                 iter step_p (sublist (read + 1) (Zlength sorted) sorted) b0 ;;
                 T <- get' id ;;
                 upper <- Andrew_Monotone_Chain_M.build_upper_chain sorted ;;
                 update'
                   (fun _ : list Point =>
                      Andrew_Monotone_Chain.andrew_merge sorted (rev T) upper))
              (equiv (t :: nil)) tt
              (equiv (Znth read sorted default_point :: t :: nil))).
    + apply step_fun_single_push_hseval.
    + exact Hsafe.
  - pose proof (Zlength_nonneg T).
    rewrite Zlength_cons, Zlength_cons in Htop.
    lia.
Qed.

Lemma safeExec_andrew_lower_cont_ccw_push :
  forall sorted chain read top X,
    top = Zlength chain ->
    2 <= top ->
    0 <= read ->
    read < Zlength sorted ->
    point_cross (Znth (top - 2) chain default_point)
                (Znth (top - 1) chain default_point)
                (Znth read sorted default_point) > 0 ->
    safeExec (equiv (rev chain)) (andrew_lower_cont sorted read) X ->
    safeExec
      (equiv (rev (chain ++ Znth read sorted default_point :: nil)))
      (andrew_lower_cont sorted (read + 1)) X.
Proof.
  intros sorted chain read top X Htop Htop_ge Hread_nonneg Hread_lt
         Hcross Hsafe.
  unfold andrew_lower_cont in *.
  unfold build_hull_c_iter in Hsafe at 1.
  rewrite (sublist_split read (Zlength sorted) (read + 1) sorted) in Hsafe
    by (pose proof (Zlength_nonneg sorted); lia).
  rewrite (sublist_single default_point read sorted) in Hsafe by lia.
  simpl in Hsafe.
  unfold Graham_Scan_M.step_p at 1 in Hsafe.
  eapply safeExec_bind_assoc_forward in Hsafe.
  unfold build_hull_c_iter.
  destruct (rev chain) as [| t [| s T]] eqn:Hrev.
  - apply (f_equal (@rev Point)) in Hrev.
    rewrite rev_involutive in Hrev.
    simpl in Hrev.
    subst chain.
    rewrite Zlength_nil in Htop. lia.
  - apply (f_equal (@rev Point)) in Hrev.
    rewrite rev_involutive in Hrev.
    simpl in Hrev.
    subst chain.
    rewrite Zlength_cons, Zlength_nil in Htop. lia.
  - assert (Hchain : chain = rev (t :: s :: T)).
    {
      rewrite <- (rev_involutive chain).
      rewrite Hrev.
      reflexivity.
    }
    subst chain.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_involutive.
    assert (Hlen_for_rev : top - 1 + 1 = Zlength (rev (t :: s :: T))) by lia.
    assert (Hccw : ccw s t (Znth read sorted default_point)).
    {
      replace (Znth (top - 2) (rev (t :: s :: T)) default_point)
        with (Znth (top - 1 - 1 - 0) (rev (t :: s :: T)) default_point)
        in Hcross by (f_equal; lia).
      replace (Znth (top - 1) (rev (t :: s :: T)) default_point)
        with (Znth (top - 1 - 0) (rev (t :: s :: T)) default_point)
        in Hcross by (f_equal; lia).
      rewrite (Znth_rev_stack_prev default_point t s T (top - 1)) in Hcross
        by exact Hlen_for_rev.
      rewrite (Znth_rev_stack_top default_point t s T (top - 1)) in Hcross
        by exact Hlen_for_rev.
      apply point_cross_gt_0_ccw_local.
      exact Hcross.
    }
    eapply (highstepbind_derive
              (Graham_Scan_M.step_fun (Znth read sorted default_point))
              (fun b0 : unit =>
                 iter step_p (sublist (read + 1) (Zlength sorted) sorted) b0 ;;
                 T0 <- get' id ;;
                 upper <- Andrew_Monotone_Chain_M.build_upper_chain sorted ;;
                 update'
                   (fun _ : list Point =>
                      Andrew_Monotone_Chain.andrew_merge sorted (rev T0) upper))
              (equiv (t :: s :: T)) tt
              (equiv (Znth read sorted default_point :: t :: s :: T))).
    + apply step_fun_ccw_push_hseval.
      exact Hccw.
    + exact Hsafe.
Qed.

Lemma safeExec_andrew_lower_cont_done_snoc_to_upper :
  forall sorted prefix read X,
    read + 1 = Zlength sorted ->
    0 <= read ->
    safeExec
      (equiv (rev (prefix ++ Znth read sorted default_point :: nil)))
      (andrew_lower_cont sorted (read + 1)) X ->
    safeExec
      (equiv (Znth read sorted default_point :: nil))
      (andrew_upper_cont sorted
        (prefix ++ Znth read sorted default_point :: nil)
        (Zlength sorted - 1)) X.
Proof.
  intros sorted prefix read X Hread_end Hread_nonneg Hsafe.
  set (p := Znth read sorted default_point).
  set (lower := prefix ++ p :: nil).
  assert (Hread_lt : read < Zlength sorted) by lia.
  assert (Hsorted_split : sorted = sublist 0 read sorted ++ p :: nil).
  {
    subst p.
    rewrite <- (sublist_self sorted (Zlength sorted)) at 1 by reflexivity.
    rewrite (sublist_split 0 (Zlength sorted) read sorted) by lia.
    replace (Zlength sorted) with (read + 1) by lia.
    rewrite (sublist_single default_point read sorted) by lia.
    reflexivity.
  }
  unfold andrew_lower_cont in Hsafe.
  unfold build_hull_c_iter in Hsafe at 1.
  replace (read + 1) with (Zlength sorted) in Hsafe by lia.
  rewrite Zsublist_nil in Hsafe by lia.
  simpl in Hsafe.
  prog_nf in Hsafe.
  eapply (safeExec_bind_reta (ret tt) _ _ _ tt) in Hsafe.
  2:{
    intros X0 Hret.
    exact Hret.
  }
  eapply (safeExec_bind_reta _ _ _ _ (rev lower)) in Hsafe.
  2:{
    intros X0 Hget.
    eapply safeExec_get'; [| exact Hget].
    intros s Hs.
    hnf in Hs.
    exact Hs.
  }
  rewrite rev_involutive in Hsafe.
  unfold Andrew_Monotone_Chain_M.build_upper_chain in Hsafe.
  unfold Andrew_Monotone_Chain_M.build_chain in Hsafe.
  prog_nf in Hsafe.
  eapply safeExec_update'_bind in Hsafe.
  eapply (safeExec_conseq (equiv nil)) in Hsafe.
  2:{
    intros s [s0 [Hs _]].
    subst s.
    reflexivity.
  }
  rewrite Hsorted_split in Hsafe.
  rewrite rev_app_distr in Hsafe.
  simpl in Hsafe.
  unfold Graham_Scan_M.step_p in Hsafe at 1.
  prog_nf in Hsafe.
  eapply (highstepbind_derive
            (Graham_Scan_M.step_fun p)
            (fun x : unit =>
               iter step_p (rev (sublist 0 read sorted)) x ;;
               upper <- (T <- get' id ;; ret (rev T)) ;;
               update'
                 (fun _ : list Point =>
                    Andrew_Monotone_Chain.andrew_merge
                      (sublist 0 read sorted ++ p :: nil) lower upper))
            (equiv nil) tt (equiv (p :: nil))) in Hsafe.
  2:{
    apply step_fun_nil_push_hseval.
  }
  prog_nf in Hsafe.
  rewrite <- Hsorted_split in Hsafe.
  subst lower p.
  unfold andrew_upper_cont, andrew_upper_remaining_points.
  replace (Zlength sorted - 1) with read by lia.
  eapply (@safeExec_proequiv (list Point) unit
      (iter step_p (rev (sublist 0 read sorted)) tt ;;
       upper <- (T <- get' id ;; ret (rev T)) ;;
       update'
         (fun _ : list Point =>
            Andrew_Monotone_Chain.andrew_merge sorted
              (prefix ++ Znth read sorted default_point :: nil) upper))
      (iter step_p (rev (sublist 0 read sorted)) tt ;;
       T <- get' id ;;
       update'
         (fun _ : list Point =>
            Andrew_Monotone_Chain.andrew_merge sorted
              (prefix ++ Znth read sorted default_point :: nil) (rev T)))
      (equiv (Znth read sorted default_point :: nil)) X).
  - apply common_step_equiv; intros [].
    etransitivity.
    + apply bind_assoc.
    + apply common_step_equiv; intro T.
      apply (@bind_ret_left (list Point) (list Point) unit (rev T)
        (fun upper =>
           update'
             (fun _ : list Point =>
                Andrew_Monotone_Chain.andrew_merge sorted
                  (prefix ++ Znth read sorted default_point :: nil) upper))).
  - exact Hsafe.
Qed.

Lemma safeExec_andrew_upper_cont_pop : forall sorted lower read t s T X,
  1 <= read ->
  read <= Zlength sorted ->
  ~ ccw s t (Znth (read - 1) sorted default_point) ->
  safeExec (equiv (t :: s :: T)) (andrew_upper_cont sorted lower read) X ->
  safeExec (equiv (s :: T)) (andrew_upper_cont sorted lower read) X.
Proof.
  intros sorted lower read t s T X Hread_pos Hread_le Hnccw Hsafe.
  unfold andrew_upper_cont, andrew_upper_remaining_points in *.
  rewrite (sublist_split 0 read (read - 1) sorted) in Hsafe by lia.
  replace (sublist (read - 1) read sorted)
    with (sublist (read - 1) (read - 1 + 1) sorted) in Hsafe
    by (f_equal; lia).
  rewrite (sublist_single default_point (read - 1) sorted) in Hsafe by lia.
  rewrite rev_app_distr in Hsafe.
  simpl in Hsafe.
  unfold Graham_Scan_M.step_p at 1 in Hsafe.
  rewrite (sublist_split 0 read (read - 1) sorted) by lia.
  replace (sublist (read - 1) read sorted)
    with (sublist (read - 1) (read - 1 + 1) sorted)
    by (f_equal; lia).
  rewrite (sublist_single default_point (read - 1) sorted) by lia.
  rewrite rev_app_distr.
  simpl.
  unfold Graham_Scan_M.step_p at 1.
  unfold Graham_Scan_M.step_fun in Hsafe at 1.
  prog_nf in Hsafe.
  unfold_loop in Hsafe.
  prog_nf in Hsafe.
  unfold Graham_Scan_M.step_fun at 1.
  prog_nf.
  unfold_loop.
  prog_nf.
  eapply (@safeExec_proequiv (list Point) unit
    (repeat_break
       (fun _ : unit => pop_fun (Znth (read - 1) sorted default_point)) tt ;;
     x0 <- (T0 <- get' id ;;
            update'
              (fun _ : list Point =>
                 Znth (read - 1) sorted default_point :: T0)) ;;
     iter step_p (rev (sublist 0 (read - 1) sorted)) x0 ;;
     T0 <- get' id ;;
     update'
       (fun _ : list Point =>
          Andrew_Monotone_Chain.andrew_merge sorted lower (rev T0)))
    _ (equiv (s :: T)) X).
  - unfold_loop. prog_nf. hnf; intros; split; intros; assumption.
  - eapply (highstepbind_derive
            (pop_fun (Znth (read - 1) sorted default_point))
            (fun x =>
               match x with
               | by_continue a0 =>
                   repeat_break
                     (fun _ : unit =>
                        pop_fun (Znth (read - 1) sorted default_point)) a0
               | by_break b0 => return b0
               end ;;
               x0 <- (T0 <- get' id ;;
                      update'
                        (fun _ : list Point =>
                           Znth (read - 1) sorted default_point :: T0)) ;;
               iter step_p (rev (sublist 0 (read - 1) sorted)) x0 ;;
               T0 <- get' id ;;
               update'
                 (fun _ : list Point =>
                    Andrew_Monotone_Chain.andrew_merge sorted lower (rev T0)))
            (equiv (t :: s :: T)) (by_continue tt) (equiv (s :: T))).
    + apply pop_fun_continue_hseval.
      exact Hnccw.
    + exact Hsafe.
Qed.

Lemma safeExec_andrew_upper_cont_single_push :
  forall sorted lower read t X,
    1 <= read ->
    read <= Zlength sorted ->
    safeExec (equiv (t :: nil)) (andrew_upper_cont sorted lower read) X ->
    safeExec (equiv (Znth (read - 1) sorted default_point :: t :: nil))
      (andrew_upper_cont sorted lower (read - 1)) X.
Proof.
  intros sorted lower read t X Hread_pos Hread_le Hsafe.
  unfold andrew_upper_cont, andrew_upper_remaining_points in *.
  rewrite (sublist_split 0 read (read - 1) sorted) in Hsafe by lia.
  replace (sublist (read - 1) read sorted)
    with (sublist (read - 1) (read - 1 + 1) sorted) in Hsafe
    by (f_equal; lia).
  rewrite (sublist_single default_point (read - 1) sorted) in Hsafe by lia.
  rewrite rev_app_distr in Hsafe.
  simpl in Hsafe.
  unfold Graham_Scan_M.step_p at 1 in Hsafe.
  eapply safeExec_bind_assoc_forward in Hsafe.
  eapply (highstepbind_derive
            (Graham_Scan_M.step_fun (Znth (read - 1) sorted default_point))
            (fun b0 : unit =>
               iter step_p (rev (sublist 0 (read - 1) sorted)) b0 ;;
               T0 <- get' id ;;
               update'
                 (fun _ : list Point =>
                    Andrew_Monotone_Chain.andrew_merge sorted lower (rev T0)))
            (equiv (t :: nil)) tt
            (equiv (Znth (read - 1) sorted default_point :: t :: nil))).
  - apply step_fun_single_push_hseval.
  - exact Hsafe.
Qed.

Lemma safeExec_andrew_upper_cont_ccw_push :
  forall sorted lower chain read top X,
    top = Zlength chain ->
    2 <= top ->
    1 <= read ->
    read <= Zlength sorted ->
    point_cross (Znth (top - 2) chain default_point)
                (Znth (top - 1) chain default_point)
                (Znth (read - 1) sorted default_point) > 0 ->
    safeExec (equiv (rev chain)) (andrew_upper_cont sorted lower read) X ->
    safeExec
      (equiv (rev (chain ++ Znth (read - 1) sorted default_point :: nil)))
      (andrew_upper_cont sorted lower (read - 1)) X.
Proof.
  intros sorted lower chain read top X Htop Htop_ge Hread_pos Hread_le
         Hcross Hsafe.
  unfold andrew_upper_cont, andrew_upper_remaining_points in *.
  rewrite (sublist_split 0 read (read - 1) sorted) in Hsafe by lia.
  replace (sublist (read - 1) read sorted)
    with (sublist (read - 1) (read - 1 + 1) sorted) in Hsafe
    by (f_equal; lia).
  rewrite (sublist_single default_point (read - 1) sorted) in Hsafe by lia.
  rewrite rev_app_distr in Hsafe.
  simpl in Hsafe.
  unfold Graham_Scan_M.step_p at 1 in Hsafe.
  eapply safeExec_bind_assoc_forward in Hsafe.
  destruct (rev chain) as [| t [| s T]] eqn:Hrev.
  - apply (f_equal (@rev Point)) in Hrev.
    rewrite rev_involutive in Hrev.
    simpl in Hrev.
    subst chain.
    rewrite Zlength_nil in Htop. lia.
  - apply (f_equal (@rev Point)) in Hrev.
    rewrite rev_involutive in Hrev.
    simpl in Hrev.
    subst chain.
    rewrite Zlength_cons, Zlength_nil in Htop. lia.
  - assert (Hchain : chain = rev (t :: s :: T)).
    {
      rewrite <- (rev_involutive chain).
      rewrite Hrev.
      reflexivity.
    }
    subst chain.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_involutive.
    assert (Hlen_for_rev : top - 1 + 1 = Zlength (rev (t :: s :: T))) by lia.
    assert (Hccw : ccw s t (Znth (read - 1) sorted default_point)).
    {
      replace (Znth (top - 2) (rev (t :: s :: T)) default_point)
        with (Znth (top - 1 - 1 - 0) (rev (t :: s :: T)) default_point)
        in Hcross by (f_equal; lia).
      replace (Znth (top - 1) (rev (t :: s :: T)) default_point)
        with (Znth (top - 1 - 0) (rev (t :: s :: T)) default_point)
        in Hcross by (f_equal; lia).
      rewrite (Znth_rev_stack_prev default_point t s T (top - 1)) in Hcross
        by exact Hlen_for_rev.
      rewrite (Znth_rev_stack_top default_point t s T (top - 1)) in Hcross
        by exact Hlen_for_rev.
      apply point_cross_gt_0_ccw_local.
      exact Hcross.
    }
    eapply (highstepbind_derive
              (Graham_Scan_M.step_fun (Znth (read - 1) sorted default_point))
              (fun b0 : unit =>
                 iter step_p (rev (sublist 0 (read - 1) sorted)) b0 ;;
                 T0 <- get' id ;;
                 update'
                   (fun _ : list Point =>
                      Andrew_Monotone_Chain.andrew_merge sorted lower (rev T0)))
              (equiv (t :: s :: T)) tt
              (equiv (Znth (read - 1) sorted default_point :: t :: s :: T))).
    + apply step_fun_ccw_push_hseval.
      exact Hccw.
    + exact Hsafe.
Qed.

Lemma andrew_merge_upper_done_point_drop_last :
  forall sorted chain lower_n,
    2 <= Zlength sorted ->
    2 <= lower_n ->
    lower_n < Zlength chain ->
    Andrew_Monotone_Chain.andrew_merge sorted
      (sublist 0 lower_n chain)
      (sublist (lower_n - 1) (Zlength chain) chain) =
    rev (point_drop_last chain).
Proof.
  intros sorted chain lower_n Hsorted_len Hlower_len Hlower_lt.
  unfold Andrew_Monotone_Chain.andrew_merge.
  unfold Andrew_Monotone_Chain.andrew_ccw_merge.
  destruct sorted as [| a sorted_tail].
  { rewrite Zlength_nil in Hsorted_len. lia. }
  destruct sorted_tail as [| b sorted_tail].
  { rewrite Zlength_cons, Zlength_nil in Hsorted_len. lia. }
  simpl.
  assert (Hlower :
    sublist 0 lower_n chain =
    sublist 0 (lower_n - 1) chain ++
    Znth (lower_n - 1) chain default_point :: nil).
  {
    rewrite (sublist_split 0 lower_n (lower_n - 1) chain) by lia.
    replace (sublist (lower_n - 1) lower_n chain)
      with (sublist (lower_n - 1) ((lower_n - 1) + 1) chain)
      by (f_equal; lia).
    rewrite (sublist_single default_point (lower_n - 1) chain) by lia.
    reflexivity.
  }
  assert (Hupper :
    sublist (lower_n - 1) (Zlength chain) chain =
    sublist (lower_n - 1) (Zlength chain - 1) chain ++
    Znth (Zlength chain - 1) chain default_point :: nil).
  {
    rewrite (sublist_split (lower_n - 1) (Zlength chain)
              (Zlength chain - 1) chain) by lia.
    replace (sublist (Zlength chain - 1) (Zlength chain) chain)
      with (sublist (Zlength chain - 1) ((Zlength chain - 1) + 1) chain)
      by (f_equal; lia).
    rewrite (sublist_single default_point (Zlength chain - 1) chain) by lia.
    reflexivity.
  }
  rewrite Hlower, Hupper.
  rewrite !Andrew_Monotone_Chain.removelast_snoc.
  unfold point_drop_last.
  rewrite <- (sublist_split 0 (Zlength chain - 1) (lower_n - 1) chain)
    by lia.
  reflexivity.
Qed.

Lemma safeExec_andrew_upper_cont_done_point_drop_last :
  forall sorted chain lower_n X,
    2 <= Zlength sorted ->
    2 <= lower_n ->
    lower_n < Zlength chain ->
    safeExec
      (equiv (rev (sublist (lower_n - 1) (Zlength chain) chain)))
      (andrew_upper_cont sorted (sublist 0 lower_n chain) 0) X ->
    safeExec (equiv (rev (point_drop_last chain))) (return tt) X.
Proof.
  intros sorted chain lower_n X Hsorted_len Hlower_len Hlower_lt Hsafe.
  unfold andrew_upper_cont, andrew_upper_remaining_points in Hsafe.
  replace (sublist 0 0 sorted) with (@nil Point) in Hsafe
    by (rewrite Zsublist_nil by lia; reflexivity).
  simpl in Hsafe.
  prog_nf in Hsafe.
  eapply (safeExec_bind_reta (ret tt) _ _ _ tt) in Hsafe.
  2:{
    intros X0 Hret.
    exact Hret.
  }
  eapply (safeExec_bind_reta _ _ _ _
            (rev (sublist (lower_n - 1) (Zlength chain) chain))) in Hsafe.
  2:{
    intros X0 Hget.
    eapply safeExec_get'; [| exact Hget].
    intros s Hs.
    hnf in Hs.
    exact Hs.
  }
  eapply safeExec_update' in Hsafe.
  eapply safeExec_conseq.
  - exact Hsafe.
  - intros s [s0 [Hs Heq]].
    hnf in Heq.
    subst s0 s.
    hnf.
    rewrite rev_involutive.
    rewrite andrew_merge_upper_done_point_drop_last by lia.
    reflexivity.
Qed.

Lemma point_xy_sorted_leftdown_Znth : forall l i j,
  point_xy_sorted l ->
  0 <= i <= j ->
  j < Zlength l ->
  point_leftdown (Znth i l default_point) (Znth j l default_point).
Proof.
  intros l i j Hsorted Hij Hj.
  apply point_cmp_leftdown_le_point_leftdown.
  unfold point_xy_sorted, point_xy_sorted_range in Hsorted.
  apply Hsorted; lia.
Qed.
