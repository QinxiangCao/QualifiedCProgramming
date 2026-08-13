(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From SimpleC.EE.Applications_human.convex_hull Require Import
  Geo_Point_Primitives Convexity Maximality Point_Order Graham_Scan.
Import ListNotations.
Local Open Scope Z_scope.
(* /COQ-HEAD *)

(** Andrew's monotone chain uses the same stack update as [build_hull]:
    repeatedly pop the stack while the next point would make a non-left turn,
    then push the point.  The state is the stack with its top at the head. *)
Definition andrew_scan_stack (l : list point) : list point :=
  fold_left (fun T p => graham_scan_inc p T) l [].

Definition andrew_chain (l : list point) : list point :=
  rev (andrew_scan_stack l).

Definition andrew_lower_chain (sorted : list point) : list point :=
  andrew_chain sorted.

Definition andrew_upper_chain (sorted : list point) : list point :=
  andrew_chain (rev sorted).

(** [lower] runs from left to right; [upper] runs from right to left.
    For lists with at least two input points, the last vertex of each chain is
    duplicated by the other chain, so [removelast] opens both chains before
    concatenation.

    This is the usual Andrew order.  [Maximality.is_convex_hull] uses the
    opposite directed-edge orientation, so [andrew_merge] below reverses this
    concrete merge for the specification hull. *)
Definition andrew_ccw_merge
    (sorted lower upper : list point) : list point :=
  match sorted with
  | [] => []
  | [_] => sorted
  | _ => removelast lower ++ removelast upper
  end.

Definition andrew_merge
    (sorted lower upper : list point) : list point :=
  rev (andrew_ccw_merge sorted lower upper).

Definition andrew_hull (sorted : list point) : list point :=
  andrew_merge
    sorted
    (andrew_lower_chain sorted)
    (andrew_upper_chain sorted).




Definition leftdown (p q : point) : Prop :=
  x p < x q \/ (x p = x q /\ y p <= y q).

Lemma point_eq_dec : forall p q : point, {p = q} + {p <> q}.
Proof.
  decide equality; apply Z.eq_dec.
Qed.

Lemma leftdown_refl : forall p,
  leftdown p p.
Proof.
  unfold leftdown.
  intros p.
  right; split; lia.
Qed.

Lemma leftdown_trans : forall p q r,
  leftdown p q ->
  leftdown q r ->
  leftdown p r.
Proof.
  unfold leftdown.
  intros p q r Hpq Hqr.
  destruct Hpq as [Hpq | [Hpqx Hpqy]];
  destruct Hqr as [Hqr | [Hqrx Hqry]]; simpl in *; lia.
Qed.

Fixpoint point_xy_sorted_from (p : point) (l : list point) : Prop :=
  match l with
  | [] => True
  | q :: rest => leftdown p q /\ point_xy_sorted_from q rest
  end.

Definition point_xy_sorted (l : list point) : Prop :=
  match l with
  | [] => True
  | p :: rest => point_xy_sorted_from p rest
  end.

Fixpoint point_xy_rev_sorted_from (p : point) (l : list point) : Prop :=
  match l with
  | [] => True
  | q :: rest => leftdown q p /\ point_xy_rev_sorted_from q rest
  end.

Definition point_xy_rev_sorted (l : list point) : Prop :=
  match l with
  | [] => True
  | p :: rest => point_xy_rev_sorted_from p rest
  end.

Lemma point_xy_sorted_from_leftdown_head : forall p l,
  point_xy_sorted_from p l ->
  Forall (leftdown p) l.
Proof.
  intros p l; revert p.
  induction l as [| q l IH]; intros p Hsorted; simpl in *.
  - constructor.
  - destruct Hsorted as [Hpq Hsorted].
    constructor; [exact Hpq |].
    eapply Forall_impl.
    2: { apply IH. exact Hsorted. }
    intros r Hqr.
    eapply leftdown_trans; eauto.
Qed.

Lemma point_xy_sorted_tail : forall p l,
  point_xy_sorted_from p l ->
  point_xy_sorted l.
Proof.
  intros p l Hsorted.
  destruct l as [| q l]; simpl in *; tauto.
Qed.

Lemma point_xy_rev_sorted_from_leftdown_head : forall p l,
  point_xy_rev_sorted_from p l ->
  Forall (fun q => leftdown q p) l.
Proof.
  intros p l; revert p.
  induction l as [| q l IH]; intros p Hsorted; simpl in *.
  - constructor.
  - destruct Hsorted as [Hqp Hsorted].
    constructor; [exact Hqp |].
    eapply Forall_impl.
    2: { apply IH. exact Hsorted. }
    intros r Hrq.
    exact (leftdown_trans r q p Hrq Hqp).
Qed.

Lemma point_xy_rev_sorted_tail : forall p l,
  point_xy_rev_sorted_from p l ->
  point_xy_rev_sorted l.
Proof.
  intros p l Hsorted.
  destruct l as [| q l]; simpl in *; tauto.
Qed.

Definition point_list_non_singleton (l : list point) : Prop :=
  exists p q rest, l = p :: q :: rest.

Definition andrew_hull_geometry (sorted : list point) : Prop :=
  point_list_non_singleton sorted /\
  rev_ccw_convex (andrew_hull sorted) /\
  is_max_hull'_edges (andrew_hull sorted) sorted.

Fixpoint rev_ccw_list (p : point) (l : list point) : Prop :=
  match l with
  | q :: l0 => Forall_ccw q p l0 /\ rev_ccw_list p l0
  | [] => True
  end.

Lemma graham_scan_inc_rev_consec : forall p T,
  rev_consec_ccw T ->
  rev_consec_ccw (graham_scan_inc p T).
Proof.
  intros p T.
  induction T as [| t T IH]; intros Hcon; simpl; try tauto.
  destruct T as [| s T']; simpl; try tauto.
  destruct (ccw_dec s t p) as [Hccw | _].
  - apply rev_consec_ccw_cons_iff.
    split.
    + exact Hcon.
    + intros b c l0 Heq.
      inversion Heq; subst.
      apply ccw_cyclicity.
      exact Hccw.
  - apply IH.
    apply rev_consec_ccw_cons_iff in Hcon as [Htail _].
    exact Htail.
Qed.

Lemma fold_left_graham_scan_inc_rev_consec : forall l T,
  rev_consec_ccw T ->
  rev_consec_ccw
    (fold_left (fun T p => graham_scan_inc p T) l T).
Proof.
  induction l as [| p l IH]; intros T Hcon; simpl.
  - exact Hcon.
  - apply IH.
    apply graham_scan_inc_rev_consec.
    exact Hcon.
Qed.

Lemma andrew_scan_stack_rev_consec : forall l,
  rev_consec_ccw (andrew_scan_stack l).
Proof.
  intros l.
  unfold andrew_scan_stack.
  apply fold_left_graham_scan_inc_rev_consec.
  simpl; exact I.
Qed.

Lemma ccw_leftdown_skip_second : forall p q r s,
  leftdown p q ->
  leftdown q r ->
  leftdown r s ->
  ccw q p r ->
  ccw r q s ->
  ccw r p s.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma ccw_leftdown_extend_head : forall p q r s,
  leftdown p q ->
  leftdown q r ->
  leftdown r s ->
  ccw q p r ->
  ccw r q s ->
  ccw q p s.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma ccw_leftdown_forward_skip_second : forall p q r s,
  leftdown p q ->
  leftdown q r ->
  leftdown r s ->
  ccw p q r ->
  ccw q r s ->
  ccw p r s.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma ccw_leftdown_forward_extend_head : forall p q r s,
  leftdown p q ->
  leftdown q r ->
  leftdown r s ->
  ccw p q r ->
  ccw q r s ->
  ccw p q s.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma ccw_leftdown_rev_forward_skip_second : forall p q r s,
  leftdown q p ->
  leftdown r q ->
  leftdown s r ->
  ccw p q r ->
  ccw q r s ->
  ccw p r s.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma ccw_leftdown_rev_forward_extend_head : forall p q r s,
  leftdown q p ->
  leftdown r q ->
  leftdown s r ->
  ccw p q r ->
  ccw q r s ->
  ccw p q s.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma point_xy_sorted_from_skip_head : forall p q l,
  leftdown p q ->
  point_xy_sorted_from q l ->
  point_xy_sorted_from p l.
Proof.
  intros p q l Hpq Hsorted.
  destruct l as [| r l]; simpl in *; [exact I |].
  destruct Hsorted as [Hqr Hsorted].
  split.
  - eapply leftdown_trans; eauto.
  - exact Hsorted.
Qed.

Lemma point_xy_rev_sorted_from_skip_head : forall p q l,
  leftdown q p ->
  point_xy_rev_sorted_from q l ->
  point_xy_rev_sorted_from p l.
Proof.
  intros p q l Hqp Hsorted.
  destruct l as [| r l]; simpl in *; [exact I |].
  destruct Hsorted as [Hrq Hsorted].
  split.
  - eapply leftdown_trans; eauto.
  - exact Hsorted.
Qed.

Lemma rev_consec_ccw_skip_second : forall p q l,
  point_xy_sorted_from p (q :: l) ->
  rev_consec_ccw (p :: q :: l) ->
  rev_consec_ccw (p :: l).
Proof.
  intros p q l Hsorted Hcon.
  destruct l as [| r l]; simpl in *; [tauto |].
  destruct l as [| s l]; simpl in *; [tauto |].
  destruct Hsorted as [Hpq [Hqr [Hrs _]]].
  destruct Hcon as [Hqpr [Hrqs Htail]].
  split.
  - eapply ccw_leftdown_skip_second; eauto.
  - exact Htail.
Qed.

Lemma rev_consec_ccw_skip_third : forall p q r l,
  point_xy_sorted_from p (q :: r :: l) ->
  rev_consec_ccw (p :: q :: r :: l) ->
  rev_consec_ccw (p :: q :: l).
Proof.
  intros p q r l Hsorted Hcon.
  destruct l as [| s l]; simpl in *; [tauto |].
  destruct Hsorted as [Hpq [Hqr [Hrs Hsorted_s]]].
  destruct Hcon as [Hqpr Htail].
  destruct Htail as [Hrqs Htail].
  split.
  - eapply ccw_leftdown_extend_head; eauto.
  - apply (rev_consec_ccw_skip_second q r (s :: l)).
    + simpl. split; eauto.
    + simpl. split; eauto.
Qed.

Lemma xy_rev_consec_ccw_head_forall : forall p q l,
  point_xy_sorted_from p (q :: l) ->
  rev_consec_ccw (p :: q :: l) ->
  Forall_ccw q p l.
Proof.
  intros p q l.
  revert p q.
  induction l as [| r l IH]; intros p q Hsorted Hcon; simpl in *.
  - constructor.
  - rewrite Forall_ccw_cons_iff.
    pose proof Hsorted as Hsorted_all.
    pose proof Hcon as Hcon_all.
    destruct Hsorted as [Hpq Hsorted_q].
    destruct Hsorted_q as [Hqr Hsorted_r].
    destruct Hcon as [Hqpr _].
    split.
    + exact Hqpr.
    + apply IH.
      * simpl.
        split.
        -- exact Hpq.
        -- eapply point_xy_sorted_from_skip_head; eauto.
      * eapply rev_consec_ccw_skip_third.
        -- exact Hsorted_all.
        -- exact Hcon_all.
Qed.


(** Convexity := any three points constitute a clockwise relation *)
(** convex
 ** is_convex : consec_ccw + point_xy_sorted -> ccw_list
*)
Lemma xy_consec_ccw_to_ccw_list : forall p sorted,
  point_xy_sorted_from p sorted ->
  rev_consec_ccw (p :: sorted) ->
  rev_ccw_list p sorted.
Proof.
  intros p sorted.
  revert p.
  induction sorted as [| q sorted IH]; intros p Hsorted Hcon; simpl.
  - exact I.
  - split.
    + apply xy_rev_consec_ccw_head_forall; assumption.
    + destruct Hsorted as [Hpq Hsorted_q].
      apply IH.
      * eapply point_xy_sorted_from_skip_head; eauto.
      * eapply rev_consec_ccw_skip_second.
        -- simpl. split; eauto.
        -- exact Hcon.
Qed.

Lemma consec_ccw_skip_second : forall p q l,
  point_xy_sorted_from p (q :: l) ->
  consec_ccw (p :: q :: l) ->
  consec_ccw (p :: l).
Proof.
  intros p q l Hsorted Hcon.
  destruct l as [| r l]; simpl in *; [tauto |].
  destruct l as [| s l]; simpl in *; [tauto |].
  destruct Hsorted as [Hpq [Hqr [Hrs _]]].
  destruct Hcon as [Hpqr [Hqrs Htail]].
  split.
  - eapply ccw_leftdown_forward_skip_second; eauto.
  - exact Htail.
Qed.

Lemma consec_ccw_skip_third : forall p q r l,
  point_xy_sorted_from p (q :: r :: l) ->
  consec_ccw (p :: q :: r :: l) ->
  consec_ccw (p :: q :: l).
Proof.
  intros p q r l Hsorted Hcon.
  destruct l as [| s l]; simpl in *; [tauto |].
  destruct Hsorted as [Hpq [Hqr [Hrs Hsorted_s]]].
  destruct Hcon as [Hpqr Htail].
  destruct Htail as [Hqrs Htail].
  split.
  - eapply ccw_leftdown_forward_extend_head; eauto.
  - apply (consec_ccw_skip_second q r (s :: l)).
    + simpl. split; eauto.
    + simpl. split; eauto.
Qed.

Lemma xy_consec_ccw_head_forall : forall p q l,
  point_xy_sorted_from p (q :: l) ->
  consec_ccw (p :: q :: l) ->
  Forall_ccw p q l.
Proof.
  intros p q l.
  revert p q.
  induction l as [| r l IH]; intros p q Hsorted Hcon; simpl in *.
  - constructor.
  - rewrite Forall_ccw_cons_iff.
    pose proof Hsorted as Hsorted_all.
    pose proof Hcon as Hcon_all.
    destruct Hsorted as [Hpq Hsorted_q].
    destruct Hsorted_q as [Hqr Hsorted_r].
    destruct Hcon as [Hpqr _].
    split.
    + exact Hpqr.
    + apply IH.
      * simpl.
        split.
        -- exact Hpq.
        -- eapply point_xy_sorted_from_skip_head; eauto.
      * eapply consec_ccw_skip_third.
        -- exact Hsorted_all.
        -- exact Hcon_all.
Qed.

Lemma xy_consec_ccw_to_ccw_list_forward : forall p sorted,
  point_xy_sorted_from p sorted ->
  consec_ccw (p :: sorted) ->
  ccw_list p sorted.
Proof.
  intros p sorted.
  revert p.
  induction sorted as [| q sorted IH]; intros p Hsorted Hcon; simpl.
  - exact I.
  - split.
    + apply xy_consec_ccw_head_forall; assumption.
    + destruct Hsorted as [Hpq Hsorted_q].
      apply IH.
      * eapply point_xy_sorted_from_skip_head; eauto.
      * eapply consec_ccw_skip_second.
        -- simpl. split; eauto.
        -- exact Hcon.
Qed.

Lemma xy_consec_ccw_to_ccw_convex : forall p sorted,
  point_xy_sorted_from p sorted ->
  consec_ccw (p :: sorted) ->
  ccw_convex (p :: sorted).
Proof.
  intros p sorted Hsorted Hcon.
  apply ccw_convex_spec_simple.
  - apply xy_consec_ccw_to_ccw_list_forward; assumption.
  - apply consec_ccw_cons_iff in Hcon.
    tauto.
Qed.

Lemma rev_sorted_consec_ccw_skip_second : forall p q l,
  point_xy_rev_sorted_from p (q :: l) ->
  consec_ccw (p :: q :: l) ->
  consec_ccw (p :: l).
Proof.
  intros p q l Hsorted Hcon.
  destruct l as [| r l]; simpl in *; [tauto |].
  destruct l as [| s l]; simpl in *; [tauto |].
  destruct Hsorted as [Hqp [Hrq [Hsr _]]].
  destruct Hcon as [Hpqr [Hqrs Htail]].
  split.
  - eapply ccw_leftdown_rev_forward_skip_second; eauto.
  - exact Htail.
Qed.

Lemma rev_sorted_consec_ccw_skip_third : forall p q r l,
  point_xy_rev_sorted_from p (q :: r :: l) ->
  consec_ccw (p :: q :: r :: l) ->
  consec_ccw (p :: q :: l).
Proof.
  intros p q r l Hsorted Hcon.
  destruct l as [| s l]; simpl in *; [tauto |].
  destruct Hsorted as [Hqp [Hrq [Hsr Hsorted_s]]].
  destruct Hcon as [Hpqr Htail].
  destruct Htail as [Hqrs Htail].
  split.
  - eapply ccw_leftdown_rev_forward_extend_head; eauto.
  - apply (rev_sorted_consec_ccw_skip_second q r (s :: l)).
    + simpl. split; eauto.
    + simpl. split; eauto.
Qed.

Lemma rev_sorted_consec_ccw_head_forall : forall p q l,
  point_xy_rev_sorted_from p (q :: l) ->
  consec_ccw (p :: q :: l) ->
  Forall_ccw p q l.
Proof.
  intros p q l.
  revert p q.
  induction l as [| r l IH]; intros p q Hsorted Hcon; simpl in *.
  - constructor.
  - rewrite Forall_ccw_cons_iff.
    pose proof Hsorted as Hsorted_all.
    pose proof Hcon as Hcon_all.
    destruct Hsorted as [Hqp Hsorted_q].
    destruct Hsorted_q as [Hrq Hsorted_r].
    destruct Hcon as [Hpqr _].
    split.
    + exact Hpqr.
    + apply IH.
      * simpl.
        split.
        -- exact Hqp.
        -- eapply point_xy_rev_sorted_from_skip_head; eauto.
      * eapply rev_sorted_consec_ccw_skip_third.
        -- exact Hsorted_all.
        -- exact Hcon_all.
Qed.

Lemma rev_sorted_consec_ccw_to_ccw_list_forward : forall p sorted,
  point_xy_rev_sorted_from p sorted ->
  consec_ccw (p :: sorted) ->
  ccw_list p sorted.
Proof.
  intros p sorted.
  revert p.
  induction sorted as [| q sorted IH]; intros p Hsorted Hcon; simpl.
  - exact I.
  - split.
    + apply rev_sorted_consec_ccw_head_forall; assumption.
    + destruct Hsorted as [Hqp Hsorted_q].
      apply IH.
      * eapply point_xy_rev_sorted_from_skip_head; eauto.
      * eapply rev_sorted_consec_ccw_skip_second.
        -- simpl. split; eauto.
        -- exact Hcon.
Qed.

Lemma rev_sorted_consec_ccw_to_ccw_convex : forall p sorted,
  point_xy_rev_sorted_from p sorted ->
  consec_ccw (p :: sorted) ->
  ccw_convex (p :: sorted).
Proof.
  intros p sorted Hsorted Hcon.
  apply ccw_convex_spec_simple.
  - apply rev_sorted_consec_ccw_to_ccw_list_forward; assumption.
  - apply consec_ccw_cons_iff in Hcon.
    tauto.
Qed.

Lemma point_xy_sorted_from_app_left : forall p l1 l2,
  point_xy_sorted_from p (l1 ++ l2) ->
  point_xy_sorted_from p l1.
Proof.
  intros p l1.
  revert p.
  induction l1 as [| q l1 IH]; intros p l2 Hsorted; simpl in *.
  - exact I.
  - destruct Hsorted as [Hpq Hsorted].
    split.
    + exact Hpq.
    + apply IH with (l2 := l2).
      exact Hsorted.
Qed.

Lemma point_xy_sorted_app_left : forall l1 l2,
  point_xy_sorted (l1 ++ l2) ->
  point_xy_sorted l1.
Proof.
  intros l1 l2 Hsorted.
  destruct l1 as [| p l1]; simpl in *; [exact I |].
  eapply point_xy_sorted_from_app_left.
  exact Hsorted.
Qed.

Lemma point_xy_sorted_from_snoc : forall p l q,
  point_xy_sorted_from p l ->
  Forall (fun r => leftdown r q) (p :: l) ->
  point_xy_sorted_from p (l ++ [q]).
Proof.
  intros p l.
  revert p.
  induction l as [| r l IH]; intros p q Hsorted Hall; simpl in *.
  - rewrite Forall_cons_iff in Hall.
    tauto.
  - destruct Hsorted as [Hpr Hsorted].
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [_ Hall].
    split.
    + exact Hpr.
    + apply IH.
      * exact Hsorted.
      * exact Hall.
Qed.

Lemma point_xy_sorted_snoc : forall l p,
  point_xy_sorted l ->
  Forall (fun q => leftdown q p) l ->
  point_xy_sorted (l ++ [p]).
Proof.
  intros l p Hsorted Hall.
  destruct l as [| q l]; simpl in *.
  - exact I.
  - apply point_xy_sorted_from_snoc; assumption.
Qed.

Lemma point_xy_rev_sorted_from_app_left : forall p l1 l2,
  point_xy_rev_sorted_from p (l1 ++ l2) ->
  point_xy_rev_sorted_from p l1.
Proof.
  intros p l1.
  revert p.
  induction l1 as [| q l1 IH]; intros p l2 Hsorted; simpl in *.
  - exact I.
  - destruct Hsorted as [Hqp Hsorted].
    split.
    + exact Hqp.
    + apply IH with (l2 := l2).
      exact Hsorted.
Qed.

Lemma point_xy_rev_sorted_app_left : forall l1 l2,
  point_xy_rev_sorted (l1 ++ l2) ->
  point_xy_rev_sorted l1.
Proof.
  intros l1 l2 Hsorted.
  destruct l1 as [| p l1]; simpl in *; [exact I |].
  eapply point_xy_rev_sorted_from_app_left.
  exact Hsorted.
Qed.

Lemma point_xy_rev_sorted_from_snoc : forall p l q,
  point_xy_rev_sorted_from p l ->
  Forall (fun r => leftdown q r) (p :: l) ->
  point_xy_rev_sorted_from p (l ++ [q]).
Proof.
  intros p l.
  revert p.
  induction l as [| r l IH]; intros p q Hsorted Hall; simpl in *.
  - rewrite Forall_cons_iff in Hall.
    tauto.
  - destruct Hsorted as [Hrp Hsorted].
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [_ Hall].
    split.
    + exact Hrp.
    + apply IH.
      * exact Hsorted.
      * exact Hall.
Qed.

Lemma point_xy_rev_sorted_snoc : forall l p,
  point_xy_rev_sorted l ->
  Forall (fun q => leftdown p q) l ->
  point_xy_rev_sorted (l ++ [p]).
Proof.
  intros l p Hsorted Hall.
  destruct l as [| q l]; simpl in *.
  - exact I.
  - apply point_xy_rev_sorted_from_snoc; assumption.
Qed.

Lemma point_xy_sorted_rev_tail : forall p T,
  point_xy_sorted (rev (p :: T)) ->
  point_xy_sorted (rev T).
Proof.
  intros p T Hsorted.
  simpl in Hsorted.
  apply (point_xy_sorted_app_left (rev T) [p]).
  exact Hsorted.
Qed.

Lemma point_xy_rev_sorted_rev_tail : forall p T,
  point_xy_rev_sorted (rev (p :: T)) ->
  point_xy_rev_sorted (rev T).
Proof.
  intros p T Hsorted.
  simpl in Hsorted.
  apply (point_xy_rev_sorted_app_left (rev T) [p]).
  exact Hsorted.
Qed.

Lemma point_xy_sorted_rev_is_rev_sorted : forall l,
  point_xy_sorted l ->
  point_xy_rev_sorted (rev l).
Proof.
  induction l as [| p l IH]; intros Hsorted; simpl in *.
  - exact I.
  - destruct l as [| q l'].
    + simpl; exact I.
    + simpl in Hsorted.
      destruct Hsorted as [Hpq Hsorted_q].
      simpl.
      apply point_xy_rev_sorted_snoc.
      * apply IH.
        exact Hsorted_q.
      * change (rev l' ++ [q]) with (rev (q :: l')).
        apply Forall_rev.
        apply point_xy_sorted_from_leftdown_head.
        simpl.
        split; assumption.
Qed.

Lemma point_xy_rev_sorted_rev_is_sorted : forall l,
  point_xy_rev_sorted l ->
  point_xy_sorted (rev l).
Proof.
  induction l as [| p l IH]; intros Hsorted; simpl in *.
  - exact I.
  - destruct l as [| q l'].
    + simpl; exact I.
    + simpl in Hsorted.
      destruct Hsorted as [Hqp Hsorted_q].
      simpl.
      apply point_xy_sorted_snoc.
      * apply IH.
        exact Hsorted_q.
      * change (rev l' ++ [q]) with (rev (q :: l')).
        apply Forall_rev.
        apply point_xy_rev_sorted_from_leftdown_head.
        simpl.
        split; assumption.
Qed.

Lemma graham_scan_inc_Forall : forall (P : point -> Prop) p T,
  P p ->
  Forall P T ->
  Forall P (graham_scan_inc p T).
Proof.
  intros P p T.
  induction T as [| t T IH]; intros Hp HT; simpl in *.
  - constructor; [exact Hp | constructor].
  - destruct T as [| s T']; simpl in *.
    + constructor; [exact Hp | exact HT].
    + destruct (ccw_dec s t p) as [_ | _].
      * constructor; [exact Hp | exact HT].
      * apply IH.
        -- exact Hp.
        -- rewrite Forall_cons_iff in HT.
           exact (proj2 HT).
Qed.

Lemma graham_scan_inc_in : forall x p T,
  In x (graham_scan_inc p T) ->
  x = p \/ In x T.
Proof.
  intros x p T.
  revert p.
  induction T as [| t T IH]; intros p Hin; simpl in *.
  - destruct Hin as [Hx | []].
    subst p; left; reflexivity.
  - destruct T as [| s T']; simpl in *.
    + destruct Hin as [Hx | Hin].
      * subst p; left; reflexivity.
      * right; simpl; exact Hin.
    + destruct (ccw_dec s t p) as [_ | _].
      * destruct Hin as [Hx | Hin].
        -- subst p; left; reflexivity.
        -- right; simpl; exact Hin.
      * specialize (IH p Hin) as [Hx | Hin_tail].
        -- left; exact Hx.
        -- right; simpl; right; exact Hin_tail.
Qed.

Lemma fold_left_graham_scan_inc_in : forall x l T,
  In x (fold_left (fun T p => graham_scan_inc p T) l T) ->
  In x l \/ In x T.
Proof.
  intros x l.
  induction l as [| p l IH]; intros T Hin; simpl in *.
  - right.
    exact Hin.
  - specialize (IH (graham_scan_inc p T) Hin) as [Hin_l | Hin_inc].
    + left.
      simpl; right.
      exact Hin_l.
    + apply graham_scan_inc_in in Hin_inc as [Hx | Hin_T].
      * subst x.
        left.
        simpl; left; reflexivity.
      * right.
        exact Hin_T.
Qed.

Lemma andrew_scan_stack_in : forall x l,
  In x (andrew_scan_stack l) ->
  In x l.
Proof.
  intros x l Hin.
  unfold andrew_scan_stack in Hin.
  apply fold_left_graham_scan_inc_in in Hin as [Hin | Hin].
  - exact Hin.
  - contradiction.
Qed.

Lemma andrew_chain_in : forall x l,
  In x (andrew_chain l) ->
  In x l.
Proof.
  intros x l Hin.
  unfold andrew_chain in Hin.
  apply andrew_scan_stack_in.
  rewrite in_rev.
  exact Hin.
Qed.

Lemma andrew_lower_chain_in : forall x sorted,
  In x (andrew_lower_chain sorted) ->
  In x sorted.
Proof.
  intros x sorted Hin.
  unfold andrew_lower_chain in Hin.
  apply andrew_chain_in.
  exact Hin.
Qed.

Lemma andrew_upper_chain_in : forall x sorted,
  In x (andrew_upper_chain sorted) ->
  In x sorted.
Proof.
  intros x sorted Hin.
  unfold andrew_upper_chain in Hin.
  rewrite in_rev.
  apply andrew_chain_in.
  exact Hin.
Qed.

Lemma graham_scan_inc_preserves_sorted_chain : forall p T,
  Forall (fun q => leftdown q p) T ->
  point_xy_sorted (rev T) ->
  point_xy_sorted (rev (graham_scan_inc p T)).
Proof.
  intros p T.
  induction T as [| t T IH]; intros Hall Hsorted; simpl in *.
  - simpl.
    exact I.
  - destruct T as [| s T']; simpl in *.
    + rewrite Forall_cons_iff in Hall.
      destruct Hall as [Htp _].
      simpl.
      split; [exact Htp | exact I].
    + rewrite Forall_cons_iff in Hall.
      destruct Hall as [Htp Hall].
      destruct (ccw_dec s t p) as [_ | _].
      * simpl.
        apply point_xy_sorted_snoc.
        -- exact Hsorted.
        -- change ((rev T' ++ [s]) ++ [t])
             with (rev (t :: s :: T')).
           apply Forall_rev.
           constructor; assumption.
      * apply IH.
        -- exact Hall.
        -- change (rev T' ++ [s]) with (rev (s :: T')).
           apply point_xy_sorted_rev_tail with (p := t).
           exact Hsorted.
Qed.

Lemma graham_scan_inc_Forall_leftdown_next : forall p q T,
  Forall (fun r => leftdown r p) T ->
  leftdown p q ->
  Forall (fun r => leftdown r q) (graham_scan_inc p T).
Proof.
  intros p q T Hall Hpq.
  apply graham_scan_inc_Forall.
  - exact Hpq.
  - eapply Forall_impl.
    2: exact Hall.
    intros r Hrp.
    exact (leftdown_trans r p q Hrp Hpq).
Qed.

Lemma graham_scan_inc_tail_forall_leftdown_next :
  forall p q T,
  Forall (fun r => leftdown r p) T ->
  leftdown p q ->
  Forall (fun r => leftdown r q) T.
Proof.
  intros p q T Hall Hpq.
  eapply Forall_impl.
  2: exact Hall.
  intros r Hrp.
  exact (leftdown_trans r p q Hrp Hpq).
Qed.

Lemma graham_scan_inc_preserves_rev_sorted_chain : forall p T,
  Forall (fun q => leftdown p q) T ->
  point_xy_rev_sorted (rev T) ->
  point_xy_rev_sorted (rev (graham_scan_inc p T)).
Proof.
  intros p T.
  induction T as [| t T IH]; intros Hall Hsorted; simpl in *.
  - simpl.
    exact I.
  - destruct T as [| s T']; simpl in *.
    + rewrite Forall_cons_iff in Hall.
      destruct Hall as [Hpt _].
      simpl.
      split; [exact Hpt | exact I].
    + rewrite Forall_cons_iff in Hall.
      destruct Hall as [Hpt Hall].
      destruct (ccw_dec s t p) as [_ | _].
      * simpl.
        apply point_xy_rev_sorted_snoc.
        -- exact Hsorted.
        -- change ((rev T' ++ [s]) ++ [t])
             with (rev (t :: s :: T')).
           apply Forall_rev.
           constructor; assumption.
      * apply IH.
        -- exact Hall.
        -- change (rev T' ++ [s]) with (rev (s :: T')).
           apply point_xy_rev_sorted_rev_tail with (p := t).
           exact Hsorted.
Qed.

Lemma graham_scan_inc_Forall_leftdown_prev : forall p q T,
  Forall (fun r => leftdown p r) T ->
  leftdown q p ->
  Forall (fun r => leftdown q r) (graham_scan_inc p T).
Proof.
  intros p q T Hall Hqp.
  apply graham_scan_inc_Forall.
  - exact Hqp.
  - eapply Forall_impl.
    2: exact Hall.
    intros r Hpr.
    exact (leftdown_trans q p r Hqp Hpr).
Qed.

Lemma fold_left_graham_scan_inc_sorted_chain : forall l T,
  point_xy_sorted l ->
  point_xy_sorted (rev T) ->
  (match l with
   | [] => True
   | p :: _ => Forall (fun q => leftdown q p) T
   end) ->
  point_xy_sorted (rev (fold_left (fun T p => graham_scan_inc p T) l T)).
Proof.
  induction l as [| p l IH]; intros T Hsorted_l Hsorted_T Hall; simpl in *.
  - exact Hsorted_T.
  - assert (Hsorted_inc :
      point_xy_sorted (rev (graham_scan_inc p T))).
    {
      apply graham_scan_inc_preserves_sorted_chain; assumption.
    }
    destruct l as [| q l'].
    + apply IH; simpl; exact I || exact Hsorted_inc.
    + destruct Hsorted_l as [Hpq Hsorted_q].
      apply IH.
      * exact Hsorted_q.
      * exact Hsorted_inc.
      * apply graham_scan_inc_Forall_leftdown_next; assumption.
Qed.

Lemma fold_left_graham_scan_inc_rev_sorted_chain : forall l T,
  point_xy_rev_sorted l ->
  point_xy_rev_sorted (rev T) ->
  (match l with
   | [] => True
   | p :: _ => Forall (fun q => leftdown p q) T
   end) ->
  point_xy_rev_sorted (rev (fold_left (fun T p => graham_scan_inc p T) l T)).
Proof.
  induction l as [| p l IH]; intros T Hsorted_l Hsorted_T Hall; simpl in *.
  - exact Hsorted_T.
  - assert (Hsorted_inc :
      point_xy_rev_sorted (rev (graham_scan_inc p T))).
    {
      apply graham_scan_inc_preserves_rev_sorted_chain; assumption.
    }
    destruct l as [| q l'].
    + apply IH; simpl; exact I || exact Hsorted_inc.
    + destruct Hsorted_l as [Hqp Hsorted_q].
      apply IH.
      * exact Hsorted_q.
      * exact Hsorted_inc.
      * apply graham_scan_inc_Forall_leftdown_prev; assumption.
Qed.

Lemma andrew_chain_sorted : forall l,
  point_xy_sorted l ->
  point_xy_sorted (andrew_chain l).
Proof.
  intros l Hsorted.
  destruct l as [| p l].
  - simpl; exact I.
  - destruct l as [| q l'].
    + simpl; exact I.
    + simpl in Hsorted.
      destruct Hsorted as [Hpq Hsorted_tail].
      unfold andrew_chain, andrew_scan_stack.
      change (fold_left (fun T p => graham_scan_inc p T) (p :: q :: l') [])
        with (fold_left (fun T p => graham_scan_inc p T) (q :: l') [p]).
      apply fold_left_graham_scan_inc_sorted_chain.
      * exact Hsorted_tail.
      * simpl; exact I.
      * rewrite Forall_cons_iff.
        split; [exact Hpq | apply Forall_nil].
Qed.

Lemma andrew_chain_rev_sorted : forall l,
  point_xy_rev_sorted l ->
  point_xy_rev_sorted (andrew_chain l).
Proof.
  intros l Hsorted.
  destruct l as [| p l].
  - simpl; exact I.
  - destruct l as [| q l'].
    + simpl; exact I.
    + simpl in Hsorted.
      destruct Hsorted as [Hqp Hsorted_tail].
      unfold andrew_chain, andrew_scan_stack.
      change (fold_left (fun T p => graham_scan_inc p T) (p :: q :: l') [])
        with (fold_left (fun T p => graham_scan_inc p T) (q :: l') [p]).
      apply fold_left_graham_scan_inc_rev_sorted_chain.
      * exact Hsorted_tail.
      * simpl; exact I.
      * rewrite Forall_cons_iff.
        split; [exact Hqp | apply Forall_nil].
Qed.

Lemma andrew_chain_consec_ccw : forall l,
  consec_ccw (andrew_chain l).
Proof.
  intros l.
  unfold andrew_chain.
  apply gs_rev_consec_ccw_rev_consec.
  apply andrew_scan_stack_rev_consec.
Qed.

Lemma andrew_chain_ccw_convex : forall l,
  point_xy_sorted l ->
  ccw_convex (andrew_chain l).
Proof.
  intros l Hsorted.
  pose proof (andrew_chain_sorted l Hsorted) as Hchain_sorted.
  pose proof (andrew_chain_consec_ccw l) as Hchain_consec.
  destruct (andrew_chain l) as [| p chain] eqn:Hchain; simpl.
  - exact I.
  - apply xy_consec_ccw_to_ccw_convex.
    + exact Hchain_sorted.
    + exact Hchain_consec.
Qed.

Lemma andrew_chain_rev_ccw_convex : forall l,
  point_xy_rev_sorted l ->
  ccw_convex (andrew_chain l).
Proof.
  intros l Hsorted.
  pose proof (andrew_chain_rev_sorted l Hsorted) as Hchain_sorted.
  pose proof (andrew_chain_consec_ccw l) as Hchain_consec.
  destruct (andrew_chain l) as [| p chain] eqn:Hchain; simpl.
  - exact I.
  - apply rev_sorted_consec_ccw_to_ccw_convex.
    + exact Hchain_sorted.
    + exact Hchain_consec.
Qed.

Lemma andrew_lower_chain_ccw_convex : forall sorted,
  point_xy_sorted sorted ->
  ccw_convex (andrew_lower_chain sorted).
Proof.
  intros sorted Hsorted.
  unfold andrew_lower_chain.
  apply andrew_chain_ccw_convex.
  exact Hsorted.
Qed.

Lemma andrew_upper_chain_ccw_convex : forall sorted,
  point_xy_sorted sorted ->
  ccw_convex (andrew_upper_chain sorted).
Proof.
  intros sorted Hsorted.
  unfold andrew_upper_chain.
  apply andrew_chain_rev_ccw_convex.
  apply point_xy_sorted_rev_is_rev_sorted.
  exact Hsorted.
Qed.

Lemma point_xy_sorted_all_leftdown_last : forall first middle last,
  point_xy_sorted (first :: (middle ++ [last])) ->
  Forall (fun q => leftdown q last) (first :: middle ++ [last]).
Proof.
  intros first middle.
  revert first.
  induction middle as [| q middle IH]; intros first last Hsorted; simpl in *.
  - destruct Hsorted as [Hfl _].
    constructor; [exact Hfl |].
    constructor; [apply leftdown_refl | constructor].
  - destruct Hsorted as [Hfq Hsorted_q].
    specialize (IH q last Hsorted_q) as Hall_tail.
    rewrite Forall_cons_iff in Hall_tail.
    destruct Hall_tail as [Hql Hall_tail].
    constructor.
    + exact (leftdown_trans first q last Hfq Hql).
    + constructor; [exact Hql | exact Hall_tail].
Qed.

Lemma point_xy_sorted_middle_between : forall first middle last,
  point_xy_sorted (first :: (middle ++ [last])) ->
  Forall (fun q => leftdown first q /\ leftdown q last) middle.
Proof.
  intros first middle last Hsorted.
  assert (Hfirst : Forall (leftdown first) middle).
  {
    simpl in Hsorted.
    apply point_xy_sorted_from_leftdown_head in Hsorted.
    rewrite Forall_app in Hsorted.
    tauto.
  }
  assert (Hlast : Forall (fun q => leftdown q last) middle).
  {
    pose proof (point_xy_sorted_all_leftdown_last first middle last Hsorted)
      as Hall.
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [_ Hall].
    rewrite Forall_app in Hall.
    tauto.
  }
  rewrite Forall_forall in *.
  intros q Hq.
  split; [apply Hfirst | apply Hlast]; exact Hq.
Qed.

Lemma point_xy_sorted_from_fold_left_stack :
  forall first prefix cur rest,
  point_xy_sorted_from first (prefix ++ cur :: rest) ->
  Forall (fun q => leftdown q cur)
    (fold_left (fun T p => graham_scan_inc p T) prefix [first]).
Proof.
  intros first prefix cur rest Hsorted.
  assert (Hall_prefix : Forall (fun q => leftdown q cur) (first :: prefix)).
  {
    pose proof (point_xy_sorted_app_left
                  (first :: prefix ++ [cur]) rest) as Happ.
    simpl in Happ.
    assert (Hsorted_prefix : point_xy_sorted (first :: prefix ++ [cur])).
    {
      apply Happ.
      replace ((prefix ++ [cur]) ++ rest)
        with (prefix ++ cur :: rest) by (rewrite <- app_assoc; reflexivity).
      exact Hsorted.
    }
    pose proof (point_xy_sorted_all_leftdown_last
                  first prefix cur Hsorted_prefix) as Hall.
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [Hfirst Hall_tail].
    rewrite Forall_app in Hall_tail.
    destruct Hall_tail as [Hprefix _].
    constructor; [exact Hfirst | exact Hprefix].
  }
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hall_prefix.
  apply fold_left_graham_scan_inc_in in Hq as [Hq | Hq].
  - simpl.
    right.
    exact Hq.
  - destruct Hq as [Hq | []].
    subst q.
    simpl; left; reflexivity.
Qed.

Lemma point_xy_rev_sorted_middle_between : forall first middle last,
  point_xy_rev_sorted (last :: (middle ++ [first])) ->
  Forall (fun q => leftdown first q /\ leftdown q last) middle.
Proof.
  intros first middle last Hsorted.
  pose proof (point_xy_rev_sorted_rev_is_sorted
                (last :: (middle ++ [first])) Hsorted) as Hrev_sorted.
  simpl in Hrev_sorted.
  rewrite rev_app_distr in Hrev_sorted.
  simpl in Hrev_sorted.
  change (first :: rev middle ++ [last]) with
    (first :: (rev middle ++ [last])) in Hrev_sorted.
  pose proof (point_xy_sorted_middle_between first (rev middle) last
                Hrev_sorted) as Hbetween_rev.
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hbetween_rev.
  rewrite <- in_rev.
  exact Hq.
Qed.

Lemma ccw_anchor_between_trans : forall first q last r,
  leftdown first q ->
  leftdown q last ->
  leftdown first r ->
  leftdown r last ->
  ccw first q last ->
  ccw first last r ->
  ccw first q r.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma ccw_lower_last_upper : forall first q last r,
  leftdown first q ->
  leftdown q last ->
  leftdown first r ->
  leftdown r last ->
  ccw first q last ->
  ccw first last r ->
  ccw q last r.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma point_in_tri_when_baseline_side_flips :
  forall first q cur a,
  leftdown first q ->
  leftdown q cur ->
  leftdown cur a ->
  ccw first cur q ->
  ~ ccw first a q ->
  point_in_triangle q a cur first.
Proof.
  unfold leftdown, x, y, point_in_triangle, ccw,
         Geo_Vec.left_than, Geo_Vec.left_equal,
         colinear, Geo_Vec.parallel, at_mid,
         Geo_Vec.backward_or_perp, Geo_Vec.cross_prod,
         Geo_Vec.dot_prod, build_vec.
  simpl; intros; left; repeat split; nia.
Qed.

Lemma ccw_baseline_side_after_nonleft_turn :
  forall first q cur a,
  leftdown first q ->
  leftdown q cur ->
  leftdown cur a ->
  ~ ccw first cur a ->
  ccw first cur q ->
  ccw first a q.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma ccw_anchor_side_trans :
  forall first b cur q,
  leftdown first q ->
  leftdown q cur ->
  leftdown first b ->
  leftdown b cur ->
  ccw first b cur ->
  ccw first cur q ->
  ccw first b q.
Proof.
  intros first b cur q Hfirst_q Hq_cur Hfirst_b Hb_cur Hbcur Hcurq.
  eapply ccw_anchor_between_trans with (last := cur); eauto.
Qed.

Lemma baseline_left_equal_not_ccw : forall first last q,
  Geo_Vec.left_equal (build_vec first last) (build_vec first q) ->
  ~ ccw first last q.
Proof.
  unfold ccw, Geo_Vec.left_than, Geo_Vec.left_equal,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma not_ccw_baseline_left_equal : forall first last q,
  ~ ccw first last q ->
  Geo_Vec.left_equal (build_vec first last) (build_vec first q).
Proof.
  unfold ccw, Geo_Vec.left_than, Geo_Vec.left_equal,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma opposite_left_equal_colinear : forall p q r,
  Geo_Vec.left_equal (build_vec p r) (build_vec p q) ->
  Geo_Vec.left_equal (build_vec r p) (build_vec r q) ->
  colinear q p r.
Proof.
  unfold Geo_Vec.left_equal, Geo_Vec.left_than,
         colinear, Geo_Vec.parallel, Geo_Vec.cross_prod,
         build_vec.
  simpl; intros; nia.
Qed.

Lemma leftdown_colinear_between_at_mid : forall p q r,
  colinear q p r ->
  leftdown p q ->
  leftdown q r ->
  at_mid q p r.
Proof.
  unfold colinear, Geo_Vec.parallel, leftdown,
         at_mid, Geo_Vec.backward_or_perp,
         Geo_Vec.cross_prod, Geo_Vec.dot_prod, build_vec.
  simpl.
  intros [px py] [qx qy] [rx ry] Hcol Hpq Hqr.
  simpl in *.
  destruct Hpq as [Hpqx | [Hpqx Hpqy]];
  destruct Hqr as [Hqrx | [Hqrx Hqry]].
  - assert (Hcol' :
        (px - qx) * (ry - qy) = (py - qy) * (rx - qx)) by nia.
    assert (Hdot :
            (rx - qx) *
              ((px - qx) * (rx - qx) +
               (py - qy) * (ry - qy)) =
            (px - qx) *
              ((rx - qx) * (rx - qx) +
               (ry - qy) * (ry - qy))).
    {
      replace ((rx - qx) *
                 ((px - qx) * (rx - qx) +
                  (py - qy) * (ry - qy)))
        with ((px - qx) * (rx - qx) * (rx - qx) +
              (py - qy) * (rx - qx) * (ry - qy)) by ring.
      rewrite <- Hcol'.
      ring.
    }
    pose proof (Z.square_nonneg (rx - qx)) as Hsqx.
    pose proof (Z.square_nonneg (ry - qy)) as Hsqy.
    assert (0 <= (rx - qx) * (rx - qx) +
                 (ry - qy) * (ry - qy)) by nia.
    nia.
  - assert (ry = qy) by nia.
    nia.
  - assert (py = qy) by nia.
    nia.
  - nia.
Qed.

Lemma upper_point_popped_by_lower_point : forall first t q a last,
  leftdown first t ->
  leftdown t q ->
  leftdown q a ->
  leftdown a last ->
  ~ ccw first last t ->
  ccw first last q ->
  ~ ccw first last a ->
  ~ ccw t q a.
Proof.
  unfold leftdown, x, y, ccw, Geo_Vec.left_than,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma consec_ccw_append_shared :
  forall prefix last suffix,
  consec_ccw (prefix ++ [last]) ->
  consec_ccw (last :: suffix) ->
  (forall pre prev u rest,
      prefix = pre ++ [prev] ->
      suffix = u :: rest ->
      ccw prev last u) ->
  consec_ccw (prefix ++ last :: suffix).
Proof.
  induction prefix as [| a prefix IH]; intros last suffix Hprefix Hsuffix Hbridge.
  - simpl.
    exact Hsuffix.
  - simpl in *.
    apply consec_ccw_cons_iff.
    split.
    + apply IH.
      * apply consec_ccw_cons_iff in Hprefix.
        tauto.
      * exact Hsuffix.
      * intros pre prev u rest Hpre Hsuf.
        apply (Hbridge (a :: pre) prev u rest).
        -- simpl. rewrite Hpre. reflexivity.
        -- exact Hsuf.
    + intros b c l0 Htail.
      apply consec_ccw_cons_iff in Hprefix as [_ Hhead].
      destruct prefix as [| b0 prefix'].
      * simpl in Htail.
        destruct suffix as [| u suffix']; [discriminate |].
        pose proof (Hbridge [] a u suffix' eq_refl eq_refl) as Hccw.
        inversion Htail; subst.
        exact Hccw.
      * destruct prefix' as [| c0 prefix''].
        -- inversion Htail; subst.
           apply (Hhead b c []).
           reflexivity.
        -- inversion Htail; subst.
           apply (Hhead b c (prefix'' ++ [last])).
           reflexivity.
Qed.

Lemma andrew_hull_convex_from_ccw_merge :
  forall sorted lower upper,
  ccw_convex (andrew_ccw_merge sorted lower upper) ->
  rev_ccw_convex (andrew_merge sorted lower upper).
Proof.
  intros sorted lower upper Hconv.
  unfold andrew_merge.
  apply gs_ccw_convex_rev_to_rev_ccw_convex.
  rewrite rev_involutive.
  exact Hconv.
Qed.

Lemma andrew_hull_max_singleton_counterexample : forall p,
  point_xy_sorted [p] /\
  ~ is_max_hull'_edges (andrew_hull [p]) [p].
Proof.
  intros p.
  split.
  - simpl; exact I.
  - simpl.
    unfold is_max_hull'_edges.
    rewrite Forall_cons_iff.
    tauto.
Qed.


(** Maximality := contain all points *)
Lemma graham_scan_inc_preserves_bottom : forall p stack bottom,
  exists stack',
    graham_scan_inc p (stack ++ [bottom]) = stack' ++ [bottom].
Proof.
  intros p stack.
  induction stack as [| a stack IH]; intros bottom.
  - simpl.
    exists [p].
    reflexivity.
  - destruct stack as [| b stack']; simpl.
    + destruct (ccw_dec bottom a p) as [_ | _].
      * exists [p; a].
        reflexivity.
      * exists [p].
        reflexivity.
    + destruct (ccw_dec b a p) as [_ | _].
      * exists (p :: a :: b :: stack').
        reflexivity.
      * apply IH.
Qed.

Lemma graham_scan_inc_preserves_bottom_with_head : forall p stack bottom,
  exists stack',
    graham_scan_inc p (stack ++ [bottom]) = p :: stack' ++ [bottom].
Proof.
  intros p stack.
  induction stack as [| a stack IH]; intros bottom.
  - simpl.
    exists [].
    reflexivity.
  - destruct stack as [| b stack']; simpl.
    + destruct (ccw_dec bottom a p) as [_ | _].
      * exists [a].
        reflexivity.
      * exists [].
        reflexivity.
    + destruct (ccw_dec b a p) as [_ | _].
      * exists (a :: b :: stack').
        reflexivity.
      * apply IH.
Qed.

Lemma fold_left_graham_scan_inc_preserves_bottom : forall l stack bottom,
  (exists stack', stack = stack' ++ [bottom]) ->
  exists stack',
    fold_left (fun T p => graham_scan_inc p T) l stack =
      stack' ++ [bottom].
Proof.
  induction l as [| p l IH]; intros stack bottom [stack' Hstack].
  - exists stack'.
    exact Hstack.
  - simpl.
    apply IH.
    subst stack.
    apply graham_scan_inc_preserves_bottom.
Qed.

Lemma andrew_scan_stack_preserves_first : forall p l,
  exists stack',
    andrew_scan_stack (p :: l) = stack' ++ [p].
Proof.
  intros p l.
  unfold andrew_scan_stack.
  simpl.
  apply fold_left_graham_scan_inc_preserves_bottom.
  exists [].
  reflexivity.
Qed.

Lemma graham_scan_inc_has_head : forall p stack,
  exists stack',
    graham_scan_inc p stack = p :: stack'.
Proof.
  intros p stack.
  induction stack as [| a stack IH]; simpl.
  - exists [].
    reflexivity.
  - destruct stack as [| b stack']; simpl.
    + exists [a].
      reflexivity.
    + destruct (ccw_dec b a p) as [_ | _].
      * exists (a :: b :: stack').
        reflexivity.
      * apply IH.
Qed.

Lemma andrew_scan_stack_has_last_head : forall l p,
  exists stack',
    andrew_scan_stack (l ++ [p]) = p :: stack'.
Proof.
  intros l p.
  unfold andrew_scan_stack.
  rewrite fold_left_app.
  simpl.
  apply graham_scan_inc_has_head.
Qed.

Lemma andrew_chain_starts_first : forall p l,
  exists chain',
    andrew_chain (p :: l) = p :: chain'.
Proof.
  intros p l.
  unfold andrew_chain.
  destruct (andrew_scan_stack_preserves_first p l) as [stack' Hstack].
  rewrite Hstack.
  rewrite rev_app_distr.
  simpl.
  exists (rev stack').
  reflexivity.
Qed.

Lemma andrew_chain_ends_last : forall l p,
  exists chain',
    andrew_chain (l ++ [p]) = chain' ++ [p].
Proof.
  intros l p.
  unfold andrew_chain.
  destruct (andrew_scan_stack_has_last_head l p) as [stack' Hstack].
  rewrite Hstack.
  simpl.
  exists (rev stack').
  reflexivity.
Qed.

Lemma andrew_scan_stack_endpoints : forall first middle last,
  exists stack_mid,
    andrew_scan_stack (first :: (middle ++ [last])) =
      last :: stack_mid ++ [first].
Proof.
  intros first middle last.
  destruct (andrew_scan_stack_preserves_first first middle) as [stack' Hstack].
  unfold andrew_scan_stack in *.
  simpl in Hstack.
  change (first :: (middle ++ [last])) with ((first :: middle) ++ [last]).
  rewrite fold_left_app.
  simpl.
  rewrite Hstack.
  apply graham_scan_inc_preserves_bottom_with_head.
Qed.

Lemma point_list_non_singleton_first_last : forall sorted,
  point_list_non_singleton sorted ->
  exists first middle last,
    sorted = first :: (middle ++ [last]).
Proof.
  intros sorted [first [second [rest Hsorted]]].
  subst sorted.
  revert first second.
  induction rest as [| a rest IH]; intros first second.
  - exists first, [], second.
    reflexivity.
  - specialize (IH second a) as [head [middle [last Hshape]]].
    exists first, (head :: middle), last.
    rewrite Hshape.
    reflexivity.
Qed.

Lemma andrew_lower_chain_endpoints : forall first middle last,
  exists lower_mid,
    andrew_lower_chain (first :: (middle ++ [last])) =
      first :: (lower_mid ++ [last]).
Proof.
  intros first middle last.
  unfold andrew_lower_chain, andrew_chain.
  destruct (andrew_scan_stack_endpoints first middle last) as [stack_mid Hstack].
  rewrite Hstack.
  simpl.
  rewrite rev_app_distr.
  simpl.
  exists (rev stack_mid).
  reflexivity.
Qed.

Lemma andrew_upper_chain_endpoints : forall first middle last,
  exists upper_mid,
    andrew_upper_chain (first :: (middle ++ [last])) =
      last :: (upper_mid ++ [first]).
Proof.
  intros first middle last.
  unfold andrew_upper_chain, andrew_chain.
  replace (rev (first :: (middle ++ [last])))
    with (last :: (rev middle ++ [first])).
  2: {
    simpl.
    rewrite rev_app_distr.
    simpl.
    reflexivity.
  }
  destruct (andrew_scan_stack_endpoints last (rev middle) first)
    as [stack_mid Hstack].
  rewrite Hstack.
  simpl.
  rewrite rev_app_distr.
  simpl.
  exists (rev stack_mid).
  reflexivity.
Qed.

Lemma andrew_lower_chain_as_graham_scan :
  forall first middle last,
  andrew_lower_chain (first :: middle ++ [last]) =
  rev (graham_scan (rev (first :: middle ++ [last]))).
Proof.
  intros first middle last.
  unfold andrew_lower_chain, andrew_chain, andrew_scan_stack.
  simpl.
  rewrite fold_left_graham_scan_inc_cons.
  reflexivity.
Qed.

Lemma andrew_upper_chain_as_graham_scan :
  forall first middle last,
  andrew_upper_chain (first :: middle ++ [last]) =
  rev (graham_scan (first :: middle ++ [last])).
Proof.
  intros first middle last.
  unfold andrew_upper_chain, andrew_chain, andrew_scan_stack.
  simpl.
  rewrite rev_app_distr.
  simpl.
  rewrite fold_left_graham_scan_inc_cons.
  replace (rev (last :: rev middle ++ [first]))
    with (first :: middle ++ [last]).
  2: {
    simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_involutive.
    reflexivity.
  }
  reflexivity.
Qed.

Lemma andrew_lower_chain_stack_shape :
  forall first middle last lower_mid,
  andrew_lower_chain (first :: middle ++ [last]) =
    first :: lower_mid ++ [last] ->
  andrew_scan_stack (first :: middle ++ [last]) =
    last :: rev lower_mid ++ [first].
Proof.
  intros first middle last lower_mid Hchain.
  unfold andrew_lower_chain, andrew_chain in Hchain.
  apply (f_equal (@rev point)) in Hchain.
  rewrite rev_involutive in Hchain.
  simpl in Hchain.
  rewrite rev_app_distr in Hchain.
  simpl in Hchain.
  exact Hchain.
Qed.

Lemma andrew_upper_chain_stack_shape :
  forall first middle last upper_mid,
  andrew_upper_chain (first :: middle ++ [last]) =
    last :: upper_mid ++ [first] ->
  andrew_scan_stack (rev (first :: middle ++ [last])) =
    first :: rev upper_mid ++ [last].
Proof.
  intros first middle last upper_mid Hchain.
  unfold andrew_upper_chain, andrew_chain in Hchain.
  apply (f_equal (@rev point)) in Hchain.
  rewrite rev_involutive in Hchain.
  simpl in Hchain.
  rewrite rev_app_distr in Hchain.
  simpl in Hchain.
  rewrite rev_app_distr in Hchain.
  simpl in Hchain.
  replace (rev (first :: middle ++ [last]))
    with (last :: rev middle ++ [first]).
  2: {
    simpl.
    rewrite rev_app_distr.
    simpl.
    reflexivity.
  }
  exact Hchain.
Qed.

Lemma removelast_snoc : forall {A : Type} (l : list A) x,
  removelast (l ++ [x]) = l.
Proof.
  intros A l.
  induction l as [| a l IH]; intros x; simpl.
  - reflexivity.
  - destruct l as [| b l']; simpl.
    + reflexivity.
    + f_equal.
      apply IH.
Qed.

Lemma andrew_ccw_merge_endpoints :
  forall sorted first middle last lower upper lower_mid upper_mid,
  sorted = first :: (middle ++ [last]) ->
  lower = first :: (lower_mid ++ [last]) ->
  upper = last :: (upper_mid ++ [first]) ->
  andrew_ccw_merge sorted lower upper =
    first :: (lower_mid ++ last :: upper_mid).
Proof.
  intros sorted first middle last lower upper lower_mid upper_mid
    Hsorted Hlower Hupper.
  subst sorted lower upper.
  unfold andrew_ccw_merge.
  destruct middle as [| m middle].
  - change (removelast (first :: (lower_mid ++ [last])) ++
            removelast (last :: (upper_mid ++ [first])) =
            first :: (lower_mid ++ last :: upper_mid)).
    change (first :: (lower_mid ++ [last]))
      with ((first :: lower_mid) ++ [last]).
    change (last :: (upper_mid ++ [first]))
      with ((last :: upper_mid) ++ [first]).
    rewrite !removelast_snoc.
    reflexivity.
  - change (removelast (first :: (lower_mid ++ [last])) ++
            removelast (last :: (upper_mid ++ [first])) =
            first :: (lower_mid ++ last :: upper_mid)).
    change (first :: (lower_mid ++ [last]))
      with ((first :: lower_mid) ++ [last]).
    change (last :: (upper_mid ++ [first]))
      with ((last :: upper_mid) ++ [first]).
    rewrite !removelast_snoc.
    reflexivity.
Qed.

Lemma point_in_hull_edges_two_points_endpoints : forall p q,
  point_in_hull_edges p [q; p] /\
  point_in_hull_edges q [q; p].
Proof.
  intros p q.
  simpl.
  split; split;
    unfold colinear, at_mid, Geo_Vec.parallel,
           Geo_Vec.backward_or_perp,
           Geo_Vec.cross_prod, Geo_Vec.dot_prod, build_vec;
    simpl; nia.
Qed.

Lemma andrew_hull_max_two_points : forall p q,
  is_max_hull'_edges (andrew_hull [p; q]) [p; q].
Proof.
  intros p q.
  simpl.
  unfold is_max_hull'_edges.
  rewrite !Forall_cons_iff.
  rewrite Forall_nil_iff.
  pose proof point_in_hull_edges_two_points_endpoints p q as [Hp Hq].
  tauto.
Qed.

Lemma andrew_hull_merge_shape : forall first middle last,
  exists lower_mid upper_mid,
    andrew_hull (first :: (middle ++ [last])) =
      rev (first :: (lower_mid ++ last :: upper_mid)) /\
    andrew_lower_chain (first :: (middle ++ [last])) =
      first :: (lower_mid ++ [last]) /\
    andrew_upper_chain (first :: (middle ++ [last])) =
      last :: (upper_mid ++ [first]).
Proof.
  intros first middle last.
  destruct (andrew_lower_chain_endpoints first middle last)
    as [lower_mid Hlower].
  destruct (andrew_upper_chain_endpoints first middle last)
    as [upper_mid Hupper].
  exists lower_mid, upper_mid.
  assert (Hmerge :
    andrew_ccw_merge
      (first :: (middle ++ [last]))
      (andrew_lower_chain (first :: (middle ++ [last])))
      (andrew_upper_chain (first :: (middle ++ [last]))) =
      first :: (lower_mid ++ last :: upper_mid)).
  {
    eapply andrew_ccw_merge_endpoints; eauto.
  }
  split.
  - unfold andrew_hull, andrew_merge.
    rewrite Hmerge.
    reflexivity.
  - split; assumption.
Qed.

Theorem andrew_hull_convex : forall sorted,
  point_xy_sorted sorted ->
  rev_ccw_convex (andrew_hull sorted).
Proof.
  intros sorted Hsorted.
  destruct sorted as [| p sorted'].
  - simpl.
    apply gs_ccw_convex_rev_to_rev_ccw_convex.
    simpl; exact I.
  - destruct sorted' as [| q rest].
    + simpl.
      apply gs_ccw_convex_rev_to_rev_ccw_convex.
      simpl; tauto.
    + assert (Hnonsingleton : point_list_non_singleton (p :: q :: rest)).
      {
        exists p, q, rest.
        reflexivity.
      }
      destruct (point_list_non_singleton_first_last
                  (p :: q :: rest) Hnonsingleton)
        as [first [middle [last Hshape]]].
      rewrite Hshape in Hsorted |- *.
      destruct (andrew_lower_chain_endpoints first middle last)
        as [lower_mid Hlower].
      destruct (andrew_upper_chain_endpoints first middle last)
        as [upper_mid Hupper].
      unfold andrew_hull.
      apply andrew_hull_convex_from_ccw_merge.
      assert (Hmerge :
        andrew_ccw_merge
          (first :: middle ++ [last])
          (andrew_lower_chain (first :: middle ++ [last]))
          (andrew_upper_chain (first :: middle ++ [last])) =
          first :: lower_mid ++ last :: upper_mid).
      {
        eapply andrew_ccw_merge_endpoints; eauto.
      }
      rewrite Hmerge.
      pose proof (andrew_lower_chain_ccw_convex
                    (first :: middle ++ [last]) Hsorted) as Hlower_conv.
      pose proof (andrew_upper_chain_ccw_convex
                    (first :: middle ++ [last]) Hsorted) as Hupper_conv.
      pose proof (andrew_chain_sorted
                    (first :: middle ++ [last]) Hsorted) as Hlower_sorted.
      unfold andrew_chain in Hlower_sorted.
      fold (andrew_chain (first :: middle ++ [last])) in Hlower_sorted.
      change (andrew_chain (first :: middle ++ [last]))
        with (andrew_lower_chain (first :: middle ++ [last]))
        in Hlower_sorted.
      rewrite Hlower in Hlower_sorted.
      pose proof (andrew_chain_rev_sorted
                    (rev (first :: middle ++ [last]))
                    (point_xy_sorted_rev_is_rev_sorted
                       (first :: middle ++ [last]) Hsorted))
        as Hupper_sorted.
      change (andrew_chain (rev (first :: middle ++ [last])))
        with (andrew_upper_chain (first :: middle ++ [last]))
        in Hupper_sorted.
      rewrite Hupper in Hupper_sorted.
      rewrite Hlower in Hlower_conv.
      rewrite Hupper in Hupper_conv.
      pose proof (point_xy_sorted_middle_between
                    first lower_mid last Hlower_sorted) as Hlower_between.
      pose proof (point_xy_rev_sorted_middle_between
                    first upper_mid last Hupper_sorted) as Hupper_between.
      pose proof (andrew_chain_consec_ccw
                    (first :: middle ++ [last])) as Hlower_consec.
      change (andrew_chain (first :: middle ++ [last]))
        with (andrew_lower_chain (first :: middle ++ [last]))
        in Hlower_consec.
      rewrite Hlower in Hlower_consec.
      pose proof (andrew_chain_consec_ccw
                    (rev (first :: middle ++ [last]))) as Hupper_consec.
      change (andrew_chain (rev (first :: middle ++ [last])))
        with (andrew_upper_chain (first :: middle ++ [last]))
        in Hupper_consec.
      rewrite Hupper in Hupper_consec.
      pose proof (ccw_convex_app_comm (last :: upper_mid) [first]
                    Hupper_conv) as Hupper_rot.
      simpl in Hlower_conv.
      destruct Hlower_conv as [Hlower_list _].
      simpl in Hupper_rot.
      destruct Hupper_rot as [Hupper_first_list _].
      assert (Hlower_first_last :
        forall q, In q lower_mid -> ccw first q last).
      {
        intros a Ha.
        rewrite ccw_list_app_iff in Hlower_list.
        destruct Hlower_list as [_ [_ Hcross]].
        apply Hcross; [exact Ha | simpl; auto].
      }
      assert (Hupper_first_last :
        forall q, In q upper_mid -> ccw first last q).
      {
        simpl in Hupper_first_list.
        destruct Hupper_first_list as [Hforall _].
        rewrite Forall_ccw_forall in Hforall.
        intros a Ha.
        apply Hforall.
        exact Ha.
      }
      apply ccw_convex_spec.
      * apply g_ccw_ccw_list.
        apply ccw_list_app_iff.
        split.
        -- rewrite ccw_list_app_iff in Hlower_list; tauto.
        -- split.
           ++ exact Hupper_first_list.
           ++ intros a b Ha Hb.
           destruct Hb as [Hb | Hb].
           ** subst b.
              apply Hlower_first_last.
              exact Ha.
           ** apply ccw_anchor_between_trans with (last := last).
              --- rewrite Forall_forall in Hlower_between.
                 exact (proj1 (Hlower_between a Ha)).
              --- rewrite Forall_forall in Hlower_between.
                 exact (proj2 (Hlower_between a Ha)).
              --- rewrite Forall_forall in Hupper_between.
                 exact (proj1 (Hupper_between b Hb)).
              --- rewrite Forall_forall in Hupper_between.
                 exact (proj2 (Hupper_between b Hb)).
              --- apply Hlower_first_last.
                 exact Ha.
              --- apply Hupper_first_last.
                 exact Hb.
      * apply (consec_ccw_append_shared
                 (first :: lower_mid) last upper_mid).
        -- exact Hlower_consec.
        -- apply (consec_ccw_app_inv1 (last :: upper_mid) [first]).
           change ((last :: upper_mid) ++ [first])
             with (last :: upper_mid ++ [first]).
           exact Hupper_consec.
        -- intros pre prev u tail Hprefix Hsuffix.
           assert (Hu : In u upper_mid).
           {
             rewrite Hsuffix.
             simpl; auto.
           }
           destruct pre as [| a pre'].
           ++ simpl in Hprefix.
              inversion Hprefix; subst.
              apply Hupper_first_last.
              exact Hu.
           ++ simpl in Hprefix.
              inversion Hprefix as [[Hfirst_eq Hmid_eq]].
              subst a.
              assert (Hprev : In prev lower_mid).
              {
                rewrite Hmid_eq.
                rewrite in_app_iff.
                right; simpl; auto.
              }
              apply ccw_lower_last_upper with (first := first).
              ** rewrite Forall_forall in Hlower_between.
                 exact (proj1 (Hlower_between prev Hprev)).
              ** rewrite Forall_forall in Hlower_between.
                 exact (proj2 (Hlower_between prev Hprev)).
              ** rewrite Forall_forall in Hupper_between.
                 exact (proj1 (Hupper_between u Hu)).
              ** rewrite Forall_forall in Hupper_between.
                 exact (proj2 (Hupper_between u Hu)).
              ** apply Hlower_first_last.
                 exact Hprev.
              ** apply Hupper_first_last.
                 exact Hu.
Qed.

Lemma point_in_hull_cons_weak : forall p q p0 T,
  weak_rev_ccw_list p (p0 :: T) ->
  point_in_hull q (p :: T) ->
  point_in_hull q (p :: p0 :: T).
Proof.
  intros p q p0 T Hweak Hinh.
  destruct T as [| a T].
  - simpl in Hinh.
    contradiction.
  - pose proof (proj2 (point_in_hull_cons_iff_weak q p a p0 T Hweak))
      as Hto.
    apply Hto.
    left.
    exact Hinh.
Qed.

Lemma is_max_hull'_cons_weak : forall p p0 T L,
  weak_rev_ccw_list p (p0 :: T) ->
  is_max_hull' p T L ->
  is_max_hull' p (p0 :: T) L.
Proof.
  intros p p0 T L Hweak Hmax.
  unfold is_max_hull' in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply point_in_hull_cons_weak; [exact Hweak |].
  apply Hmax.
  exact Hq.
Qed.

Lemma point_in_tri_snoc_edge_weak : forall p q b a,
  weak_rev_ccw p b a ->
  colinear q p b ->
  at_mid q p b ->
  point_in_triangle q b a p.
Proof.
  intros p q b a Hweak Hcol Hmid.
  destruct Hweak as [Hstrict | [Hcol_ba Hmid_a]].
  - rewrite point_in_tri_cyclicity.
    eapply point_in_tri_col_mid'.
    + apply ccw_cyclicity_2.
      exact Hstrict.
    + exact Hcol.
    + exact Hmid.
  - right.
    unfold colinear, Geo_Vec.parallel,
           at_mid, Geo_Vec.backward_or_perp,
           ccw, Geo_Vec.left_than, Geo_Vec.left_equal,
           Geo_Vec.cross_prod, Geo_Vec.dot_prod, build_vec
      in *.
    simpl in *.
    nia.
Qed.

Lemma point_in_hull_snoc_weak : forall p q a CH,
  weak_rev_ccw_list p (CH ++ [a]) ->
  point_in_hull q (p :: CH) ->
  point_in_hull q (p :: CH ++ [a]).
Proof.
  intros p q a CH.
  induction CH as [| b CH IH]; intros Hweak Hinh.
  - simpl in Hinh.
    contradiction.
  - destruct CH as [| c CH'].
    + simpl in *.
      destruct Hweak as [Hfor _].
      rewrite Forall_weak_rev_ccw_cons_iff in Hfor.
      destruct Hfor as [Hba _].
      destruct Hinh as [Hcol Hmid].
      left.
      exact (point_in_tri_snoc_edge_weak p q b a Hba Hcol Hmid).
    + change (p :: b :: c :: CH' ++ [a])
        with (p :: b :: (c :: CH' ++ [a])).
      pose proof (point_in_hull_cons_iff_weak q p c b (CH' ++ [a]) Hweak)
        as [_ Hto].
      apply Hto.
      assert (Hsmall_weak : weak_rev_ccw_list p (b :: c :: CH')).
      {
        assert (Hweak' :
          weak_rev_ccw_list p ((b :: c :: CH') ++ [a] ++ [])).
        {
          rewrite app_nil_r.
          exact Hweak.
        }
        pose proof (weak_rev_ccw_list_remove_middle
                      p (b :: c :: CH') [a] [] Hweak') as Htmp.
        rewrite app_nil_r in Htmp.
        exact Htmp.
      }
      pose proof (point_in_hull_cons_iff_weak q p c b CH' Hsmall_weak)
        as [Hfrom _].
      destruct (Hfrom Hinh) as [Hsmall | Htri].
      * left.
        destruct Hweak as [_ Htail_weak].
        apply (IH Htail_weak Hsmall).
      * right.
        exact Htri.
Qed.

Lemma point_in_hull_last_weak : forall p CH a,
  weak_rev_ccw_list p (CH ++ [a]) ->
  point_in_hull a (p :: CH ++ [a]).
Proof.
  intros p CH a Hweak.
  induction CH as [| b CH IH].
  - simpl.
    unfold colinear, Geo_Vec.parallel,
           at_mid, Geo_Vec.backward_or_perp,
           Geo_Vec.cross_prod, Geo_Vec.dot_prod, build_vec.
    simpl.
    split; lia.
  - change (p :: b :: CH ++ [a]) with (p :: b :: (CH ++ [a])).
    eapply point_in_hull_cons_weak.
    + exact Hweak.
    + apply IH.
      destruct Hweak as [_ Htail_weak].
      exact Htail_weak.
Qed.

Lemma is_max_hull'_snoc_weak : forall p a CH l,
  weak_rev_ccw_list p (CH ++ [a]) ->
  is_max_hull' p CH l ->
  is_max_hull' p (CH ++ [a]) l.
Proof.
  intros p a CH l Hweak Hmax.
  unfold is_max_hull' in *.
  rewrite Forall_forall in *.
  intros q Hq.
  eapply point_in_hull_snoc_weak; eauto.
Qed.

Lemma is_max_hull'_snoc_self_weak : forall p a CH l,
  weak_rev_ccw_list p (CH ++ [a]) ->
  is_max_hull' p CH l ->
  is_max_hull' p (CH ++ [a]) (l ++ [a]).
Proof.
  intros p a CH l Hweak Hmax.
  unfold is_max_hull' in *.
  rewrite Forall_app.
  split.
  - apply is_max_hull'_snoc_weak; assumption.
  - apply Forall_cons.
    + apply point_in_hull_last_weak.
      exact Hweak.
    + apply Forall_nil.
Qed.

Lemma point_in_hull_member_weak : forall p CH q,
  weak_rev_ccw_list p CH ->
  In q CH ->
  point_in_hull q (p :: CH).
Proof.
  intros p CH.
  induction CH as [| a CH IH]; intros q Hweak Hin.
  - contradiction.
  - destruct Hin as [Hq | Hin].
    + subst q.
      apply gs_point_in_hull_new_head.
      exact Hweak.
    + destruct CH as [| b CH'].
      * contradiction.
      * apply point_in_hull_cons_weak.
        -- exact Hweak.
        -- apply IH.
           ++ exact (proj2 Hweak).
           ++ exact Hin.
Qed.

Lemma point_in_hull_pop_weak : forall p a b c l q,
  g_rev_ccw_list p (c :: b :: a :: l) ->
  ~ ccw a b c ->
  point_in_hull q (p :: c :: b :: a :: l) ->
  point_in_hull q (p :: c :: a :: l).
Proof.
  intros p a b c l q Hweak Hn Hinh.
  assert (Hmax : is_max_hull' p (c :: b :: a :: l) [q]).
  {
    unfold is_max_hull'.
    rewrite Forall_cons_iff.
    split; [exact Hinh | apply Forall_nil].
  }
  pose proof (is_max_hull'_pop'_g p a b c l [q]
                Hweak Hn Hmax) as Hmax'.
  unfold is_max_hull' in Hmax'.
  rewrite Forall_cons_iff in Hmax'.
  exact (proj1 Hmax').
Qed.

Lemma graham_scan_inc_preserves_cover_disj :
  forall first a C L,
  weak_rev_ccw_list first (a :: C) ->
  Forall
    (fun q =>
       point_in_hull q (first :: a :: C) \/
       ccw first a q)
    L ->
  Forall
    (fun q =>
       point_in_hull q
         (first :: removelast (graham_scan_inc a (C ++ [first]))) \/
       ccw first a q)
    L.
Proof.
  intros first a C.
  induction C as [| b C IH]; intros L Hweak Hcover.
  - simpl.
    exact Hcover.
  - destruct C as [| c C'].
    + simpl in *.
      destruct (ccw_dec first b a) as [Hccw | Hnccw].
      * simpl.
        exact Hcover.
      * rewrite Forall_forall in *.
        intros q Hq.
        specialize (Hcover q Hq) as [Hinh | Habove].
        -- left.
           apply (gs_point_in_hull_pop_single first a b q).
           ++ simpl in Hweak.
              destruct Hweak as [Hfor _].
              rewrite Forall_g_rev_ccw_cons_iff in Hfor.
              exact (proj1 Hfor).
           ++ exact Hnccw.
           ++ exact Hinh.
        -- right.
           exact Habove.
    + simpl in *.
      destruct (ccw_dec c b a) as [Hccw | Hnccw].
      * simpl.
        assert (Htail :
          match C' ++ [first] with
          | [] => []
          | _ :: _ => c :: removelast (C' ++ [first])
          end = c :: C').
        {
          destruct (C' ++ [first]) as [| h t] eqn:Happ.
          - destruct C'; simpl in Happ; discriminate.
          - rewrite <- Happ.
            rewrite removelast_snoc.
            reflexivity.
        }
        rewrite Htail.
        exact Hcover.
      * apply IH.
        -- pose proof (weak_rev_ccw_list_remove_middle
                         first [a] [b] (c :: C') Hweak) as Hweak'.
           simpl in Hweak'.
           exact Hweak'.
        -- rewrite Forall_forall in *.
           intros q Hq.
           specialize (Hcover q Hq) as [Hinh | Habove].
           ++ left.
              eapply point_in_hull_pop_weak.
              ** exact Hweak.
              ** exact Hnccw.
              ** exact Hinh.
           ++ right.
              exact Habove.
Qed.

Lemma lower_cover_push_candidate :
  forall first cur a C L,
  weak_rev_ccw_list first (a :: cur :: C) ->
  leftdown cur a ->
  Forall (fun q => leftdown first q /\ leftdown q cur) L ->
  Forall
    (fun q =>
       point_in_hull q (first :: cur :: C) \/
       ccw first cur q)
    L ->
  Forall
    (fun q =>
       point_in_hull q (first :: a :: cur :: C) \/
       ccw first a q)
    L.
Proof.
  intros first cur a C L Hweak Hcur_a Hbetween Hcover.
  rewrite Forall_forall in *.
  intros q Hq.
  specialize (Hcover q Hq) as [Hinh | Habove_old].
  - left.
    eapply point_in_hull_cons_weak.
    + exact Hweak.
    + exact Hinh.
  - destruct (ccw_dec first a q) as [Habove_new | Hnot_above_new].
    + right.
      exact Habove_new.
    + left.
      simpl.
      left.
      specialize (Hbetween q Hq) as [Hfirst_q Hq_cur].
      eapply point_in_tri_when_baseline_side_flips; eauto.
Qed.

Lemma lower_cover_step :
  forall first cur a C L,
  weak_rev_ccw_list first (a :: cur :: C) ->
  leftdown cur a ->
  Forall (fun q => leftdown first q /\ leftdown q cur) L ->
  Forall
    (fun q =>
       point_in_hull q (first :: cur :: C) \/
       ccw first cur q)
    L ->
  Forall
    (fun q =>
       point_in_hull q
         (first :: removelast (graham_scan_inc a ((cur :: C) ++ [first]))) \/
       ccw first a q)
    L.
Proof.
  intros first cur a C L Hweak Hcur_a Hbetween Hcover.
  apply graham_scan_inc_preserves_cover_disj.
  - exact Hweak.
  - eapply lower_cover_push_candidate; eauto.
Qed.

Lemma g_ccw_to_g_rev_ccw_rev : forall p q r,
  g_ccw p r q ->
  g_rev_ccw p q r.
Proof.
  intros p q r H.
  rewrite g_rev_ccw_iff_g_ccw_rev.
  exact H.
Qed.

Lemma g_ccw_list_to_g_rev_ccw_list_rev : forall p l,
  g_ccw_list p l ->
  g_rev_ccw_list p (rev l).
Proof.
  intros p l.
  induction l as [| a l IH]; simpl; intros Hccw.
  - exact I.
  - destruct Hccw as [Ha Htail].
    rewrite g_rev_ccw_list_app_iff.
    repeat split.
    + apply IH.
      exact Htail.
    + unfold g_rev_ccw_list.
      simpl.
      repeat constructor.
    + intros q r Hq Hr.
      simpl in Hr.
      destruct Hr as [Hr | []].
      subst r.
      rewrite Forall_forall in Ha.
      apply g_ccw_to_g_rev_ccw_rev.
      apply Ha.
      rewrite in_rev.
      exact Hq.
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

Lemma ccw_convex_tail_sort_rev : forall p l,
  leftmost p l ->
  ccw_convex (p :: l) ->
  sort p (rev l).
Proof.
  intros p l Hleft Hconv.
  simpl in Hconv.
  destruct Hconv as [Hlist _].
  split.
  - apply leftmost_rev.
    exact Hleft.
  - apply g_ccw_list_to_g_rev_ccw_list_rev.
    apply g_ccw_ccw_list.
    exact Hlist.
Qed.

Lemma weak_rev_ccw_list_of_sorted_clean_stack : forall first T,
  point_xy_sorted (rev (T ++ [first])) ->
  rev_consec_ccw (T ++ [first]) ->
  weak_rev_ccw_list first T.
Proof.
  intros first T Hsorted Hcon.
  assert (Hsorted' : point_xy_sorted (first :: rev T)).
  {
    rewrite rev_app_distr in Hsorted.
    simpl in Hsorted.
    exact Hsorted.
  }
  assert (Hcon' : consec_ccw (first :: rev T)).
  {
    replace (first :: rev T) with (rev (T ++ [first])).
    2: {
      rewrite rev_app_distr.
      reflexivity.
    }
    apply gs_rev_consec_ccw_rev_consec.
    exact Hcon.
  }
  assert (Hleft : leftmost first (rev T)).
  {
    simpl in Hsorted'.
    apply point_xy_sorted_from_leftdown_head.
    exact Hsorted'.
  }
  assert (Hconv : ccw_convex (first :: rev T)).
  {
    simpl in Hsorted'.
    apply xy_consec_ccw_to_ccw_convex; assumption.
  }
  pose proof (ccw_convex_tail_sort_rev first (rev T) Hleft Hconv)
    as [_ Hweak].
  rewrite rev_involutive in Hweak.
  exact Hweak.
Qed.

Lemma graham_scan_inc_removelast_preserves_bottom : forall p stack bottom,
  graham_scan_inc p (stack ++ [bottom]) =
    removelast (graham_scan_inc p (stack ++ [bottom])) ++ [bottom].
Proof.
  intros p stack bottom.
  destruct (graham_scan_inc_preserves_bottom p stack bottom)
    as [stack' Hstack].
  rewrite Hstack.
  rewrite removelast_snoc.
  reflexivity.
Qed.

Lemma graham_scan_inc_clean_stack_weak :
  forall first a stack,
  point_xy_sorted (rev (stack ++ [first])) ->
  Forall (fun q => leftdown q a) (stack ++ [first]) ->
  rev_consec_ccw (stack ++ [first]) ->
  weak_rev_ccw_list first
    (removelast (graham_scan_inc a (stack ++ [first]))).
Proof.
  intros first a stack Hsorted Hall Hcon.
  pose proof (graham_scan_inc_removelast_preserves_bottom a stack first)
    as Hshape.
  eapply weak_rev_ccw_list_of_sorted_clean_stack.
  - rewrite <- Hshape.
    apply graham_scan_inc_preserves_sorted_chain; assumption.
  - rewrite <- Hshape.
    apply graham_scan_inc_rev_consec.
    exact Hcon.
Qed.

Lemma rev_consec_ccw_of_consec_rev : forall l,
  consec_ccw (rev l) ->
  rev_consec_ccw l.
Proof.
  induction l as [| a l IH]; intros Hcon.
  - simpl; exact I.
  - rewrite rev_consec_ccw_cons_iff.
    split.
    + apply IH.
      simpl in Hcon.
      apply (consec_ccw_app_inv1 (rev l) [a]).
      exact Hcon.
    + intros b c l0 Hl.
      subst l.
      simpl in Hcon.
      rewrite consec_ccw_snoc_iff in Hcon.
      destruct Hcon as [_ Hlast].
      apply ccw_cyclicity.
      apply (Hlast b c (rev l0)).
      simpl.
      rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma consec_ccw_rev_rev_consec : forall l,
  consec_ccw l ->
  rev_consec_ccw (rev l).
Proof.
  intros l Hcon.
  apply rev_consec_ccw_of_consec_rev.
  rewrite rev_involutive.
  exact Hcon.
Qed.

Lemma ccw_convex_consec_ccw : forall l,
  ccw_convex l ->
  consec_ccw l.
Proof.
  induction l as [| p l IH]; intros Hconv; simpl.
  - exact I.
  - destruct Hconv as [Hlist Htail].
    split.
    + destruct l as [| q [| r rest]]; simpl; exact I || idtac.
      simpl in Hlist.
      destruct Hlist as [Hfor _].
      rewrite Forall_ccw_cons_iff in Hfor.
      exact (proj1 Hfor).
    + apply IH.
      exact Htail.
Qed.

Lemma merged_triangle_max_to_edges : forall first tail base,
  leftmost first tail ->
  ccw_convex (first :: tail) ->
  consec_ccw tail ->
  is_max_hull' first (rev tail) base ->
  is_max_hull'_edges (rev (first :: tail)) base.
Proof.
  intros first tail base Hleft Hconv Hconsec Hmax.
  simpl.
  apply gs_is_max_hull'_edges_rotate1.
  eapply is_max_hull'_edges_of_max_hull.
  - apply ccw_convex_tail_sort_rev; assumption.
  - apply consec_ccw_rev_rev_consec.
    exact Hconsec.
  - exact Hmax.
Qed.

Lemma merged_triangle_max_to_edges_from_convex : forall first tail base,
  leftmost first tail ->
  ccw_convex (first :: tail) ->
  is_max_hull' first (rev tail) base ->
  is_max_hull'_edges (rev (first :: tail)) base.
Proof.
  intros first tail base Hleft Hconv Hmax.
  apply merged_triangle_max_to_edges.
  - exact Hleft.
  - exact Hconv.
  - pose proof (ccw_convex_consec_ccw (first :: tail) Hconv) as Hconsec.
    apply consec_ccw_cons_iff in Hconsec as [Htail _].
    exact Htail.
  - exact Hmax.
Qed.

Lemma andrew_ccw_merge_leftmost :
  forall first middle last lower_mid upper_mid,
  point_xy_sorted (first :: middle ++ [last]) ->
  andrew_lower_chain (first :: middle ++ [last]) =
    first :: lower_mid ++ [last] ->
  andrew_upper_chain (first :: middle ++ [last]) =
    last :: upper_mid ++ [first] ->
  leftmost first (lower_mid ++ last :: upper_mid).
Proof.
  intros first middle last lower_mid upper_mid Hsorted Hlower Hupper.
  assert (Hlower_sorted :
    point_xy_sorted (first :: lower_mid ++ [last])).
  {
    pose proof (andrew_chain_sorted
                  (first :: middle ++ [last]) Hsorted) as Hchain_sorted.
    change (andrew_chain (first :: middle ++ [last]))
      with (andrew_lower_chain (first :: middle ++ [last]))
      in Hchain_sorted.
    rewrite Hlower in Hchain_sorted.
    exact Hchain_sorted.
  }
  assert (Hupper_sorted :
    point_xy_rev_sorted (last :: upper_mid ++ [first])).
  {
    pose proof (andrew_chain_rev_sorted
                  (rev (first :: middle ++ [last]))
                  (point_xy_sorted_rev_is_rev_sorted
                     (first :: middle ++ [last]) Hsorted)) as Hchain_sorted.
    change (andrew_chain (rev (first :: middle ++ [last])))
      with (andrew_upper_chain (first :: middle ++ [last]))
      in Hchain_sorted.
    rewrite Hupper in Hchain_sorted.
    exact Hchain_sorted.
  }
  assert (Hlower_all : Forall (leftdown first) (lower_mid ++ [last])).
  {
    simpl in Hlower_sorted.
    apply point_xy_sorted_from_leftdown_head.
    exact Hlower_sorted.
  }
  pose proof (point_xy_rev_sorted_middle_between
                first upper_mid last Hupper_sorted) as Hupper_between.
  unfold leftmost.
  rewrite Forall_forall.
  intros q Hq.
  replace (lower_mid ++ last :: upper_mid)
    with ((lower_mid ++ [last]) ++ upper_mid) in Hq
    by (rewrite <- app_assoc; reflexivity).
  rewrite in_app_iff in Hq.
  destruct Hq as [Hq | Hq].
  - rewrite Forall_forall in Hlower_all.
    exact (Hlower_all q Hq).
  - rewrite Forall_forall in Hupper_between.
    exact (proj1 (Hupper_between q Hq)).
Qed.

Lemma andrew_lower_mid_below_baseline :
  forall first middle last lower_mid,
  point_xy_sorted (first :: middle ++ [last]) ->
  andrew_lower_chain (first :: middle ++ [last]) =
    first :: lower_mid ++ [last] ->
  forall q, In q lower_mid -> ccw first q last.
Proof.
  intros first middle last lower_mid Hsorted Hlower q Hq.
  pose proof (andrew_lower_chain_ccw_convex
                (first :: middle ++ [last]) Hsorted) as Hlower_conv.
  rewrite Hlower in Hlower_conv.
  simpl in Hlower_conv.
  destruct Hlower_conv as [Hlower_list _].
  rewrite ccw_list_app_iff in Hlower_list.
  destruct Hlower_list as [_ [_ Hcross]].
  apply Hcross; [exact Hq | simpl; auto].
Qed.

Lemma andrew_upper_mid_above_baseline :
  forall first middle last upper_mid,
  point_xy_sorted (first :: middle ++ [last]) ->
  andrew_upper_chain (first :: middle ++ [last]) =
    last :: upper_mid ++ [first] ->
  forall q, In q upper_mid -> ccw first last q.
Proof.
  intros first middle last upper_mid Hsorted Hupper q Hq.
  pose proof (andrew_upper_chain_ccw_convex
                (first :: middle ++ [last]) Hsorted) as Hupper_conv.
  rewrite Hupper in Hupper_conv.
  pose proof (ccw_convex_app_comm (last :: upper_mid) [first]
                Hupper_conv) as Hupper_rot.
  simpl in Hupper_rot.
  destruct Hupper_rot as [Hupper_first_list _].
  simpl in Hupper_first_list.
  destruct Hupper_first_list as [Hforall _].
  rewrite Forall_ccw_forall in Hforall.
  apply Hforall.
  exact Hq.
Qed.

Lemma andrew_merged_triangle_max_to_edges :
  forall first middle last lower_mid upper_mid,
  point_xy_sorted (first :: middle ++ [last]) ->
  andrew_lower_chain (first :: middle ++ [last]) =
    first :: lower_mid ++ [last] ->
  andrew_upper_chain (first :: middle ++ [last]) =
    last :: upper_mid ++ [first] ->
  ccw_convex (first :: lower_mid ++ last :: upper_mid) ->
  is_max_hull' first (rev (lower_mid ++ last :: upper_mid))
    (first :: middle ++ [last]) ->
  is_max_hull'_edges
    (andrew_hull (first :: middle ++ [last]))
    (first :: middle ++ [last]).
Proof.
  intros first middle last lower_mid upper_mid
    Hsorted Hlower Hupper Hconv Hmax.
  unfold andrew_hull, andrew_merge.
  assert (Hmerge :
    andrew_ccw_merge
      (first :: middle ++ [last])
      (andrew_lower_chain (first :: middle ++ [last]))
      (andrew_upper_chain (first :: middle ++ [last])) =
      first :: lower_mid ++ last :: upper_mid).
  {
    eapply andrew_ccw_merge_endpoints; eauto.
  }
  rewrite Hmerge.
  apply merged_triangle_max_to_edges_from_convex.
  - eapply andrew_ccw_merge_leftmost; eauto.
  - exact Hconv.
  - exact Hmax.
Qed.

Fixpoint point_left_of_path_edges_from
    (q prev : point) (path : list point) : Prop :=
  match path with
  | p :: rest =>
      Geo_Vec.left_equal (build_vec prev p) (build_vec prev q) /\
      point_left_of_path_edges_from q p rest
  | [] => True
  end.

Definition point_left_of_path_edges (q : point) (path : list point) : Prop :=
  match path with
  | prev :: rest => point_left_of_path_edges_from q prev rest
  | [] => True
  end.

Lemma point_left_of_path_edges_cons :
  forall q p r rest,
  Geo_Vec.left_equal (build_vec p r) (build_vec p q) ->
  point_left_of_path_edges q (r :: rest) ->
  point_left_of_path_edges q (p :: r :: rest).
Proof.
  intros q p r rest Hedge Hpath.
  simpl.
  split; assumption.
Qed.

Lemma point_left_of_path_edges_tail :
  forall q p r rest,
  point_left_of_path_edges q (p :: r :: rest) ->
  point_left_of_path_edges q (r :: rest).
Proof.
  intros q p r rest Hpath.
  simpl in Hpath.
  exact (proj2 Hpath).
Qed.

Lemma left_equal_pop_shortcut :
  forall q p t s,
  ~ ccw s t p ->
  Geo_Vec.left_equal (build_vec p t) (build_vec p q) ->
  Geo_Vec.left_equal (build_vec t s) (build_vec t q) ->
  Geo_Vec.left_equal (build_vec p s) (build_vec p q).
Proof.
  unfold ccw, Geo_Vec.left_than, Geo_Vec.left_equal,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma point_left_of_path_edges_pop_middle :
  forall q p t s rest,
  ~ ccw s t p ->
  point_left_of_path_edges q (p :: t :: s :: rest) ->
  point_left_of_path_edges q (p :: s :: rest).
Proof.
  intros q p t s rest Hnccw Hpath.
  simpl in Hpath |- *.
  destruct Hpath as [Hpt [Hts Htail]].
  split.
  - eapply left_equal_pop_shortcut; eauto.
  - exact Htail.
Qed.

Lemma point_left_of_path_edges_graham_scan_inc_cleanup :
  forall q p T,
  point_left_of_path_edges q (p :: T) ->
  point_left_of_path_edges q (graham_scan_inc p T).
Proof.
  intros q p T.
  revert p.
  induction T as [| t T IH]; intros p Hpath; simpl in *.
  - exact I.
  - destruct T as [| s rest].
    + exact Hpath.
    + destruct (ccw_dec s t p) as [_ | Hnccw].
      * exact Hpath.
      * apply IH.
        eapply point_left_of_path_edges_pop_middle; eauto.
Qed.

Lemma Forall_point_left_of_path_edges_graham_scan_inc_cleanup :
  forall L p T,
  Forall (fun q => point_left_of_path_edges q (p :: T)) L ->
  Forall (fun q => point_left_of_path_edges q (graham_scan_inc p T)) L.
Proof.
  intros L p T Hcover.
  eapply Forall_impl.
  2: exact Hcover.
  intros q Hq.
  apply point_left_of_path_edges_graham_scan_inc_cleanup.
  exact Hq.
Qed.

Lemma left_equal_push_support_lower :
  forall q s t a,
  leftdown s t ->
  leftdown q t ->
  leftdown t a ->
  ccw s t a ->
  Geo_Vec.left_equal (build_vec t s) (build_vec t q) ->
  Geo_Vec.left_equal (build_vec a t) (build_vec a q).
Proof.
  unfold leftdown, ccw, Geo_Vec.left_than,
         Geo_Vec.left_equal, Geo_Vec.cross_prod, build_vec,
         x, y.
  simpl.
  intros [qx qy] [sx sy] [tx ty] [ax ay] Hst Hqt Hta Hturn Hedge.
  simpl in *.
  set (dx := tx - sx) in *.
  set (dy := ty - sy) in *.
  set (ux := ax - tx) in *.
  set (uy := ay - ty) in *.
  set (vx := qx - tx) in *.
  set (vy := qy - ty) in *.
  assert (Hturn' : dx * uy - dy * ux > 0) by (subst; ring_simplify; nia).
  assert (Hedge' : dx * vy - dy * vx >= 0) by (subst; ring_simplify; nia).
  assert (Hdx : dx > 0).
  {
    destruct Hst as [Hst | [Hstx Hsty]];
    destruct Hta as [Hta | [Htax Htay]]; subst; nia.
  }
  assert (Hux_nonneg : 0 <= ux).
  {
    destruct Hta as [Hta | [Htax Htay]]; subst; nia.
  }
  assert (Hvx_nonpos : vx <= 0).
  {
    destruct Hqt as [Hqt | [Hqtx Hqty]]; subst; nia.
  }
  assert (Hgoal_shift : ux * vy - uy * vx >= 0).
  {
    destruct (Z_lt_ge_dec 0 ux) as [Hux_pos | Hux_zeroish].
    - destruct Hqt as [Hvx_neg | [Hvx_eq Hvy_nonpos]].
      + assert (Hid :
          dx * (ux * vy - uy * vx) =
          ux * (dx * vy - dy * vx) -
          vx * (dx * uy - dy * ux)) by ring.
        assert (0 <= ux * (dx * vy - dy * vx)) by nia.
        assert (0 <= - vx * (dx * uy - dy * ux)) by nia.
        nia.
      + assert (vx = 0) by (subst; nia).
        assert (vy = 0) by nia.
        nia.
    - assert (ux = 0) by nia.
      subst ux.
      destruct Hta as [Hta | [Htax Htay]]; [nia |].
      nia.
  }
  subst dx dy ux uy vx vy.
  ring_simplify in Hgoal_shift.
  nia.
Qed.

Lemma left_equal_pop_support_lower :
  forall q s t a,
  leftdown s q ->
  leftdown q t ->
  leftdown s t ->
  leftdown t a ->
  ~ ccw s t a ->
  Geo_Vec.left_equal (build_vec t s) (build_vec t q) ->
  Geo_Vec.left_equal (build_vec a s) (build_vec a q).
Proof.
  unfold leftdown, ccw, Geo_Vec.left_than,
         Geo_Vec.left_equal, Geo_Vec.cross_prod, build_vec,
         x, y.
  simpl.
  intros [qx qy] [sx sy] [tx ty] [ax ay] Hsq Hqt Hst Hta Hturn Hedge.
  simpl in *.
  set (dx := tx - sx) in *.
  set (dy := ty - sy) in *.
  set (ux := ax - tx) in *.
  set (uy := ay - ty) in *.
  set (vx := qx - tx) in *.
  set (vy := qy - ty) in *.
  assert (Hturn' : dx * uy - dy * ux <= 0) by (subst; ring_simplify; nia).
  assert (Hedge' : dx * vy - dy * vx >= 0) by (subst; ring_simplify; nia).
  assert (Hdx : dx >= 0).
  {
    destruct Hst as [Hst | [Hstx Hsty]]; subst; nia.
  }
  assert (Hux_nonneg : 0 <= ux).
  {
    destruct Hta as [Hta | [Htax Htay]]; subst; nia.
  }
  assert (Hvx_nonpos : vx <= 0).
  {
    destruct Hqt as [Hqt | [Hqtx Hqty]]; subst; nia.
  }
  assert (Hsv_nonneg : 0 <= vx + dx).
  {
    destruct Hsq as [Hsq | [Hsqx Hsqy]]; subst; nia.
  }
  assert (Hgoal_shift : (ux + dx) * (vy + dy) - (uy + dy) * (vx + dx) >= 0).
  {
    assert (Hid :
      dx * ((ux + dx) * (vy + dy) - (uy + dy) * (vx + dx)) =
      (ux + dx) * (dx * vy - dy * vx) -
      (vx + dx) * (dx * uy - dy * ux)) by ring.
    destruct (Z.eq_dec dx 0) as [Hdx0 | Hdx_ne].
    - subst dx.
      assert (vx = 0) by nia.
      subst vx.
      destruct Hst as [Hst | [Hstx Hsty]]; [nia |].
      destruct Hsq as [Hsq | [Hsqx Hsqy]]; [nia |].
      destruct Hqt as [Hqt | [Hqtx Hqty]]; [nia |].
      subst; nia.
    - assert (Hdx_pos : dx > 0) by nia.
      assert (0 <= (ux + dx) * (dx * vy - dy * vx)) by nia.
      assert (0 <= - (vx + dx) * (dx * uy - dy * ux)) by nia.
      nia.
  }
  subst dx dy ux uy vx vy.
  ring_simplify in Hgoal_shift.
  nia.
Qed.

Lemma left_equal_push_support_upper :
  forall q s t a,
  leftdown t s ->
  leftdown t q ->
  leftdown a t ->
  ccw s t a ->
  Geo_Vec.left_equal (build_vec t s) (build_vec t q) ->
  Geo_Vec.left_equal (build_vec a t) (build_vec a q).
Proof.
  unfold leftdown, ccw, Geo_Vec.left_than,
         Geo_Vec.left_equal, Geo_Vec.cross_prod, build_vec,
         x, y.
  simpl.
  intros [qx qy] [sx sy] [tx ty] [ax ay] Hts Htq Hat Hturn Hedge.
  simpl in *.
  set (dx := sx - tx) in *.
  set (dy := sy - ty) in *.
  set (ux := tx - ax) in *.
  set (uy := ty - ay) in *.
  set (vx := qx - tx) in *.
  set (vy := qy - ty) in *.
  assert (Hturn' : dx * uy - dy * ux > 0) by (subst; ring_simplify; nia).
  assert (Hedge' : dx * vy - dy * vx <= 0) by (subst; ring_simplify; nia).
  assert (Hdx : dx > 0).
  {
    destruct Hts as [Hts | [Htsx Htsy]];
    destruct Hat as [Hat | [Hatx Haty]]; subst; nia.
  }
  assert (Hux_nonneg : 0 <= ux).
  {
    destruct Hat as [Hat | [Hatx Haty]]; subst; nia.
  }
  assert (Hvx_nonneg : 0 <= vx).
  {
    destruct Htq as [Htq | [Htqx Htqy]]; subst; nia.
  }
  assert (Hgoal_shift : ux * vy - uy * vx <= 0).
  {
    destruct (Z_lt_ge_dec 0 ux) as [Hux_pos | Hux_zeroish].
    - assert (Hid :
        dx * (ux * vy - uy * vx) =
        ux * (dx * vy - dy * vx) -
        vx * (dx * uy - dy * ux)) by ring.
      assert (ux * (dx * vy - dy * vx) <= 0) by nia.
      assert (- vx * (dx * uy - dy * ux) <= 0) by nia.
      nia.
    - assert (ux = 0) by nia.
      subst ux.
      destruct Hat as [Hat | [Hatx Haty]]; [nia |].
      destruct Htq as [Htq | [Htqx Htqy]]; subst; nia.
  }
  subst dx dy ux uy vx vy.
  ring_simplify in Hgoal_shift.
  nia.
Qed.

Lemma left_equal_pop_support_upper :
  forall q s t a,
  leftdown t q ->
  leftdown q s ->
  leftdown t s ->
  leftdown a t ->
  ~ ccw s t a ->
  Geo_Vec.left_equal (build_vec t s) (build_vec t q) ->
  Geo_Vec.left_equal (build_vec a s) (build_vec a q).
Proof.
  unfold leftdown, ccw, Geo_Vec.left_than,
         Geo_Vec.left_equal, Geo_Vec.cross_prod, build_vec,
         x, y.
  simpl.
  intros [qx qy] [sx sy] [tx ty] [ax ay] Htq Hqs Hts Hat Hturn Hedge.
  simpl in *.
  set (dx := sx - tx) in *.
  set (dy := sy - ty) in *.
  set (ux := tx - ax) in *.
  set (uy := ty - ay) in *.
  set (vx := qx - tx) in *.
  set (vy := qy - ty) in *.
  assert (Hturn' : dx * uy - dy * ux <= 0) by (subst; ring_simplify; nia).
  assert (Hedge' : dx * vy - dy * vx <= 0) by (subst; ring_simplify; nia).
  assert (Hdx : dx >= 0).
  {
    destruct Hts as [Hts | [Htsx Htsy]]; subst; nia.
  }
  assert (Hux_nonneg : 0 <= ux).
  {
    destruct Hat as [Hat | [Hatx Haty]]; subst; nia.
  }
  assert (Hvx_nonneg : 0 <= vx).
  {
    destruct Htq as [Htq | [Htqx Htqy]]; subst; nia.
  }
  assert (Hsv_nonneg : vx <= dx).
  {
    destruct Hqs as [Hqs | [Hqsx Hqsy]]; subst; nia.
  }
  assert (Hgoal_shift :
    (ux + dx) * (vy + uy) - (uy + dy) * (vx + ux) <= 0).
  {
    assert (Hid :
      dx * ((ux + dx) * (vy + uy) - (uy + dy) * (vx + ux)) =
      (ux + dx) * (dx * vy - dy * vx) +
      (dx - vx) * (dx * uy - dy * ux)) by ring.
    destruct (Z.eq_dec dx 0) as [Hdx0 | Hdx_ne].
    - subst dx.
      assert (vx = 0) by nia.
      subst vx.
      nia.
    - assert (Hdx_pos : dx > 0) by nia.
      assert ((ux + dx) * (dx * vy - dy * vx) <= 0) by nia.
      assert ((dx - vx) * (dx * uy - dy * ux) <= 0) by nia.
      nia.
  }
  subst dx dy ux uy vx vy.
  ring_simplify in Hgoal_shift.
  nia.
Qed.

Lemma point_left_of_path_edges_push_support_lower :
  forall q a t s rest,
  leftdown s t ->
  leftdown q t ->
  leftdown t a ->
  ccw s t a ->
  point_left_of_path_edges q (t :: s :: rest) ->
  point_left_of_path_edges q (a :: t :: s :: rest).
Proof.
  intros q a t s rest Hst Hqt Hta Hturn Hpath.
  pose proof Hpath as Hpath_edge.
  simpl in Hpath_edge.
  destruct Hpath_edge as [Hedge _].
  simpl.
  split.
  - exact (left_equal_push_support_lower
             q s t a Hst Hqt Hta Hturn Hedge).
  - exact Hpath.
Qed.

Lemma point_left_of_path_edges_pop_interval_lower :
  forall q a t s rest,
  leftdown s q ->
  leftdown q t ->
  leftdown s t ->
  leftdown t a ->
  ~ ccw s t a ->
  point_left_of_path_edges q (t :: s :: rest) ->
  point_left_of_path_edges q (a :: s :: rest).
Proof.
  intros q a t s rest Hsq Hqt Hst Hta Hturn Hpath.
  simpl in Hpath |- *.
  destruct Hpath as [Hedge Htail].
  split.
  - exact (left_equal_pop_support_lower
             q s t a Hsq Hqt Hst Hta Hturn Hedge).
  - exact Htail.
Qed.

Lemma point_left_of_path_edges_push_support_upper :
  forall q a t s rest,
  leftdown t s ->
  leftdown t q ->
  leftdown a t ->
  ccw s t a ->
  point_left_of_path_edges q (t :: s :: rest) ->
  point_left_of_path_edges q (a :: t :: s :: rest).
Proof.
  intros q a t s rest Hts Htq Hat Hturn Hpath.
  pose proof Hpath as Hpath_edge.
  simpl in Hpath_edge.
  destruct Hpath_edge as [Hedge _].
  simpl.
  split.
  - exact (left_equal_push_support_upper
             q s t a Hts Htq Hat Hturn Hedge).
  - exact Hpath.
Qed.

Lemma point_left_of_path_edges_pop_interval_upper :
  forall q a t s rest,
  leftdown t q ->
  leftdown q s ->
  leftdown t s ->
  leftdown a t ->
  ~ ccw s t a ->
  point_left_of_path_edges q (t :: s :: rest) ->
  point_left_of_path_edges q (a :: s :: rest).
Proof.
  intros q a t s rest Htq Hqs Hts Hat Hturn Hpath.
  simpl in Hpath |- *.
  destruct Hpath as [Hedge Htail].
  split.
  - exact (left_equal_pop_support_upper
             q s t a Htq Hqs Hts Hat Hturn Hedge).
  - exact Htail.
Qed.

Lemma leftdown_total : forall p q,
  leftdown p q \/ leftdown q p.
Proof.
  unfold leftdown, x, y.
  intros [px py] [qx qy].
  simpl; lia.
Qed.

Lemma point_xy_sorted_rev_stack_adjacent :
  forall top s rest first,
  point_xy_sorted (rev (top :: s :: rest ++ [first])) ->
  leftdown s top.
Proof.
  intros top s rest first Hsorted.
  simpl in Hsorted.
  rewrite rev_app_distr in Hsorted.
  simpl in Hsorted.
  change (point_xy_sorted (first :: (rev rest ++ [s]) ++ [top]))
    in Hsorted.
  pose proof (point_xy_sorted_all_leftdown_last
                first (rev rest ++ [s]) top Hsorted) as Hall.
  rewrite Forall_forall in Hall.
  apply Hall.
  simpl.
  right.
  rewrite in_app_iff.
  left.
  rewrite in_app_iff.
  right; simpl; auto.
Qed.

Lemma point_left_of_path_edges_graham_scan_inc_lower_between :
  forall q a first top stack,
  point_xy_sorted (rev (top :: stack ++ [first])) ->
  Forall (fun r => leftdown r a) (top :: stack ++ [first]) ->
  leftdown first q ->
  leftdown q top ->
  point_left_of_path_edges q (top :: stack ++ [first]) ->
  point_left_of_path_edges q (graham_scan_inc a (top :: stack ++ [first])).
Proof.
  intros q a first top stack.
  revert q a top.
  induction stack as [| s rest IH]; intros q a top
    Hsorted Hall Hfirstq Hqtop Hpath.
  - change (top :: [] ++ [first]) with ([top; first])
      in Hsorted, Hall, Hpath |- *.
    simpl in Hall.
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [Htopa Hall].
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [Hfirsta _].
    simpl in Hpath.
    destruct (ccw_dec first top a) as [Hturn | Hnot] eqn:Hturn_dec.
    + simpl.
      rewrite Hturn_dec.
      apply point_left_of_path_edges_push_support_lower.
      * eapply leftdown_trans; eauto.
      * exact Hqtop.
      * exact Htopa.
      * exact Hturn.
      * exact Hpath.
    + simpl.
      rewrite Hturn_dec.
      split.
      * eapply left_equal_pop_support_lower.
        -- exact Hfirstq.
        -- exact Hqtop.
        -- eapply leftdown_trans; eauto.
        -- exact Htopa.
        -- exact Hnot.
        -- exact (proj1 Hpath).
      * exact I.
  - rewrite Forall_cons_iff in Hall.
    destruct Hall as [Htopa Hall_tail].
    pose proof (point_xy_sorted_rev_stack_adjacent
                  top s rest first Hsorted) as Hstop.
    destruct (ccw_dec s top a) as [Hturn | Hnot] eqn:Hturn_dec.
    + simpl.
      rewrite Hturn_dec.
      apply point_left_of_path_edges_push_support_lower.
      * exact Hstop.
      * exact Hqtop.
      * exact Htopa.
      * exact Hturn.
      * exact Hpath.
    + destruct (leftdown_total s q) as [Hsq | Hqs].
      * simpl.
        rewrite Hturn_dec.
        change (point_left_of_path_edges q
          (graham_scan_inc a (s :: rest ++ [first]))).
        apply point_left_of_path_edges_graham_scan_inc_cleanup.
        eapply point_left_of_path_edges_pop_interval_lower.
        -- exact Hsq.
        -- exact Hqtop.
        -- exact Hstop.
        -- exact Htopa.
        -- exact Hnot.
        -- exact Hpath.
      * simpl.
        rewrite Hturn_dec.
        change (point_left_of_path_edges q
          (graham_scan_inc a (s :: rest ++ [first]))).
        apply IH.
        -- change (point_xy_sorted (rev (s :: rest ++ [first]))).
           eapply point_xy_sorted_rev_tail.
           exact Hsorted.
        -- exact Hall_tail.
        -- exact Hfirstq.
        -- exact Hqs.
        -- eapply point_left_of_path_edges_tail.
           exact Hpath.
Qed.

Lemma point_xy_sorted_stack_adjacent :
  forall top s rest last,
  point_xy_sorted (top :: s :: rest ++ [last]) ->
  leftdown top s.
Proof.
  intros top s rest last Hsorted.
  simpl in Hsorted.
  exact (proj1 Hsorted).
Qed.

Lemma point_left_of_path_edges_graham_scan_inc_upper_between :
  forall q a last top stack,
  point_xy_sorted (top :: stack ++ [last]) ->
  Forall (fun r => leftdown a r) (top :: stack ++ [last]) ->
  leftdown top q ->
  leftdown q last ->
  point_left_of_path_edges q (top :: stack ++ [last]) ->
  point_left_of_path_edges q (graham_scan_inc a (top :: stack ++ [last])).
Proof.
  intros q a last top stack.
  revert q a top.
  induction stack as [| s rest IH]; intros q a top
    Hsorted Hall Htopq Hqlast Hpath.
  - change (top :: [] ++ [last]) with ([top; last])
      in Hsorted, Hall, Hpath |- *.
    simpl in Hall.
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [Hatop Hall].
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [Halast _].
    simpl in Hpath.
    destruct (ccw_dec last top a) as [Hturn | Hnot] eqn:Hturn_dec.
    + simpl.
      rewrite Hturn_dec.
      apply point_left_of_path_edges_push_support_upper.
      * eapply leftdown_trans; eauto.
      * exact Htopq.
      * exact Hatop.
      * exact Hturn.
      * exact Hpath.
    + simpl.
      rewrite Hturn_dec.
      split.
      * eapply left_equal_pop_support_upper.
        -- exact Htopq.
        -- exact Hqlast.
        -- eapply leftdown_trans; eauto.
        -- exact Hatop.
        -- exact Hnot.
        -- exact (proj1 Hpath).
      * exact I.
  - rewrite Forall_cons_iff in Hall.
    destruct Hall as [Hatop Hall_tail].
    pose proof (point_xy_sorted_stack_adjacent
                  top s rest last Hsorted) as Htops.
    destruct (ccw_dec s top a) as [Hturn | Hnot] eqn:Hturn_dec.
    + simpl.
      rewrite Hturn_dec.
      apply point_left_of_path_edges_push_support_upper.
      * exact Htops.
      * exact Htopq.
      * exact Hatop.
      * exact Hturn.
      * exact Hpath.
    + destruct (leftdown_total q s) as [Hqs | Hsq].
      * simpl.
        rewrite Hturn_dec.
        change (point_left_of_path_edges q
          (graham_scan_inc a (s :: rest ++ [last]))).
        apply point_left_of_path_edges_graham_scan_inc_cleanup.
        eapply point_left_of_path_edges_pop_interval_upper.
        -- exact Htopq.
        -- exact Hqs.
        -- exact Htops.
        -- exact Hatop.
        -- exact Hnot.
        -- exact Hpath.
      * simpl.
        rewrite Hturn_dec.
        change (point_left_of_path_edges q
          (graham_scan_inc a (s :: rest ++ [last]))).
        apply IH.
        -- eapply point_xy_sorted_tail.
           exact Hsorted.
        -- exact Hall_tail.
        -- exact Hsq.
        -- exact Hqlast.
        -- eapply point_left_of_path_edges_tail.
           exact Hpath.
Qed.

Lemma left_equal_to_endpoint : forall p q,
  Geo_Vec.left_equal (build_vec p q) (build_vec p p).
Proof.
  unfold Geo_Vec.left_equal, Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma left_equal_to_edge_endpoint : forall p q,
  Geo_Vec.left_equal (build_vec p q) (build_vec p q).
Proof.
  unfold Geo_Vec.left_equal.
  intros; rewrite Geo_Vec.cross_prod_self; lia.
Qed.

Lemma ccw_rev_edge_left_equal : forall p q r,
  ccw p q r ->
  Geo_Vec.left_equal (build_vec q p) (build_vec q r).
Proof.
  unfold ccw, Geo_Vec.left_than, Geo_Vec.left_equal,
         Geo_Vec.cross_prod, build_vec.
  simpl; intros; nia.
Qed.

Lemma point_xy_sorted_rev_stack_all_leftdown_head :
  forall top stack first,
  point_xy_sorted (rev (top :: stack ++ [first])) ->
  Forall (fun r => leftdown r top) (top :: stack ++ [first]).
Proof.
  intros top stack first Hsorted.
  assert (Hsorted' : point_xy_sorted (first :: rev stack ++ [top])).
  {
    simpl in Hsorted.
    rewrite rev_app_distr in Hsorted.
    simpl in Hsorted.
    exact Hsorted.
  }
  pose proof (point_xy_sorted_all_leftdown_last
                first (rev stack) top Hsorted') as Hall.
  replace (top :: stack ++ [first])
    with (rev (first :: rev stack ++ [top])).
  - apply Forall_rev.
    exact Hall.
  - simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_involutive.
    reflexivity.
Qed.

Lemma point_xy_sorted_stack_all_leftdown_head :
  forall top stack last,
  point_xy_sorted (top :: stack ++ [last]) ->
  Forall (fun r => leftdown top r) (top :: stack ++ [last]).
Proof.
  intros top stack last Hsorted.
  constructor.
  - apply leftdown_refl.
  - simpl in Hsorted.
    apply point_xy_sorted_from_leftdown_head.
    exact Hsorted.
Qed.

Lemma point_left_of_path_edges_lower_after_turn :
  forall a first top s rest,
  point_xy_sorted (rev (top :: s :: rest ++ [first])) ->
  rev_consec_ccw (top :: s :: rest ++ [first]) ->
  Forall (fun r => leftdown r a) (top :: s :: rest ++ [first]) ->
  ccw s top a ->
  point_left_of_path_edges a (top :: s :: rest ++ [first]).
Proof.
  intros a first top s rest.
  revert a first top s.
  induction rest as [| u rest IH]; intros a first top s
    Hsorted Hcon Hall Hturn.
  - assert (Hfirsts : leftdown first s).
    {
      simpl in Hsorted.
      destruct Hsorted as [Hfirsts _].
      exact Hfirsts.
    }
    assert (Hstop : leftdown s top).
    {
      simpl in Hsorted.
      destruct Hsorted as [_ [Hstop _]].
      exact Hstop.
    }
    assert (Htopa : leftdown top a).
    {
      rewrite Forall_cons_iff in Hall.
      exact (proj1 Hall).
    }
    assert (Hfirst_s_top : ccw first s top).
    {
      simpl in Hcon.
      destruct Hcon as [Hs_top_first _].
      apply ccw_cyclicity_2.
      exact Hs_top_first.
    }
    assert (Hfirst_s_a : ccw first s a).
    {
      eapply ccw_leftdown_forward_extend_head; eauto.
    }
    simpl.
    split.
    + apply ccw_rev_edge_left_equal.
      exact Hturn.
    + split.
      * apply ccw_rev_edge_left_equal.
        exact Hfirst_s_a.
      * exact I.
  - assert (Htail_sorted :
      point_xy_sorted (rev (s :: u :: rest ++ [first]))).
    {
      change (point_xy_sorted (rev (s :: u :: rest ++ [first]))).
      eapply point_xy_sorted_rev_tail.
      exact Hsorted.
    }
    assert (Hstop : leftdown s top).
    {
      eapply point_xy_sorted_rev_stack_adjacent.
      exact Hsorted.
    }
    assert (Hus : leftdown u s).
    {
      eapply point_xy_sorted_rev_stack_adjacent.
      exact Htail_sorted.
    }
    assert (Htopa : leftdown top a).
    {
      rewrite Forall_cons_iff in Hall.
      exact (proj1 Hall).
    }
    assert (Htail_con : rev_consec_ccw (s :: u :: rest ++ [first])).
    {
      apply rev_consec_ccw_cons_iff in Hcon as [Htail _].
      exact Htail.
    }
    assert (Hu_s_top : ccw u s top).
    {
      apply rev_consec_ccw_cons_iff in Hcon as [_ Hhead].
      apply ccw_cyclicity_2.
      apply (Hhead s u (rest ++ [first])).
      reflexivity.
    }
    assert (Hu_s_a : ccw u s a).
    {
      eapply ccw_leftdown_forward_extend_head; eauto.
    }
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [_ Hall_tail].
    simpl.
    split.
    + apply ccw_rev_edge_left_equal.
      exact Hturn.
    + eapply IH; eauto.
Qed.

Lemma point_left_of_path_edges_upper_after_turn :
  forall a last top s rest,
  point_xy_sorted (top :: s :: rest ++ [last]) ->
  rev_consec_ccw (top :: s :: rest ++ [last]) ->
  Forall (fun r => leftdown a r) (top :: s :: rest ++ [last]) ->
  ccw s top a ->
  point_left_of_path_edges a (top :: s :: rest ++ [last]).
Proof.
  intros a last top s rest.
  revert a last top s.
  induction rest as [| u rest IH]; intros a last top s
    Hsorted Hcon Hall Hturn.
  - assert (Htops : leftdown top s).
    {
      simpl in Hsorted.
      exact (proj1 Hsorted).
    }
    assert (Hslast : leftdown s last).
    {
      simpl in Hsorted.
      destruct Hsorted as [_ [Hslast _]].
      exact Hslast.
    }
    assert (Hatop : leftdown a top).
    {
      rewrite Forall_cons_iff in Hall.
      exact (proj1 Hall).
    }
    assert (Hlast_s_top : ccw last s top).
    {
      simpl in Hcon.
      destruct Hcon as [Hs_top_last _].
      apply ccw_cyclicity_2.
      exact Hs_top_last.
    }
    assert (Hlast_s_a : ccw last s a).
    {
      eapply ccw_leftdown_rev_forward_extend_head; eauto.
    }
    simpl.
    split.
    + apply ccw_rev_edge_left_equal.
      exact Hturn.
    + split.
      * apply ccw_rev_edge_left_equal.
        exact Hlast_s_a.
      * exact I.
  - assert (Htail_sorted :
      point_xy_sorted (s :: u :: rest ++ [last])).
    {
      eapply point_xy_sorted_tail.
      exact Hsorted.
    }
    assert (Htops : leftdown top s).
    {
      eapply point_xy_sorted_stack_adjacent.
      exact Hsorted.
    }
    assert (Hsu : leftdown s u).
    {
      eapply point_xy_sorted_stack_adjacent.
      exact Htail_sorted.
    }
    assert (Hatop : leftdown a top).
    {
      rewrite Forall_cons_iff in Hall.
      exact (proj1 Hall).
    }
    assert (Htail_con : rev_consec_ccw (s :: u :: rest ++ [last])).
    {
      apply rev_consec_ccw_cons_iff in Hcon as [Htail _].
      exact Htail.
    }
    assert (Hu_s_top : ccw u s top).
    {
      apply rev_consec_ccw_cons_iff in Hcon as [_ Hhead].
      apply ccw_cyclicity_2.
      apply (Hhead s u (rest ++ [last])).
      reflexivity.
    }
    assert (Hu_s_a : ccw u s a).
    {
      eapply ccw_leftdown_rev_forward_extend_head; eauto.
    }
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [_ Hall_tail].
    simpl.
    split.
    + apply ccw_rev_edge_left_equal.
      exact Hturn.
    + eapply IH; eauto.
Qed.

Lemma point_left_of_path_edges_graham_scan_inc_lower_self :
  forall a first top stack,
  point_xy_sorted (rev (top :: stack ++ [first])) ->
  rev_consec_ccw (top :: stack ++ [first]) ->
  Forall (fun r => leftdown r a) (top :: stack ++ [first]) ->
  point_left_of_path_edges a (graham_scan_inc a (top :: stack ++ [first])).
Proof.
  intros a first top stack.
  revert a first top.
  induction stack as [| s rest IH]; intros a first top
    Hsorted Hcon Hall.
  - change (top :: [] ++ [first]) with ([top; first])
      in Hsorted, Hcon, Hall |- *.
    simpl.
    destruct (ccw_dec first top a) as [Hturn | _].
    + simpl.
      split.
      * apply left_equal_to_endpoint.
      * split.
        -- apply ccw_rev_edge_left_equal.
           exact Hturn.
        -- exact I.
    + simpl.
      split; [apply left_equal_to_endpoint | exact I].
  - pose proof Hall as Hall_all.
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [_ Hall_tail].
    simpl.
    destruct (ccw_dec s top a) as [Hturn | _].
    + simpl.
      split.
      * apply left_equal_to_endpoint.
      * eapply point_left_of_path_edges_lower_after_turn; eauto.
    + change (point_left_of_path_edges a
        (graham_scan_inc a (s :: rest ++ [first]))).
      apply IH.
      * change (point_xy_sorted (rev (s :: rest ++ [first]))).
        eapply point_xy_sorted_rev_tail.
        exact Hsorted.
      * apply rev_consec_ccw_cons_iff in Hcon as [Htail _].
        exact Htail.
      * exact Hall_tail.
Qed.

Lemma point_left_of_path_edges_graham_scan_inc_upper_self :
  forall a last top stack,
  point_xy_sorted (top :: stack ++ [last]) ->
  rev_consec_ccw (top :: stack ++ [last]) ->
  Forall (fun r => leftdown a r) (top :: stack ++ [last]) ->
  point_left_of_path_edges a (graham_scan_inc a (top :: stack ++ [last])).
Proof.
  intros a last top stack.
  revert a last top.
  induction stack as [| s rest IH]; intros a last top
    Hsorted Hcon Hall.
  - change (top :: [] ++ [last]) with ([top; last])
      in Hsorted, Hcon, Hall |- *.
    simpl.
    destruct (ccw_dec last top a) as [Hturn | _].
    + simpl.
      split.
      * apply left_equal_to_endpoint.
      * split.
        -- apply ccw_rev_edge_left_equal.
           exact Hturn.
        -- exact I.
    + simpl.
      split; [apply left_equal_to_endpoint | exact I].
  - pose proof Hall as Hall_all.
    rewrite Forall_cons_iff in Hall.
    destruct Hall as [_ Hall_tail].
    simpl.
    destruct (ccw_dec s top a) as [Hturn | _].
    + simpl.
      split.
      * apply left_equal_to_endpoint.
      * eapply point_left_of_path_edges_upper_after_turn; eauto.
    + change (point_left_of_path_edges a
        (graham_scan_inc a (s :: rest ++ [last]))).
      apply IH.
      * eapply point_xy_sorted_tail.
        exact Hsorted.
      * apply rev_consec_ccw_cons_iff in Hcon as [Htail _].
        exact Htail.
      * exact Hall_tail.
Qed.

Lemma graham_scan_inc_preserves_stack_sorted_upper : forall p T,
  Forall (fun q => leftdown p q) T ->
  point_xy_sorted T ->
  point_xy_sorted (graham_scan_inc p T).
Proof.
  intros p T Hall Hsorted.
  replace (graham_scan_inc p T)
    with (rev (rev (graham_scan_inc p T)))
    by apply rev_involutive.
  apply point_xy_rev_sorted_rev_is_sorted.
  apply graham_scan_inc_preserves_rev_sorted_chain.
  - exact Hall.
  - apply point_xy_sorted_rev_is_rev_sorted.
    exact Hsorted.
Qed.

Lemma fold_left_graham_scan_inc_lower_open_edges_aux :
  forall first top stack rest L,
  point_xy_sorted (rev (top :: stack ++ [first])) ->
  rev_consec_ccw (top :: stack ++ [first]) ->
  point_xy_sorted_from top rest ->
  Forall (fun q => leftdown first q) L ->
  Forall (fun q => leftdown q top) L ->
  Forall
    (fun q => point_left_of_path_edges q (top :: stack ++ [first]))
    L ->
  Forall
    (fun q =>
       point_left_of_path_edges q
         (fold_left (fun T p => graham_scan_inc p T)
            rest (top :: stack ++ [first])))
    (L ++ rest).
Proof.
  intros first top stack rest.
  revert first top stack.
  induction rest as [| a rest IH]; intros first top stack L
    Hsorted Hcon Hrest Hfirst_L Htop_L Hcover_L.
  - simpl.
    rewrite app_nil_r.
    exact Hcover_L.
  - simpl in Hrest.
    destruct Hrest as [Htopa Hrest].
    assert (Hall : Forall (fun r => leftdown r a)
      (top :: stack ++ [first])).
    {
      eapply Forall_impl.
      - intros r Hrtop.
        eapply leftdown_trans.
        + exact Hrtop.
        + exact Htopa.
      - apply point_xy_sorted_rev_stack_all_leftdown_head.
        exact Hsorted.
    }
    assert (Hcover_old :
      Forall
        (fun q =>
           point_left_of_path_edges q
             (graham_scan_inc a (top :: stack ++ [first])))
        L).
    {
      rewrite Forall_forall.
      intros q Hq.
      eapply point_left_of_path_edges_graham_scan_inc_lower_between.
      - exact Hsorted.
      - exact Hall.
      - rewrite Forall_forall in Hfirst_L.
        exact (Hfirst_L q Hq).
      - rewrite Forall_forall in Htop_L.
        exact (Htop_L q Hq).
      - rewrite Forall_forall in Hcover_L.
        exact (Hcover_L q Hq).
    }
    assert (Hcover_a :
      point_left_of_path_edges a
        (graham_scan_inc a (top :: stack ++ [first]))).
    {
      eapply point_left_of_path_edges_graham_scan_inc_lower_self; eauto.
    }
    assert (Hfirsta : leftdown first a).
    {
      rewrite Forall_forall in Hall.
      apply Hall.
      simpl.
      right.
      rewrite in_app_iff.
      right.
      simpl; auto.
    }
    destruct (graham_scan_inc_preserves_bottom_with_head
                a (top :: stack) first) as [stack' Hshape].
    change (graham_scan_inc a (top :: stack ++ [first]) =
              a :: stack' ++ [first]) in Hshape.
    change (fold_left (fun T p => graham_scan_inc p T)
              (a :: rest) (top :: stack ++ [first]))
      with (fold_left (fun T p => graham_scan_inc p T)
              rest (graham_scan_inc a (top :: stack ++ [first]))).
    rewrite Hshape.
    replace (L ++ a :: rest) with ((L ++ [a]) ++ rest)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
    + rewrite <- Hshape.
      apply graham_scan_inc_preserves_sorted_chain; assumption.
    + rewrite <- Hshape.
      apply graham_scan_inc_rev_consec.
      exact Hcon.
    + exact Hrest.
    + rewrite Forall_app.
      split.
      * exact Hfirst_L.
      * constructor; [exact Hfirsta | constructor].
    + rewrite Forall_app.
      split.
      * eapply Forall_impl.
        -- intros q Hqtop.
           eapply leftdown_trans.
           ++ exact Hqtop.
           ++ exact Htopa.
        -- exact Htop_L.
      * constructor; [apply leftdown_refl | constructor].
    + rewrite Forall_app.
      split.
      * rewrite <- Hshape.
        exact Hcover_old.
      * constructor.
        -- rewrite <- Hshape.
           exact Hcover_a.
        -- constructor.
Qed.

Lemma fold_left_graham_scan_inc_upper_open_edges_aux :
  forall last top stack rest L,
  point_xy_sorted (top :: stack ++ [last]) ->
  rev_consec_ccw (top :: stack ++ [last]) ->
  point_xy_rev_sorted_from top rest ->
  Forall (fun q => leftdown top q) L ->
  Forall (fun q => leftdown q last) L ->
  Forall
    (fun q => point_left_of_path_edges q (top :: stack ++ [last]))
    L ->
  Forall
    (fun q =>
       point_left_of_path_edges q
         (fold_left (fun T p => graham_scan_inc p T)
            rest (top :: stack ++ [last])))
    (L ++ rest).
Proof.
  intros last top stack rest.
  revert last top stack.
  induction rest as [| a rest IH]; intros last top stack L
    Hsorted Hcon Hrest Htop_L Hlast_L Hcover_L.
  - simpl.
    rewrite app_nil_r.
    exact Hcover_L.
  - simpl in Hrest.
    destruct Hrest as [Hatop Hrest].
    assert (Hall : Forall (fun r => leftdown a r)
      (top :: stack ++ [last])).
    {
      eapply Forall_impl.
      - intros r Htopr.
        eapply leftdown_trans.
        + exact Hatop.
        + exact Htopr.
      - apply point_xy_sorted_stack_all_leftdown_head.
        exact Hsorted.
    }
    assert (Hcover_old :
      Forall
        (fun q =>
           point_left_of_path_edges q
             (graham_scan_inc a (top :: stack ++ [last])))
        L).
    {
      rewrite Forall_forall.
      intros q Hq.
      eapply point_left_of_path_edges_graham_scan_inc_upper_between.
      - exact Hsorted.
      - exact Hall.
      - rewrite Forall_forall in Htop_L.
        exact (Htop_L q Hq).
      - rewrite Forall_forall in Hlast_L.
        exact (Hlast_L q Hq).
      - rewrite Forall_forall in Hcover_L.
        exact (Hcover_L q Hq).
    }
    assert (Hcover_a :
      point_left_of_path_edges a
        (graham_scan_inc a (top :: stack ++ [last]))).
    {
      eapply point_left_of_path_edges_graham_scan_inc_upper_self; eauto.
    }
    assert (Halast : leftdown a last).
    {
      rewrite Forall_forall in Hall.
      apply Hall.
      simpl.
      right.
      rewrite in_app_iff.
      right.
      simpl; auto.
    }
    destruct (graham_scan_inc_preserves_bottom_with_head
                a (top :: stack) last) as [stack' Hshape].
    change (graham_scan_inc a (top :: stack ++ [last]) =
              a :: stack' ++ [last]) in Hshape.
    change (fold_left (fun T p => graham_scan_inc p T)
              (a :: rest) (top :: stack ++ [last]))
      with (fold_left (fun T p => graham_scan_inc p T)
              rest (graham_scan_inc a (top :: stack ++ [last]))).
    rewrite Hshape.
    replace (L ++ a :: rest) with ((L ++ [a]) ++ rest)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
    + rewrite <- Hshape.
      apply graham_scan_inc_preserves_stack_sorted_upper; assumption.
    + rewrite <- Hshape.
      apply graham_scan_inc_rev_consec.
      exact Hcon.
    + exact Hrest.
    + rewrite Forall_app.
      split.
      * eapply Forall_impl.
        -- intros q Htopq.
           eapply leftdown_trans.
           ++ exact Hatop.
           ++ exact Htopq.
        -- exact Htop_L.
      * constructor; [apply leftdown_refl | constructor].
    + rewrite Forall_app.
      split.
      * exact Hlast_L.
      * constructor; [exact Halast | constructor].
    + rewrite Forall_app.
      split.
      * rewrite <- Hshape.
        exact Hcover_old.
      * constructor.
        -- rewrite <- Hshape.
           exact Hcover_a.
        -- constructor.
Qed.

Lemma fold_left_graham_scan_inc_lower_open_edges :
  forall first second rest,
  point_xy_sorted (first :: second :: rest) ->
  Forall
    (fun q =>
       point_left_of_path_edges q
         (andrew_scan_stack (first :: second :: rest)))
    (first :: second :: rest).
Proof.
  intros first second rest Hsorted.
  simpl in Hsorted.
  destruct Hsorted as [Hfirst_second Hsorted_rest].
  unfold andrew_scan_stack.
  simpl.
  eapply (fold_left_graham_scan_inc_lower_open_edges_aux
            first second [] rest [first; second]).
  - simpl.
    split; [exact Hfirst_second | exact I].
  - simpl; repeat split.
  - exact Hsorted_rest.
  - constructor; [apply leftdown_refl |].
    constructor; [exact Hfirst_second | constructor].
  - constructor; [exact Hfirst_second |].
    constructor; [apply leftdown_refl | constructor].
  - rewrite !Forall_cons_iff.
    split.
    + simpl.
      split; [apply left_equal_to_edge_endpoint | exact I].
    + split.
      * simpl.
        split; [apply left_equal_to_endpoint | exact I].
      * apply Forall_nil.
Qed.

Lemma fold_left_graham_scan_inc_upper_open_edges :
  forall last second rest,
  point_xy_rev_sorted (last :: second :: rest) ->
  Forall
    (fun q =>
       point_left_of_path_edges q
         (andrew_scan_stack (last :: second :: rest)))
    (last :: second :: rest).
Proof.
  intros last second rest Hsorted.
  simpl in Hsorted.
  destruct Hsorted as [Hsecond_last Hsorted_rest].
  unfold andrew_scan_stack.
  simpl.
  eapply (fold_left_graham_scan_inc_upper_open_edges_aux
            last second [] rest [last; second]).
  - simpl.
    split; [exact Hsecond_last | exact I].
  - simpl; repeat split.
  - exact Hsorted_rest.
  - constructor; [exact Hsecond_last |].
    constructor; [apply leftdown_refl | constructor].
  - constructor; [apply leftdown_refl |].
    constructor; [exact Hsecond_last | constructor].
  - rewrite !Forall_cons_iff.
    split.
    + simpl.
      split; [apply left_equal_to_edge_endpoint | exact I].
    + split.
      * simpl.
        split; [apply left_equal_to_endpoint | exact I].
      * apply Forall_nil.
Qed.

Lemma andrew_lower_chain_open_edge_cover :
  forall first middle last lower_mid,
  point_xy_sorted (first :: middle ++ [last]) ->
  andrew_lower_chain (first :: middle ++ [last]) =
    first :: lower_mid ++ [last] ->
  Forall
    (fun q =>
       point_left_of_path_edges q (last :: rev lower_mid ++ [first]))
    (first :: middle ++ [last]).
Proof.
  intros first middle last lower_mid Hsorted Hlower.
  pose proof (andrew_lower_chain_stack_shape
                first middle last lower_mid Hlower) as Hstack.
  destruct middle as [| second middle].
  - rewrite <- Hstack.
    simpl.
    rewrite !Forall_cons_iff.
    split.
    + simpl.
      split; [apply left_equal_to_edge_endpoint | exact I].
    + split.
      * simpl.
        split; [apply left_equal_to_endpoint | exact I].
      * apply Forall_nil.
  - pose proof (fold_left_graham_scan_inc_lower_open_edges
                  first second (middle ++ [last]) Hsorted) as Hcover.
    change (andrew_scan_stack (first :: second :: middle ++ [last]) =
              last :: rev lower_mid ++ [first]) in Hstack.
    rewrite Hstack in Hcover.
    exact Hcover.
Qed.

Lemma andrew_upper_chain_open_edge_cover :
  forall first middle last upper_mid,
  point_xy_sorted (first :: middle ++ [last]) ->
  andrew_upper_chain (first :: middle ++ [last]) =
    last :: upper_mid ++ [first] ->
  Forall
    (fun q =>
       point_left_of_path_edges q (first :: rev upper_mid ++ [last]))
    (first :: middle ++ [last]).
Proof.
  intros first middle last upper_mid Hsorted Hupper.
  pose proof (andrew_upper_chain_stack_shape
                first middle last upper_mid Hupper) as Hstack.
  assert (Hrev_sorted :
    point_xy_rev_sorted (rev (first :: middle ++ [last]))).
  {
    apply point_xy_sorted_rev_is_rev_sorted.
    exact Hsorted.
  }
  assert (Hcover_rev :
    Forall
      (fun q =>
         point_left_of_path_edges q
           (andrew_scan_stack (rev (first :: middle ++ [last]))))
      (rev (first :: middle ++ [last]))).
  {
    replace (rev (first :: middle ++ [last]))
      with (last :: rev middle ++ [first]) in Hrev_sorted |- *.
    2: {
      simpl.
      rewrite rev_app_distr.
      simpl.
      reflexivity.
    }
    destruct (rev middle) as [| second rest].
    - change (last :: [] ++ [first]) with ([last; first])
        in Hrev_sorted |- *.
      apply fold_left_graham_scan_inc_upper_open_edges.
      exact Hrev_sorted.
    - change (last :: (second :: rest) ++ [first]) with
        (last :: second :: rest ++ [first]) in Hrev_sorted |- *.
      apply fold_left_graham_scan_inc_upper_open_edges.
      exact Hrev_sorted.
  }
  rewrite Hstack in Hcover_rev.
  apply Forall_rev in Hcover_rev.
  rewrite rev_involutive in Hcover_rev.
  exact Hcover_rev.
Qed.

Lemma point_in_hull_edges_aux_from_path_edges :
  forall q first prev rest,
  point_left_of_path_edges q (prev :: rest ++ [first]) ->
  point_in_hull_edges_aux_ q first prev rest.
Proof.
  intros q first prev rest.
  revert prev.
  induction rest as [| p rest IH]; intros prev Hpath.
  - simpl in Hpath |- *.
    tauto.
  - simpl in Hpath |- *.
    destruct Hpath as [Hedge Hpath].
    split.
    + apply IH.
      exact Hpath.
    + exact Hedge.
Qed.

Lemma point_in_hull_edges_from_closed_path_edges :
  forall q first second third rest,
  point_left_of_path_edges q (first :: second :: third :: rest ++ [first]) ->
  point_in_hull_edges q (first :: second :: third :: rest).
Proof.
  intros q first second third rest Hpath.
  simpl in Hpath |- *.
  destruct Hpath as [Hedge Hpath].
  split.
  - exact Hedge.
  - destruct Hpath as [Hedge' Hpath].
    split.
    + apply point_in_hull_edges_aux_from_path_edges.
      exact Hpath.
    + exact Hedge'.
Qed.

Lemma point_left_of_path_edges_from_aux :
  forall q first prev rest,
  point_in_hull_edges_aux_ q first prev rest ->
  point_left_of_path_edges_from q prev (rest ++ [first]).
Proof.
  intros q first prev rest.
  revert prev.
  induction rest as [| p rest IH]; intros prev Haux.
  - simpl in Haux |- *.
    split; [exact Haux | exact I].
  - simpl in Haux |- *.
    destruct Haux as [Haux Hedge].
    split.
    + exact Hedge.
    + apply IH.
      exact Haux.
Qed.

Lemma point_left_of_path_edges_from_hull_edges :
  forall q first second third rest,
  point_in_hull_edges q (first :: second :: third :: rest) ->
  point_left_of_path_edges q (first :: second :: third :: rest ++ [first]).
Proof.
  intros q first second third rest Hedges.
  simpl in Hedges |- *.
  destruct Hedges as [Hfirst Haux].
  split.
  - exact Hfirst.
  - simpl in Haux.
    destruct Haux as [Haux Hsecond].
    split.
    + exact Hsecond.
    + apply point_left_of_path_edges_from_aux.
      exact Haux.
Qed.

Lemma point_in_hull_edges_two_path_segment :
  forall q first last,
  Geo_Vec.left_equal (build_vec first last) (build_vec first q) ->
  Geo_Vec.left_equal (build_vec last first) (build_vec last q) ->
  leftdown first q ->
  leftdown q last ->
  point_in_hull_edges q [last; first].
Proof.
  intros q first last Hfl Hlf Hfirst Hlast.
  simpl.
  assert (Hcol : colinear q first last).
  {
    eapply opposite_left_equal_colinear; eauto.
  }
  split.
  - apply colinear_comm.
    exact Hcol.
  - apply at_mid_comm.
    apply leftdown_colinear_between_at_mid; assumption.
Qed.

Lemma point_left_of_path_edges_two_paths :
  forall q first upper last lower final,
  point_left_of_path_edges q (first :: upper ++ [last]) ->
  point_left_of_path_edges q (last :: lower ++ [final]) ->
  point_left_of_path_edges q ((first :: upper ++ last :: lower) ++ [final]).
Proof.
  intros q first upper.
  revert first.
  induction upper as [| u upper IH]; intros first last lower final Hupper Hlower.
  - simpl in Hupper |- *.
    destruct Hupper as [Hedge _].
    split.
    + exact Hedge.
    + exact Hlower.
  - simpl in Hupper |- *.
    destruct Hupper as [Hedge Hupper].
    split.
    + exact Hedge.
    + apply IH; assumption.
Qed.

Lemma point_in_hull_edges_from_two_open_paths :
  forall q first upper last lower,
  upper <> [] \/ lower <> [] ->
  point_left_of_path_edges q (first :: upper ++ [last]) ->
  point_left_of_path_edges q (last :: lower ++ [first]) ->
  point_in_hull_edges q (first :: upper ++ last :: lower).
Proof.
  intros q first upper last lower Hnon Hupper Hlower.
  pose proof (point_left_of_path_edges_two_paths
                q first upper last lower first Hupper Hlower) as Hclosed.
  destruct upper as [| u upper].
  - destruct lower as [| l lower].
    + destruct Hnon as [Hbad | Hbad]; contradiction Hbad; reflexivity.
    + simpl in Hclosed |- *.
      apply point_in_hull_edges_from_closed_path_edges.
      exact Hclosed.
  - simpl in Hclosed |- *.
    destruct upper as [| u' upper].
    + apply point_in_hull_edges_from_closed_path_edges.
      exact Hclosed.
    + apply point_in_hull_edges_from_closed_path_edges.
      exact Hclosed.
Qed.

Lemma point_in_hull_edges_andrew_merge_from_two_paths :
  forall q first lower_mid last upper_mid,
  upper_mid <> [] \/ lower_mid <> [] ->
  point_left_of_path_edges q (first :: rev upper_mid ++ [last]) ->
  point_left_of_path_edges q (last :: rev lower_mid ++ [first]) ->
  point_in_hull_edges q (rev upper_mid ++ last :: rev lower_mid ++ [first]).
Proof.
  intros q first lower_mid last upper_mid Hnon Hupper Hlower.
  replace (rev upper_mid ++ last :: rev lower_mid ++ [first])
    with ((rev upper_mid ++ last :: rev lower_mid) ++ [first])
    by (rewrite <- app_assoc; reflexivity).
  apply gs_point_in_hull_edges_rotate1.
  change (first :: rev upper_mid ++ last :: rev lower_mid)
    with (first :: rev upper_mid ++ last :: rev lower_mid).
  apply point_in_hull_edges_from_two_open_paths.
  - destruct Hnon as [Hupper_non | Hlower_non].
    + left.
      intro Hrev_nil.
      apply Hupper_non.
      apply (f_equal (@rev point)) in Hrev_nil.
      rewrite rev_involutive in Hrev_nil.
      exact Hrev_nil.
    + right.
      intro Hrev_nil.
      apply Hlower_non.
      apply (f_equal (@rev point)) in Hrev_nil.
      rewrite rev_involutive in Hrev_nil.
      exact Hrev_nil.
  - exact Hupper.
  - exact Hlower.
Qed.

Lemma andrew_hull_max_from_open_edge_covers :
  forall first middle last lower_mid upper_mid,
  point_xy_sorted (first :: middle ++ [last]) ->
  andrew_lower_chain (first :: middle ++ [last]) =
    first :: lower_mid ++ [last] ->
  andrew_upper_chain (first :: middle ++ [last]) =
    last :: upper_mid ++ [first] ->
  Forall
    (fun q =>
       point_left_of_path_edges q (first :: rev upper_mid ++ [last]))
    (first :: middle ++ [last]) ->
  Forall
    (fun q =>
       point_left_of_path_edges q (last :: rev lower_mid ++ [first]))
    (first :: middle ++ [last]) ->
  is_max_hull'_edges
    (andrew_hull (first :: middle ++ [last]))
    (first :: middle ++ [last]).
Proof.
  intros first middle last lower_mid upper_mid Hsorted Hlower Hupper
    Hupper_cover Hlower_cover.
  unfold andrew_hull, andrew_merge.
  assert (Hmerge :
    andrew_ccw_merge
      (first :: middle ++ [last])
      (andrew_lower_chain (first :: middle ++ [last]))
      (andrew_upper_chain (first :: middle ++ [last])) =
      first :: lower_mid ++ last :: upper_mid).
  {
    eapply andrew_ccw_merge_endpoints; eauto.
  }
  rewrite Hmerge.
  unfold is_max_hull'_edges.
  rewrite Forall_forall in *.
  intros q Hq.
  destruct upper_mid as [| u upper_mid];
  destruct lower_mid as [| l lower_mid].
  - simpl.
    assert (Hfirstq : leftdown first q).
    {
      simpl in Hq.
      destruct Hq as [Hq | Hq].
      - subst q.
        apply leftdown_refl.
      - simpl in Hsorted.
        apply point_xy_sorted_from_leftdown_head in Hsorted.
        rewrite Forall_forall in Hsorted.
        apply Hsorted.
        exact Hq.
    }
    assert (Hqlast : leftdown q last).
    {
      pose proof (point_xy_sorted_all_leftdown_last
                    first middle last Hsorted) as Hall.
      rewrite Forall_forall in Hall.
      apply Hall.
      exact Hq.
    }
    specialize (Hupper_cover q Hq) as Hupper_q.
    specialize (Hlower_cover q Hq) as Hlower_q.
    simpl in Hupper_q, Hlower_q.
    destruct Hupper_q as [Hfl _].
    destruct Hlower_q as [Hlf _].
    eapply point_in_hull_edges_two_path_segment; eauto.
  - replace (rev (first :: (l :: lower_mid) ++ last :: []))
      with ([] ++ last :: rev (l :: lower_mid) ++ [first])
      by (simpl; rewrite rev_app_distr; simpl;
          repeat rewrite <- app_assoc; reflexivity).
    change (point_in_hull_edges q
      (rev (@nil point) ++ last :: rev (l :: lower_mid) ++ [first])).
    eapply (point_in_hull_edges_andrew_merge_from_two_paths
              q first (l :: lower_mid) last []).
    + right; discriminate.
    + apply Hupper_cover.
      exact Hq.
    + apply Hlower_cover.
      exact Hq.
  - replace (rev (first :: [] ++ last :: u :: upper_mid))
      with (rev (u :: upper_mid) ++ last :: rev [] ++ [first]).
    2: {
      simpl.
      repeat rewrite <- app_assoc.
      reflexivity.
    }
    eapply (point_in_hull_edges_andrew_merge_from_two_paths
              q first [] last (u :: upper_mid)).
    + left; discriminate.
    + apply Hupper_cover.
      exact Hq.
    + apply Hlower_cover.
      exact Hq.
  - replace (rev (first :: (l :: lower_mid) ++ last :: u :: upper_mid))
      with (rev (u :: upper_mid) ++ last :: rev (l :: lower_mid) ++ [first]).
    2: {
      simpl.
      rewrite rev_app_distr.
      simpl.
      repeat rewrite <- app_assoc.
      reflexivity.
    }
    eapply (point_in_hull_edges_andrew_merge_from_two_paths
              q first (l :: lower_mid) last (u :: upper_mid)).
    + left; discriminate.
    + apply Hupper_cover.
      exact Hq.
    + apply Hlower_cover.
      exact Hq.
Qed.

Lemma andrew_hull_max_from_algorithmic_open_edge_covers :
  forall sorted,
  point_xy_sorted sorted ->
  point_list_non_singleton sorted ->
  (forall first middle last lower_mid upper_mid,
    sorted = first :: middle ++ [last] ->
    andrew_lower_chain sorted = first :: lower_mid ++ [last] ->
    andrew_upper_chain sorted = last :: upper_mid ++ [first] ->
    Forall
      (fun q =>
         point_left_of_path_edges q (first :: rev upper_mid ++ [last]))
      sorted) ->
  (forall first middle last lower_mid upper_mid,
    sorted = first :: middle ++ [last] ->
    andrew_lower_chain sorted = first :: lower_mid ++ [last] ->
    andrew_upper_chain sorted = last :: upper_mid ++ [first] ->
    Forall
      (fun q =>
         point_left_of_path_edges q (last :: rev lower_mid ++ [first]))
      sorted) ->
  is_max_hull'_edges (andrew_hull sorted) sorted.
Proof.
  intros sorted Hsorted Hnon Hupper_edges Hlower_edges.
  destruct (point_list_non_singleton_first_last sorted Hnon)
    as [first [middle [last Hshape]]].
  subst sorted.
  destruct (andrew_lower_chain_endpoints first middle last)
    as [lower_mid Hlower].
  destruct (andrew_upper_chain_endpoints first middle last)
    as [upper_mid Hupper].
  eapply andrew_hull_max_from_open_edge_covers.
  - exact Hsorted.
  - exact Hlower.
  - exact Hupper.
  - eapply Hupper_edges; eauto.
  - eapply Hlower_edges; eauto.
Qed.

Lemma weak_rev_ccw_list_app_prefix :
  forall p prefix suffix,
  weak_rev_ccw_list p (prefix ++ suffix) ->
  weak_rev_ccw_list p prefix.
Proof.
  intros p prefix suffix Hweak.
  rewrite weak_rev_ccw_list_app_iff in Hweak.
  tauto.
Qed.

Lemma point_in_hull_prepend_many_weak :
  forall p prefix CH q,
  weak_rev_ccw_list p (prefix ++ CH) ->
  point_in_hull q (p :: CH) ->
  point_in_hull q (p :: prefix ++ CH).
Proof.
  intros p prefix.
  induction prefix as [| a prefix IH]; intros CH q Hweak Hinh.
  - simpl.
    exact Hinh.
  - simpl in Hweak |- *.
    apply point_in_hull_cons_weak.
    + exact Hweak.
    + apply IH.
      * exact (proj2 Hweak).
      * exact Hinh.
Qed.

Lemma point_in_hull_append_many_weak :
  forall p suffix CH q,
  weak_rev_ccw_list p (CH ++ suffix) ->
  point_in_hull q (p :: CH) ->
  point_in_hull q (p :: CH ++ suffix).
Proof.
  intros p suffix.
  induction suffix as [| a suffix IH]; intros CH q Hweak Hinh.
  - rewrite app_nil_r.
    exact Hinh.
  - assert (Hsnoc : weak_rev_ccw_list p (CH ++ [a])).
    {
      assert (Hfull : weak_rev_ccw_list p ((CH ++ [a]) ++ suffix ++ [])).
      {
        rewrite app_nil_r.
        rewrite <- app_assoc.
        simpl.
        exact Hweak.
      }
      pose proof (weak_rev_ccw_list_remove_middle
                    p (CH ++ [a]) suffix [] Hfull) as Htmp.
      rewrite app_nil_r in Htmp.
      exact Htmp.
    }
    assert (Hstep : point_in_hull q (p :: CH ++ [a])).
    {
      apply point_in_hull_snoc_weak.
      - exact Hsnoc.
      - exact Hinh.
    }
    replace (CH ++ a :: suffix) with ((CH ++ [a]) ++ suffix)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
    + rewrite <- app_assoc.
      simpl.
      exact Hweak.
    + exact Hstep.
Qed.

Lemma is_max_hull'_of_two_fans_weak :
  forall p prefix joint suffix base,
  weak_rev_ccw_list p (prefix ++ joint :: suffix) ->
  Forall
    (fun q =>
       point_in_hull q (p :: prefix ++ [joint]) \/
       point_in_hull q (p :: joint :: suffix))
    base ->
  is_max_hull' p (prefix ++ joint :: suffix) base.
Proof.
  intros p prefix joint suffix base Hweak Hcover.
  unfold is_max_hull'.
  rewrite Forall_forall in *.
  intros q Hq.
  specialize (Hcover q Hq) as [Hupper | Hlower].
  - replace (prefix ++ joint :: suffix)
      with ((prefix ++ [joint]) ++ suffix)
      by (rewrite <- app_assoc; reflexivity).
    apply point_in_hull_append_many_weak.
    + rewrite <- app_assoc.
      exact Hweak.
    + exact Hupper.
  - apply point_in_hull_prepend_many_weak.
    + exact Hweak.
    + exact Hlower.
Qed.

(** These are the two [point_in_hull] fans of the reversed merged tail
    [first :: rev upper_mid ++ last :: rev lower_mid], not the raw semi-hull
    paths.  The upper fan is the prefix ending at [last]; the lower fan starts
    at [last] and then follows the reversed lower middle. *)
Lemma andrew_two_fan_cover_to_merged_max_weak :
  forall first last lower_mid upper_mid base,
  weak_rev_ccw_list first (rev upper_mid ++ last :: rev lower_mid) ->
  Forall
    (fun q =>
       point_in_hull q (first :: rev upper_mid ++ [last]) \/
       point_in_hull q (first :: last :: rev lower_mid))
    base ->
  is_max_hull' first (rev upper_mid ++ last :: rev lower_mid) base.
Proof.
  intros first last lower_mid upper_mid base Hweak Hcover.
  apply is_max_hull'_of_two_fans_weak.
  - exact Hweak.
  - exact Hcover.
Qed.

Lemma andrew_merged_triangle_max_of_two_fans :
  forall first middle last lower_mid upper_mid,
  leftmost first (lower_mid ++ last :: upper_mid) ->
  ccw_convex (first :: lower_mid ++ last :: upper_mid) ->
  Forall
    (fun q =>
       point_in_hull q (first :: rev upper_mid ++ [last]) \/
       point_in_hull q (first :: last :: rev lower_mid))
    (first :: middle ++ [last]) ->
  is_max_hull' first (rev (lower_mid ++ last :: upper_mid))
    (first :: middle ++ [last]).
Proof.
  intros first middle last lower_mid upper_mid Hleft Hconv Hcover.
  simpl.
  rewrite rev_app_distr.
  simpl.
  rewrite <- app_assoc.
  simpl.
  apply andrew_two_fan_cover_to_merged_max_weak.
  - destruct (ccw_convex_tail_sort_rev
                first (lower_mid ++ last :: upper_mid) Hleft Hconv)
      as [_ Hweak].
    simpl in Hweak.
    rewrite rev_app_distr in Hweak.
    simpl in Hweak.
    rewrite <- app_assoc in Hweak.
    simpl in Hweak.
    exact Hweak.
  - exact Hcover.
Qed.

Lemma weak_rev_ccw_list_lower_fan_from_merged_convex :
  forall first lower_mid last upper_mid,
  leftmost first (lower_mid ++ last :: upper_mid) ->
  ccw_convex (first :: lower_mid ++ last :: upper_mid) ->
  weak_rev_ccw_list first (last :: rev lower_mid).
Proof.
  intros first lower_mid last upper_mid Hleft Hconv.
  destruct (ccw_convex_tail_sort_rev
              first (lower_mid ++ last :: upper_mid) Hleft Hconv)
    as [_ Hweak].
  simpl in Hweak.
  rewrite rev_app_distr in Hweak.
  simpl in Hweak.
  rewrite <- app_assoc in Hweak.
  eapply (g_rev_ccw_list_ind' first (rev upper_mid)).
  exact Hweak.
Qed.

Lemma weak_rev_ccw_list_upper_fan_from_merged_convex :
  forall first lower_mid last upper_mid,
  leftmost first (lower_mid ++ last :: upper_mid) ->
  ccw_convex (first :: lower_mid ++ last :: upper_mid) ->
  weak_rev_ccw_list first (rev upper_mid ++ [last]).
Proof.
  intros first lower_mid last upper_mid Hleft Hconv.
  destruct (ccw_convex_tail_sort_rev
              first (lower_mid ++ last :: upper_mid) Hleft Hconv)
    as [_ Hweak].
  simpl in Hweak.
  rewrite rev_app_distr in Hweak.
  simpl in Hweak.
  rewrite <- app_assoc in Hweak.
  simpl in Hweak.
  replace (rev upper_mid ++ last :: rev lower_mid)
    with ((rev upper_mid ++ [last]) ++ rev lower_mid) in Hweak
    by (rewrite <- app_assoc; reflexivity).
  eapply weak_rev_ccw_list_app_prefix.
  exact Hweak.
Qed.

Lemma lower_fan_covers_endpoints :
  forall first lower_mid last upper_mid,
  leftmost first (lower_mid ++ last :: upper_mid) ->
  ccw_convex (first :: lower_mid ++ last :: upper_mid) ->
  point_in_hull first (first :: last :: rev lower_mid) /\
  point_in_hull last (first :: last :: rev lower_mid).
Proof.
  intros first lower_mid last upper_mid Hleft Hconv.
  pose proof (weak_rev_ccw_list_lower_fan_from_merged_convex
                first lower_mid last upper_mid Hleft Hconv) as Hweak.
  split.
  - apply gs_point_in_hull_anchor.
    + discriminate.
    + exact Hweak.
  - apply gs_point_in_hull_new_head.
    exact Hweak.
Qed.

Lemma lower_fan_covers_member :
  forall first lower_mid last upper_mid q,
  leftmost first (lower_mid ++ last :: upper_mid) ->
  ccw_convex (first :: lower_mid ++ last :: upper_mid) ->
  In q lower_mid ->
  point_in_hull q (first :: last :: rev lower_mid).
Proof.
  intros first lower_mid last upper_mid q Hleft Hconv Hq.
  pose proof (weak_rev_ccw_list_lower_fan_from_merged_convex
                first lower_mid last upper_mid Hleft Hconv) as Hweak.
  apply point_in_hull_member_weak with (CH := last :: rev lower_mid).
  - exact Hweak.
  - simpl.
    right.
    apply (proj1 (in_rev lower_mid q)).
    exact Hq.
Qed.

Lemma upper_fan_covers_member :
  forall first lower_mid last upper_mid q,
  leftmost first (lower_mid ++ last :: upper_mid) ->
  ccw_convex (first :: lower_mid ++ last :: upper_mid) ->
  In q upper_mid ->
  point_in_hull q (first :: rev upper_mid ++ [last]).
Proof.
  intros first lower_mid last upper_mid q Hleft Hconv Hq.
  pose proof (weak_rev_ccw_list_upper_fan_from_merged_convex
                first lower_mid last upper_mid Hleft Hconv) as Hweak.
  apply point_in_hull_member_weak with (CH := rev upper_mid ++ [last]).
  - exact Hweak.
  - rewrite in_app_iff.
    left.
    apply (proj1 (in_rev upper_mid q)).
    exact Hq.
Qed.

Lemma upper_fan_covers_endpoints :
  forall first lower_mid last upper_mid,
  leftmost first (lower_mid ++ last :: upper_mid) ->
  ccw_convex (first :: lower_mid ++ last :: upper_mid) ->
  point_in_hull first (first :: rev upper_mid ++ [last]) /\
  point_in_hull last (first :: rev upper_mid ++ [last]).
Proof.
  intros first lower_mid last upper_mid Hleft Hconv.
  pose proof (weak_rev_ccw_list_upper_fan_from_merged_convex
                first lower_mid last upper_mid Hleft Hconv) as Hweak.
  split.
  - apply gs_point_in_hull_anchor.
    + destruct (rev upper_mid ++ [last]) as [| a rest] eqn:Hfan.
      * apply app_eq_nil in Hfan as [_ Hlast_nil].
        discriminate Hlast_nil.
      * discriminate.
    + exact Hweak.
  - apply point_in_hull_last_weak.
    exact Hweak.
Qed.

Lemma andrew_retained_point_two_fan_cover :
  forall first middle last lower_mid upper_mid q,
  point_xy_sorted (first :: middle ++ [last]) ->
  andrew_lower_chain (first :: middle ++ [last]) =
    first :: lower_mid ++ [last] ->
  andrew_upper_chain (first :: middle ++ [last]) =
    last :: upper_mid ++ [first] ->
  In q lower_mid \/ In q upper_mid ->
  point_in_hull q (first :: rev upper_mid ++ [last]) \/
  point_in_hull q (first :: last :: rev lower_mid).
Proof.
  intros first middle last lower_mid upper_mid q
    Hsorted Hlower Hupper Hretained.
  assert (Hmerge :
    andrew_ccw_merge
      (first :: middle ++ [last])
      (andrew_lower_chain (first :: middle ++ [last]))
      (andrew_upper_chain (first :: middle ++ [last])) =
      first :: lower_mid ++ last :: upper_mid).
  {
    eapply andrew_ccw_merge_endpoints; eauto.
  }
  assert (Hconv : ccw_convex (first :: lower_mid ++ last :: upper_mid)).
  {
    pose proof (andrew_hull_convex
                  (first :: middle ++ [last]) Hsorted) as Hrevconv.
    unfold andrew_hull, andrew_merge in Hrevconv.
    rewrite Hmerge in Hrevconv.
    apply gs_rev_ccw_convex_to_ccw_convex_rev in Hrevconv.
    rewrite rev_involutive in Hrevconv.
    exact Hrevconv.
  }
  assert (Hleft : leftmost first (lower_mid ++ last :: upper_mid)).
  {
    eapply andrew_ccw_merge_leftmost; eauto.
  }
  destruct Hretained as [Hlower_q | Hupper_q].
  - right.
    eapply lower_fan_covers_member; eauto.
  - left.
    eapply upper_fan_covers_member; eauto.
Qed.

Lemma andrew_two_fan_cover_of_middle :
  forall first middle last lower_mid upper_mid,
  leftmost first (lower_mid ++ last :: upper_mid) ->
  ccw_convex (first :: lower_mid ++ last :: upper_mid) ->
  Forall
    (fun q =>
       point_in_hull q (first :: rev upper_mid ++ [last]) \/
       point_in_hull q (first :: last :: rev lower_mid))
    middle ->
  Forall
    (fun q =>
       point_in_hull q (first :: rev upper_mid ++ [last]) \/
       point_in_hull q (first :: last :: rev lower_mid))
    (first :: middle ++ [last]).
Proof.
  intros first middle last lower_mid upper_mid Hleft Hconv Hmiddle.
  pose proof (lower_fan_covers_endpoints
                first lower_mid last upper_mid Hleft Hconv)
    as [Hfirst Hlast].
  rewrite Forall_cons_iff.
  split.
  - right.
    exact Hfirst.
  - rewrite Forall_app.
    split.
    + exact Hmiddle.
    + rewrite Forall_cons_iff.
      split.
      * right.
        exact Hlast.
      * apply Forall_nil.
Qed.

Lemma andrew_two_fan_cover_from_side_covers :
  forall first middle last lower_mid upper_mid,
  Forall
    (fun q =>
       point_in_hull q (first :: last :: rev lower_mid) \/
       ccw first last q)
    middle ->
  Forall
    (fun q =>
       point_in_hull q (first :: rev upper_mid ++ [last]) \/
       ~ ccw first last q)
    middle ->
  Forall
    (fun q =>
       point_in_hull q (first :: rev upper_mid ++ [last]) \/
       point_in_hull q (first :: last :: rev lower_mid))
    middle.
Proof.
  intros first middle last lower_mid upper_mid Hlower Hupper.
  rewrite Forall_forall in *.
  intros q Hq.
  specialize (Hlower q Hq) as [Hlower_q | Habove].
  - right.
    exact Hlower_q.
  - specialize (Hupper q Hq) as [Hupper_q | Hnot_above].
    + left.
      exact Hupper_q.
    + contradiction.
Qed.

Lemma andrew_hull_max_from_middle_two_fan_cover :
  forall first middle last lower_mid upper_mid,
  point_xy_sorted (first :: middle ++ [last]) ->
  (** coexisting head & last *)
  andrew_lower_chain (first :: middle ++ [last]) =
    first :: lower_mid ++ [last] ->
  andrew_upper_chain (first :: middle ++ [last]) =
    last :: upper_mid ++ [first] ->
  (** semi-hull triangulation *)
  Forall
    (fun q =>
       point_in_hull q (first :: rev upper_mid ++ [last]) \/
       point_in_hull q (first :: last :: rev lower_mid))
    middle ->
  (** full-hull left-to-edges *)
  is_max_hull'_edges
    (andrew_hull (first :: middle ++ [last]))
    (first :: middle ++ [last]).
Proof.
  intros first middle last lower_mid upper_mid
    Hsorted Hlower Hupper Hmiddle.
  assert (Hmerge :
    andrew_ccw_merge
      (first :: middle ++ [last])
      (andrew_lower_chain (first :: middle ++ [last]))
      (andrew_upper_chain (first :: middle ++ [last])) =
      first :: lower_mid ++ last :: upper_mid).
  {
    eapply andrew_ccw_merge_endpoints; eauto.
  }
  assert (Hconv : ccw_convex (first :: lower_mid ++ last :: upper_mid)).
  {
    pose proof (andrew_hull_convex
                  (first :: middle ++ [last]) Hsorted) as Hrevconv.
    unfold andrew_hull, andrew_merge in Hrevconv.
    rewrite Hmerge in Hrevconv.
    apply gs_rev_ccw_convex_to_ccw_convex_rev in Hrevconv.
    rewrite rev_involutive in Hrevconv.
    exact Hrevconv.
  }
  assert (Hleft : leftmost first (lower_mid ++ last :: upper_mid)).
  {
    eapply andrew_ccw_merge_leftmost; eauto.
  }
  assert (Hcover :
    Forall
      (fun q =>
         point_in_hull q (first :: rev upper_mid ++ [last]) \/
         point_in_hull q (first :: last :: rev lower_mid))
      (first :: middle ++ [last])).
  {
    eapply andrew_two_fan_cover_of_middle; eauto.
  }
  assert (Hmax :
    is_max_hull' first (rev (lower_mid ++ last :: upper_mid))
      (first :: middle ++ [last])).
  {
    eapply andrew_merged_triangle_max_of_two_fans; eauto.
  }
  eapply andrew_merged_triangle_max_to_edges; eauto.
Qed.

Lemma andrew_chains_endpoints_coexist :
  forall sorted,
  point_list_non_singleton sorted ->
  exists first middle last lower_mid upper_mid,
    sorted = first :: middle ++ [last] /\
    andrew_lower_chain sorted = first :: lower_mid ++ [last] /\
    andrew_upper_chain sorted = last :: upper_mid ++ [first].
Proof.
  intros sorted Hnon.
  destruct (point_list_non_singleton_first_last sorted Hnon)
    as [first [middle [last Hsorted]]].
  subst sorted.
  destruct (andrew_lower_chain_endpoints first middle last)
    as [lower_mid Hlower].
  destruct (andrew_upper_chain_endpoints first middle last)
    as [upper_mid Hupper].
  exists first, middle, last, lower_mid, upper_mid.
  repeat split; assumption.
Qed.

Lemma andrew_hull_max_from_algorithmic_two_fan_cover :
  forall sorted,
  point_xy_sorted sorted ->
  point_list_non_singleton sorted ->
  (forall first middle last lower_mid upper_mid,
    sorted = first :: middle ++ [last] ->
    andrew_lower_chain sorted = first :: lower_mid ++ [last] ->
    andrew_upper_chain sorted = last :: upper_mid ++ [first] ->
    Forall
      (fun q =>
         point_in_hull q (first :: rev upper_mid ++ [last]) \/
         point_in_hull q (first :: last :: rev lower_mid))
      middle) ->
  is_max_hull'_edges (andrew_hull sorted) sorted.
Proof.
  intros sorted Hsorted Hnon Hcover.
  destruct (andrew_chains_endpoints_coexist sorted Hnon)
    as [first [middle [last [lower_mid [upper_mid
       [Hshape [Hlower Hupper]]]]]]].
  subst sorted.
  eapply andrew_hull_max_from_middle_two_fan_cover.
  - exact Hsorted.
  - exact Hlower.
  - exact Hupper.
  - eapply Hcover; eauto.
Qed.

Lemma andrew_hull_max_from_algorithmic_side_covers :
  forall sorted,
  point_xy_sorted sorted ->
  point_list_non_singleton sorted ->
  (forall first middle last lower_mid upper_mid,
    sorted = first :: middle ++ [last] ->
    andrew_lower_chain sorted = first :: lower_mid ++ [last] ->
    andrew_upper_chain sorted = last :: upper_mid ++ [first] ->
    Forall
      (fun q =>
         point_in_hull q (first :: last :: rev lower_mid) \/
         ccw first last q)
      middle) ->
  (forall first middle last lower_mid upper_mid,
    sorted = first :: middle ++ [last] ->
    andrew_lower_chain sorted = first :: lower_mid ++ [last] ->
    andrew_upper_chain sorted = last :: upper_mid ++ [first] ->
    Forall
      (fun q =>
         point_in_hull q (first :: rev upper_mid ++ [last]) \/
         ~ ccw first last q)
      middle) ->
  is_max_hull'_edges (andrew_hull sorted) sorted.
Proof.
  intros sorted Hsorted Hnon Hlower Hupper.
  eapply andrew_hull_max_from_algorithmic_two_fan_cover; eauto.
  intros first middle last lower_mid upper_mid
    Hshape Hlower_shape Hupper_shape.
  eapply andrew_two_fan_cover_from_side_covers.
  - eapply Hlower; eauto.
  - eapply Hupper; eauto.
Qed.

Lemma andrew_hull_max_f : forall sorted,
  point_xy_sorted sorted ->
  point_list_non_singleton sorted ->
  is_max_hull'_edges (andrew_hull sorted) sorted.
Proof.
  intros sorted Hsorted Hnon.
  eapply andrew_hull_max_from_algorithmic_open_edge_covers; eauto.
  - intros first middle last lower_mid upper_mid
      Hshape Hlower Hupper.
    subst sorted.
    eapply andrew_upper_chain_open_edge_cover; eauto.
  - intros first middle last lower_mid upper_mid
      Hshape Hlower Hupper.
    subst sorted.
    eapply andrew_lower_chain_open_edge_cover; eauto.
Qed.

Theorem andrew_hull_max : forall sorted,
  point_xy_sorted sorted ->
  point_list_non_singleton sorted ->
  is_max_hull'_edges (andrew_hull sorted) sorted.
Proof.
  exact andrew_hull_max_f.
Qed.




Definition andrew_hull_geometry_from_sorting (sorted : list point) : Prop :=
  point_xy_sorted sorted ->
  point_list_non_singleton sorted ->
  andrew_hull_geometry sorted.

Lemma andrew_hull_geometry_from_sorting_correct : forall sorted,
  andrew_hull_geometry_from_sorting sorted.
Proof.
  unfold andrew_hull_geometry_from_sorting, andrew_hull_geometry.
  intros sorted Hsorted Hnonsingleton.
  split.
  - exact Hnonsingleton.
  - split.
    + apply andrew_hull_convex.
      exact Hsorted.
    + apply andrew_hull_max; assumption.
Qed.

Lemma andrew_hull_geometry_is_convex_hull : forall sorted T,
  T = andrew_hull sorted ->
  andrew_hull_geometry sorted ->
  is_convex_hull sorted T.
Proof.
  intros sorted T HT Hgeom.
  subst T.
  exact (proj2 Hgeom).
Qed.
