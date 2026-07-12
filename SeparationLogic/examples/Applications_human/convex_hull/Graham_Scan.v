(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From SimpleC.EE.Applications_human.convex_hull Require Import
  Geo_Point_Primitives Convexity Maximality.
Local Open Scope Z.
Import ListNotations.
(* /COQ-HEAD *)

(** Graham scan over input already ordered around its anchor. The stack head is
    the most recently accepted point; non-left turns are removed before the
    next point is pushed. *)

(* ========================== *)
(*      Main Algorithm        *)
(* ========================== *)

Fixpoint graham_scan_inc (p : point) (T : list point) : list point :=
  match T with
  | t :: T' =>
    match T' with
    | s :: _ =>
      match (ccw_dec s t p) with
      (* ccw s t p, push stack *)
      | left _ => p :: T
      (* ~ ccw s t p, pop stack & recursion *)
      | right _ => graham_scan_inc p T'
      end
    (* T = [t], push stack *)
    | _ => p :: T
    end
  (* T = [], untouched *)
  | _ => p :: T
  end.

(** append point AFTER pop several points *)

Fixpoint graham_scan (l: list point) : list point :=
  (* fold_right graham_scan_inc nil l *)
  match l with
  | p :: l' => graham_scan_inc p (graham_scan l')
  | _ => nil
  end.

Lemma fold_left_graham_scan_inc_cons : forall p l,
  fold_left (fun T q => graham_scan_inc q T) l [p] =
  graham_scan (rev (p :: l)).
Proof.
  assert (Hfold : forall l,
    graham_scan l = fold_right graham_scan_inc [] l).
  {
    induction l as [| q l IH]; simpl.
    - reflexivity.
    - f_equal.
  }
  intros p l.
  rewrite Hfold.
  rewrite fold_left_rev_right.
  simpl.
  reflexivity.
Qed.

(** Legacy alternate formulation retained for compatibility. The verified
    implementation in this development is [graham_scan]. *)
Fixpoint graham_scan_inc' (p : point) (T : list point) : list point :=
  match T with
  | p1 :: T' =>
    match T' with
    | p0 :: _ =>
      match (ccw_dec p0 p1 p) with
      | left _ => T
      | right _ => graham_scan_inc' p T'
      end
    | _ => T
    end
  | _ => T
  end.

Definition graham_scan' (l : list point) : list point :=
  match l with
  | p :: l' => p :: (graham_scan_inc' p l')
  | _ => nil
  end.

(** Proof *)
(*  After the i’th iteration,
the vertices on the stack are the vertices of C_i
in clockwise order.  *)
(* Prove that [graham_scan T] is subset of T while preserving order *)
Lemma succ_stack : forall (a : point) (T : list point),
  exists T0 T', T = T0 ++ T' /\ graham_scan_inc a T = a :: T'.
Proof.
  intros; destruct T.
  - exists [], []. split; reflexivity.
  - destruct T.
    + exists [], [p]. split; reflexivity.
    + revert a p p0.
      induction T; intros.
      * simpl; destruct (ccw_dec p0 p a).
        exists [], [p ; p0]. split; reflexivity.
        exists [p], [p0]. split; reflexivity.
      * pose proof IHT a0 p0 a.
        pose proof IHT a0 p p0.
        destruct H as [T0 [T' [H1 H2]]].
        destruct H0 as [T1 [T'' [H3 H4]]].
        simpl in H4. simpl. destruct (ccw_dec p0 p a0).
        exists [], (p :: p0 :: a :: T). split; reflexivity.
        simpl in H2. destruct (ccw_dec a p0 a0).
        exists [p], (p0 :: a :: T). split; reflexivity.
        exists (p :: T0), T'.
        split.
        rewrite H1. reflexivity.
        assumption.
Qed.

Lemma graham_scan_subset : forall p T,
  sort p T ->
  (forall x,
  In x (graham_scan T) ->
  In x T).
Proof.
  induction T; [tauto| ].
  intros. simpl in H0.
  pose proof succ_stack a (graham_scan T) as [? [? [? ?]]].
  rewrite H1, H2 in *.
  destruct H0; [ left; tauto| ].
  right. apply IHT.
  - pose proof sort_ind p [a] T H. tauto.
  - pose proof in_or_app x0 x1 x as H3.
    apply H3. tauto.
Qed.

Theorem Forall_ccw_conv : forall (p q : point) (T : list point),
  Forall_ccw p q T -> Forall_ccw p q (graham_scan T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof Forall_ccw_ind p q a [] T H.
  specialize (IHT H0).
  pose proof succ_stack a (graham_scan T).
  destruct H1 as [T0 [T' [H1 H2]]].
  induction T0; rewrite H1 in *; rewrite H2.
  - rewrite Forall_ccw_cons_iff in H |- *.
    tauto.
  - simpl in IHT.
    rewrite Forall_ccw_cons_iff in H, IHT |- *.
    pose proof Forall_ccw_ind' p q T0 T'.
    tauto.
Qed.

Theorem Forall_g_rev_ccw_conv : forall (p q : point) (T : list point),
  Forall_g_rev_ccw p q T -> Forall_g_rev_ccw p q (graham_scan T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof Forall_g_rev_ccw_ind p q a [] T H.
  specialize (IHT H0).
  pose proof succ_stack a (graham_scan T).
  destruct H1 as [T0 [T' [H1 H2]]].
  induction T0; rewrite H1 in *; rewrite H2.
  - rewrite Forall_g_rev_ccw_cons_iff in H |- *.
    tauto.
  - simpl in IHT.
    rewrite Forall_g_rev_ccw_cons_iff in H, IHT |- *.
    pose proof Forall_g_rev_ccw_ind' p q T0 T'.
    tauto.
Qed.

Theorem g_rev_ccw_list_conv : forall (p : point) (T : list point),
  g_rev_ccw_list p T -> g_rev_ccw_list p (graham_scan T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof g_rev_ccw_list_ind' p [a] T H.
  specialize (IHT H0).
  pose proof succ_stack a (graham_scan T).
  destruct H1 as [T0 [T' [H1 H2]]].
  induction T0; simpl in H1; rewrite H1 in *; rewrite H2;
  destruct H; split.
  - pose proof Forall_g_rev_ccw_conv p a T H.
    rewrite <- H1. assumption.
  - assumption.
  - pose proof Forall_g_rev_ccw_conv p a T H.
    rewrite H1 in H4.
    pose proof Forall_g_rev_ccw_ind' p a (a0 :: T0) T'.
    apply (H5 H4).
  - destruct IHT.
    pose proof g_rev_ccw_list_ind' p T0 T'.
    apply (H6 H5).
Qed.

Theorem g_rev_ccw_list_convex_ind : forall (p q : point) (T : list point),
  g_rev_ccw_list p (q :: T) -> is_convex p T -> is_convex p (graham_scan_inc q T).
Proof.
  intros. destruct H.
  destruct T; try eauto.
  generalize dependent p0.
  induction T; intros; simpl; try eauto.
  destruct (ccw_dec a p0 q).
  - rewrite Forall_g_rev_ccw_cons_iff in H.
    destruct H as [Hqp0 Hqa].
    repeat split; try assumption;
    try (apply ccw_cyclicity; assumption);
    try (apply ccw_cyclicity_2; assumption).
    rewrite Forall_g_rev_ccw_cons_iff in Hqa.
    destruct Hqa as [Hqa _].
    exact (g_rev_ccw_head_strict p q p0 a Hqp0 Hqa c).
  - pose proof IHT a.
    pose proof Forall_g_rev_ccw_ind p q p0 [] (a :: T) H.
    pose proof g_rev_ccw_list_ind' p [p0] (a :: T) H1.
    pose proof convex_ind p p0 (a :: T) H0.
    specialize (H2 H3 H4 H5). assumption.
Qed.


(** Prove that if a list of point is sorted by p, then it will be convex after applying graham_scan. *)
Theorem graham_convex_1 : forall (p : point) (T : list point),
  sort p T -> is_convex p (graham_scan T).
Proof.
  unfold sort; intros. destruct H as [_ H].
  induction T; simpl; try eauto.
  pose proof g_rev_ccw_list_ind' p [a] T H. specialize (IHT H0).
  pose proof g_rev_ccw_list_convex_ind p a (graham_scan T) as H1.
  apply H1; try assumption. clear H0 H1.
  simpl in *. destruct H. split.
  - apply Forall_g_rev_ccw_conv. assumption.
  - apply g_rev_ccw_list_conv. assumption.
Qed.

(* ===================== *)


Lemma sort_gs_g_rev_ccw_list : forall p T,
  sort p T ->
  g_rev_ccw_list p (graham_scan T).
Proof.
  intros.
  destruct H as [_ H].
  apply g_rev_ccw_list_conv.
  exact H.
Qed.

Lemma sort_gs_g_rev_ccw_list' : forall p a T,
  sort p (a :: T) ->
  g_rev_ccw_list p (a :: graham_scan T).
Proof.
  intros.
  destruct H as [_ [? ?]].
  split.
  - apply Forall_g_rev_ccw_conv; tauto.
  - apply g_rev_ccw_list_conv; tauto.
Qed.

(* Print graham_convex_1. *)
(* forall (p : point) (T : list point),
   sort p T -> is_convex p (graham_scan T) *)


Lemma sort_gs_consec_ccw : forall p T,
  sort p T ->
  rev_consec_ccw (graham_scan T).
Proof.
  intros p T Hsort.
  apply (is_convex_rev_consec p (graham_scan T)).
  apply graham_convex_1.
  exact Hsort.
Qed.


(** Prove that stack incrementation preserves is_max_hull' *)
Lemma hull_inc : forall p a T,
  sort p (a :: T) ->
  is_max_hull' p (graham_scan T) T ->
  is_max_hull' p (graham_scan (a :: T)) T.
Proof.
  intros. simpl.
  pose proof sort_gs_consec_ccw p (a :: T) H as Hconsec.
  pose proof sort_ind p [a] T H as H_.
  pose proof sort_gs_consec_ccw p T H_.
  pose proof sort_gs_g_rev_ccw_list' p a T H as Hcl.
  clear H_.
  (** assert (is_max_hull' p (a :: graham_scan T) T) *)
  simpl in Hconsec, Hcl, H1.
  remember (graham_scan T) as l. clear Heql.
  assert (is_max_hull' p (a :: l) T).
    {
      destruct l.
      - unfold is_max_hull' in *. simpl in *.
        destruct T; [apply Forall_nil|].
        pose proof (forall_false_elim _ _ H0). tauto.
      - destruct l.
        + unfold is_max_hull' in *. simpl in *.
          destruct Hcl as [Hcl _];
          rewrite Forall_g_rev_ccw_cons_iff in Hcl;
          destruct Hcl as [Hcl _].
          rewrite Forall_forall in H0; rewrite Forall_forall.
          intros.
          pose proof (H0 x) H2. left.
          destruct H3 as [Hcol Hmid].
          exact (point_in_tri_weak_edge p x a p0 Hcl Hcol Hmid).
        +
          unfold is_max_hull' in *.
          rewrite Forall_forall in H0. rewrite Forall_forall.
          intros x HIn. specialize (H0 x HIn).
          simpl in H0 |- *.
          right. exact H0.
    }
  destruct l. 1: { unfold is_max_hull'. simpl. tauto. }
  clear H0.
  revert p0 H1 H2 Hconsec Hcl.
  induction l. 1: {
    unfold is_max_hull' in *.
    simpl; intros.
    destruct T; tauto.
  }
  intros.
  simpl. simpl in Hconsec.
  (** is_max_hull' p (graham_scan_inc a (p0 :: a0 :: l)) T *)
  destruct (ccw_dec a0 p0 a). 1: { tauto. }
  (** Hconsec : rev_consec_ccw (graham_scan_inc a (a0 :: l))*)
  (** Hcl: g_rev_ccw_list p (graham_scan_inc a (a0 :: l)) *)
  (** (1/1): is_max_hull' p (graham_scan_inc a (a0 :: l)) T *)
  (* ? *)
  apply (IHl a0); try tauto.
  - apply rev_consec_ccw_cons_iff in H1 as [? _]. tauto.
  (** is_max_hull' p (a :: p0 :: a0 :: l) T -> is_max_hull' p (a :: a0 :: l) T *)
  - apply (is_max_hull'_pop'_g p a0 p0 a l T).
    + exact Hcl.
    + assumption.
    + assumption.
  - pose proof g_rev_ccw_list_remove_middle p [a] [p0] (a0 :: l) Hcl as Hcl'.
    exact Hcl'.
Qed.

Theorem graham_convex_2 : forall p T,
  sort p T -> is_max_hull' p (graham_scan T) T.
Proof.
  induction T; [unfold is_max_hull'; eauto|].
  intros.
  pose proof sort_ind _ [a] _ H as H_.
  specialize (IHT H_); clear H_.
  unfold is_max_hull'. rewrite Forall_cons_iff; split.
  - simpl.
    pose proof succ_stack a (graham_scan T) as [? [? [? ?]]].
    rewrite H1.
    destruct x0.
    + (** point_in_hull 2point *)
      simpl;
      unfold colinear, parallel, at_mid, backward_or_perp;
      unfold cross_prod, dot_prod;
      simpl; split; lia.
    + left.
      apply point_in_tri_1.
      pose proof sort_gs_g_rev_ccw_list' p a T H as Hcl.
      rewrite H0 in *.
      simpl in Hcl.
      destruct Hcl as [Ha _].
      rewrite Forall_g_rev_ccw_forall in Ha.
      specialize (Ha p0 ltac:(rewrite in_app_iff; simpl; tauto)).
      destruct Ha as [Hap0 | [Hcol Hmid]].
      * exact (ccw_anti_symmetry _ _ _ Hap0).
      * unfold ccw, colinear, left_than, parallel, cross_prod, build_vec in *;
        simpl in *; nia.
  - apply hull_inc; tauto.
Qed.
