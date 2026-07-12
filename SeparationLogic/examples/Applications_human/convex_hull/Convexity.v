(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From SimpleC.EE.Applications_human.convex_hull Require Export Geo_Point_Primitives.
Local Open Scope Z.
Import ListNotations.
Import GeoNotations.
(* /COQ-HEAD *)

Definition Forall_ccw (p q: point) (P: list point): Prop :=
  Forall (ccw p q) P.

Lemma Forall_ccw_g_ccw: forall p q l,
  Forall_ccw p q l ->
  Forall (g_ccw p q) l.
Proof.
  intros p q l.
  apply Forall_impl.
  intros a.
  apply ccw_g_ccw.
Qed.

Lemma Forall_ccw_cons_iff:
  forall p q a l,
    Forall_ccw p q (a :: l) <->
    ccw p q a /\ Forall_ccw p q l.
Proof. intros. apply Forall_cons_iff. Qed.

Lemma Forall_ccw_nil_iff:
  forall p q,
    Forall_ccw p q nil <-> True.
Proof. intros. apply Forall_nil_iff. Qed.

Lemma Forall_ccw_app:
  forall p q l1 l2,
    Forall_ccw p q (l1 ++ l2) <->
    Forall_ccw p q l1 /\ Forall_ccw p q l2.
Proof. intros. apply Forall_app. Qed.

Lemma Forall_ccw_forall:
  forall p q l,
    Forall_ccw p q l <-> forall r, In r l -> ccw p q r.
Proof. intros. apply Forall_forall. Qed.

Lemma Forall_ccw_ind : forall (p q r : point) (P P' : list point),
  Forall_ccw p q (P ++ r :: P') -> Forall_ccw p q (P ++ P').
Proof.
  intros p q ? ? ?.
  rewrite !Forall_ccw_app.
  rewrite Forall_ccw_cons_iff.
  tauto.
Qed.

Lemma Forall_ccw_ind' : forall (p q : point) (T0 T : list point),
  Forall_ccw p q (T0 ++ T) -> Forall_ccw p q T.
Proof.
  intros p q ? ? .
  rewrite !Forall_ccw_app.
  tauto.
Qed.

Fixpoint ccw_list (p: point) (l: list point): Prop :=
  match l with
  | cons q l0 => Forall_ccw p q l0 /\ ccw_list p l0
  | nil => True
  end.

Fixpoint g_ccw_list (p: point) (l: list point): Prop :=
  match l with
  | cons q l0 => Forall (g_ccw p q) l0 /\ g_ccw_list p l0
  | nil => True
  end.

Lemma g_ccw_ccw_list: forall p l,
  ccw_list p l ->
  g_ccw_list p l.
Proof.
  intros.
  induction l; simpl in *.
  + tauto.
  + destruct H.
    pose proof Forall_ccw_g_ccw p a l.
    tauto.
Qed.

Lemma ccw_list_app_iff: forall p l1 l2,
  ccw_list p (l1 ++ l2) <->
    ccw_list p l1 /\
    ccw_list p l2 /\
    (forall q r, In q l1 -> In r l2 -> ccw p q r).
Proof.
  intros.
  split; induction l1; simpl.
  + tauto.
  + intros.
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_ccw_app in H.
    destruct IHl1 as [? [? ?]], H as [[? ?] ?].
    repeat split; try tauto.
    intros.
    destruct H5; [| apply H2; tauto].
    subst q.
    rewrite Forall_ccw_forall in H3.
    apply H3; tauto.
  + tauto.
  + intros [[? ?] [? ?]].
    assert (forall q r, In q l1 -> In r l2 -> ccw p q r)
      by (intros; apply H2; tauto).
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_ccw_app.
    repeat split; try tauto.
    rewrite Forall_ccw_forall.
    intros; apply H2; tauto.
Qed.

Lemma g_ccw_list_app_iff: forall p l1 l2,
  g_ccw_list p (l1 ++ l2) <->
    g_ccw_list p l1 /\
    g_ccw_list p l2 /\
    (forall q r, In q l1 -> In r l2 -> g_ccw p q r).
Proof.
  intros.
  split; induction l1; simpl.
  + tauto.
  + intros.
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_app in H.
    destruct IHl1 as [? [? ?]], H as [[? ?] ?].
    repeat split; try tauto.
    intros.
    destruct H5; [| apply H2; tauto].
    subst q.
    rewrite Forall_forall in H3.
    apply H3; tauto.
  + tauto.
  + intros [[? ?] [? ?]].
    assert (forall q r, In q l1 -> In r l2 -> g_ccw p q r)
      by (intros; apply H2; tauto).
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_app.
    repeat split; try tauto.
    rewrite Forall_forall.
    intros; apply H2; tauto.
Qed.

Lemma g_ccw_list_snoc_iff: forall p l q,
  g_ccw_list p (l ++ q :: nil) <->
  g_ccw_list p l /\ Forall (fun r => g_ccw p r q) l.
Proof.
  intros.
  induction l.
  + simpl.
    rewrite !Forall_nil_iff.
    tauto.
  + simpl.
    rewrite Forall_cons_iff.
    rewrite Forall_app, Forall_cons_iff, Forall_nil_iff.
    tauto.
Qed.

Lemma g_ccw_list_remove_middle: forall p l1 l2 l3,
  g_ccw_list p (l1 ++ l2 ++ l3) ->
  g_ccw_list p (l1 ++ l3).
Proof.
  intros.
  rewrite g_ccw_list_app_iff.
  rewrite !g_ccw_list_app_iff in H.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  split; [| split]; try tauto.
  intros.
  apply H1; try tauto.
  rewrite in_app_iff.
  tauto.
Qed.

Fixpoint ccw_convex (l: list point): Prop :=
  match l with
  | cons p l0 => ccw_list p l0 /\ ccw_convex l0
  | nil => True
  end.

Lemma ccw_convex_rotate1: forall p l,
  ccw_convex (p :: l) ->
  ccw_convex (l ++ p :: nil).
Proof.
  intros.
  simpl in H.
  destruct H.
  induction l; simpl in *.
  + tauto.
  + split; [| tauto].
    apply ccw_list_app_iff.
    simpl.
    rewrite Forall_ccw_nil_iff.
    repeat split; try tauto.
    intros ? ? ? [? |[]].
    subst r.
    destruct H.
    rewrite Forall_ccw_forall in H.
    apply ccw_cyclicity.
    apply H; tauto.
Qed.

Lemma ccw_convex_app_comm: forall l1 l2,
  ccw_convex (l1 ++ l2) ->
  ccw_convex (l2 ++ l1).
Proof.
  intros.
  revert l2 H; induction l1; simpl app; intros.
  + rewrite app_nil_r.
    tauto.
  + specialize (IHl1 (l2 ++ a :: nil)).
    rewrite <- app_assoc in IHl1.
    simpl app in IHl1.
    apply IHl1.
    rewrite app_assoc.
    apply ccw_convex_rotate1.
    tauto.
Qed.

Lemma ccw_list_forall2: forall p l,
  (forall l1 q l2 r l3, l = l1 ++ q :: l2 ++ r :: l3 -> ccw p q r) ->
  ccw_list p l.
Proof.
  intros.
  induction l; [simpl; tauto |].
  simpl.
  split.
  - clear IHl.
    rewrite Forall_ccw_forall.
    intros r ?.
    apply in_split in H0.
    destruct H0 as [l1 [l2 ?]].
    specialize (H nil a l1 r l2).
    rewrite H0 in H.
    apply H; reflexivity.
  - apply IHl.
    intros.
    specialize (H (a :: l1) q l2 r l3).
    apply H; rewrite H0; reflexivity.
Qed.

Lemma ccw_convex_forall3: forall l,
  (forall l1 p l2 q l3 r l4,
     l = l1 ++ p :: l2 ++ q :: l3 ++ r :: l4 -> ccw p q r) ->
  ccw_convex l.
Proof.
  intros.
  induction l; [simpl; tauto |].
  simpl.
  split.
  + clear IHl.
    apply ccw_list_forall2.
    intros.
    specialize (H nil a l1 q l2 r l3).
    apply H; rewrite H0; reflexivity.
  + apply IHl.
    intros.
    specialize (H (a :: l1) p l2 q l3 r l4).
    apply H; rewrite H0; reflexivity.
Qed.

Fixpoint consec_ccw (l: list point): Prop :=
  match l with
  | p :: _l =>
    match _l with
    | q :: r :: _ => ccw p q r
    | _ => True
    end /\ consec_ccw _l
  | _ => True
  end.

Lemma consec_ccw_cons_iff: forall a l,
  consec_ccw (a :: l) <->
  consec_ccw l /\ (forall b c l0, l = b :: c :: l0 -> ccw a b c).
Proof.
  intros.
  split; intros.
  + destruct H.
    split; [tauto |].
    intros.
    subst l.
    tauto.
  + destruct H.
    split; [| tauto].
    destruct l as [| ? [|]]; try tauto.
    specialize (H0 _ _ _ ltac:(reflexivity)).
    tauto.
Qed.

Lemma consec_ccw_cons3_iff: forall a b c l,
  consec_ccw (a :: b :: c :: l) <->
  consec_ccw (b :: c :: l) /\ ccw a b c.
Proof.
  intros.
  rewrite (consec_ccw_cons_iff a).
  assert ((forall b0 c0 l0, b :: c :: l = b0 :: c0 :: l0 -> ccw a b0 c0)
          <-> ccw a b c); [| tauto].
  split; intros.
  + eapply H; reflexivity.
  + injection H0 as ? ? _.
    subst.
    tauto.
Qed.

Lemma consec_ccw_spec: forall l,
  consec_ccw l <->
  (forall l1 p q r l2, l = l1 ++ p :: q :: r :: l2 -> ccw p q r).
Proof.
  intros.
  induction l.
  + simpl.
    split; [intros _ ? ? ? ? ? ? | tauto].
    destruct l1; discriminate H.
  + rewrite consec_ccw_cons_iff.
    rewrite IHl; clear IHl.
    split; [intros [? ?]; intros | intros; split].
    - destruct l1.
      * injection H1 as ? ?.
        subst.
        eapply H0.
        reflexivity.
      * injection H1 as ? ?.
        subst.
        eapply (H l1).
        reflexivity.
    - intros.
      eapply (H (a :: l1)).
      rewrite H0.
      reflexivity.
    - intros.
      eapply (H nil).
      rewrite H0.
      simpl.
      reflexivity.
Qed.

Lemma consec_ccw_snoc_iff: forall a l,
  consec_ccw (l ++ a :: nil) <->
  consec_ccw l /\ (forall b c l0, l = l0 ++ c :: b :: nil -> ccw c b a).
Proof.
  intros.
  destruct l as [| ? [|]].
  + simpl.
    assert (forall b c l0, [] = l0 ++ [c; b] -> ccw c b a); [| tauto].
    intros.
    destruct l0; discriminate H.
  + simpl.
    assert (forall b c l0, [p] = l0 ++ [c; b] -> ccw c b a); [| tauto].
    intros.
    destruct l0 as [| ? [|]]; discriminate H.
  + simpl app.
    revert p p0; induction l; intros.
    - simpl.
      assert (ccw p p0 a <->
              forall b c l0, [p; p0] = l0 ++ [c; b] -> ccw c b a); [| tauto].
      split.
      * intros.
        destruct l0 as [| ? [| ? [|]]]; [| discriminate H0 ..].
        injection H0 as ? ?.
        subst; tauto.
      * intros.
        apply (H _ _ nil).
        reflexivity.
    - simpl app.
      do 2 rewrite (consec_ccw_cons_iff p).
      rewrite IHl.
      clear IHl.
      split; intros [[? ?] ?]; (split; [split |]); try tauto.
      * intros.
        injection H2 as ? ? ?; subst.
        apply (H1 _ _ (l0 ++ [a])).
        reflexivity.
      * intros.
        destruct l0; [discriminate H2 | simpl in H2].
        injection H2 as ? ?.
        subst.
        apply (H0 _ _ l0); tauto.
      * intros.
        apply (H1 _ _ (p :: l0)).
        rewrite H2; reflexivity.
      * intros.
        injection H2 as ? ? ?; subst.
        eapply H0.
        reflexivity.
Qed.

Lemma consec_ccw_snoc3_iff: forall a b c l,
  consec_ccw (l ++ c :: b :: a :: nil) <->
  consec_ccw (l ++ c :: b :: nil) /\ ccw c b a.
Proof.
  intros.
  change (c :: b :: a :: nil) with ((c :: b :: nil) ++ (a :: nil)).
  rewrite app_assoc.
  rewrite consec_ccw_snoc_iff.
  assert ((forall b0 c0 l0, l ++ [c; b] = l0 ++ [c0; b0] -> ccw c0 b0 a) <->
          ccw c b a); [| tauto].
  split; intros.
  + eapply H; reflexivity.
  + change (c :: b :: nil) with ((c :: nil) ++ (b :: nil)) in H0.
    change (c0 :: b0 :: nil) with ((c0 :: nil) ++ (b0 :: nil)) in H0.
    rewrite !app_assoc in H0.
    rewrite !app_inj_tail_iff in H0.
    destruct H0 as [[? ?] ?]; subst.
    tauto.
Qed.

Lemma consec_ccw_app_inv1: forall l1 l2,
  consec_ccw (l1 ++ l2) ->
  consec_ccw l1.
Proof.
  intros.
  induction l1.
  + simpl; tauto.
  + destruct H.
    split; [| apply IHl1; tauto].
    clear H0 IHl1.
    destruct l1 as [| ? [|]]; simpl in *; tauto.
Qed.

Lemma consec_ccw_app_inv2: forall l1 l2,
  consec_ccw (l1 ++ l2) ->
  consec_ccw l2.
Proof.
  intros.
  induction l1.
  + exact H.
  + apply IHl1.
    destruct H; tauto.
Qed.

Lemma consec_ccw_head_elim1: forall s p0 p1 l,
  g_ccw_list s (p0 :: p1 :: l) ->
  consec_ccw (p0 :: p1 :: l) ->
  consec_ccw (p0 :: l).
Proof.
  intros.
  destruct l as [| p2 [| p3 ?]]; try (simpl; tauto).
  rewrite !consec_ccw_cons3_iff in *.
  split; [tauto |].
  simpl in H.
  destruct H as [? [? [? ?]]], H0 as [[? ?] ?].
  rewrite !Forall_cons_iff in H.
  rewrite !Forall_cons_iff in H1.
  rewrite !Forall_cons_iff in H2.
  apply (ccw_skip_head s p0 p1 p2 p3); try tauto.
Qed.

Lemma consec_ccw_head_elim: forall s p l1 l2,
  g_ccw_list s (p :: l1 ++ l2) ->
  consec_ccw (p :: l1 ++ l2) ->
  consec_ccw (p :: l2).
Proof.
  intros.
  induction l1 as [| p0 l1 IHl1].
  + simpl app in H0.
    tauto.
  + simpl in H.
    apply IHl1.
    - rewrite Forall_cons_iff in H.
      simpl. tauto.
    - simpl app in H0.
      revert H0; apply (consec_ccw_head_elim1 s).
      simpl.
      tauto.
Qed.

Lemma destruct_tail: forall {A: Type} (l: list A),
  {l = nil} + {exists a l', l = l' ++ a :: nil}.
Proof.
  induction l.
  + left.
    reflexivity.
  + right.
    destruct IHl.
    - exists a, nil.
      subst; reflexivity.
    - destruct e as [a0 [l' ?]].
      exists a0, (a :: l').
      subst.
      reflexivity.
Qed.

Lemma consec_ccw_tail_elim: forall s p l1 l2,
  g_ccw_list s ((l1 ++ l2) ++ p :: nil) ->
  consec_ccw ((l1 ++ l2) ++ p :: nil) ->
  consec_ccw (l1 ++ p :: nil).
Proof.
  intros s p l1.
  refine (rev_ind _ _ _).
  + intros.
    rewrite <- app_assoc in H0.
    simpl app in H0.
    tauto.
  + intros p0 ? IHl2 ? ?.
    rewrite app_assoc in H, H0.
    rewrite !g_ccw_list_snoc_iff in H.
    destruct H as [[? ?] ?].
    rewrite Forall_app, Forall_cons_iff in H2.
    destruct H2 as [? [? _]].
    apply IHl2.
    1: { rewrite g_ccw_list_snoc_iff. tauto. }
    clear IHl2.
    destruct (destruct_tail (l1 ++ l)) as [| [p1 [? ?l]]];
      try (rewrite e in *; simpl; tauto).
    rewrite l0 in *; clear l1 l l0.
    destruct (destruct_tail x) as [| [p2 [? ?l]]];
      try (rewrite e in *; simpl; tauto).
    subst x.
    rewrite <- !app_assoc; simpl.
    rewrite consec_ccw_snoc3_iff.
    do 2 rewrite <- app_assoc in H0; simpl  in H0.
    rewrite consec_ccw_snoc3_iff in H0.
    rewrite <- app_assoc in H0; simpl  in H0.
    rewrite consec_ccw_snoc3_iff in H0.
    split; [tauto |].
    rewrite !g_ccw_list_snoc_iff in H.
    rewrite !Forall_app, !Forall_cons_iff, !Forall_nil_iff in H1.
    rewrite !Forall_app, !Forall_cons_iff, !Forall_nil_iff in H2.
    rewrite !Forall_app, !Forall_cons_iff, !Forall_nil_iff in H.
    apply (ccw_skip_tail s p2 p1 p0 p);
    try tauto;
    try (apply ccw_cyclicity; tauto).
Qed.

Fixpoint ccw_list_consec (p: point) (l: list point): Prop :=
  match l with
  | nil => True
  | p0 :: l0 =>
    match l0 with
    | nil => True
    | p1 :: l1 => ccw p p0 p1
    end /\ ccw_list_consec p l0
  end.

Lemma ccw_list_consec_Forall_g_ccw_ccw: forall p q l,
  Forall (g_ccw p q) l ->
  ccw_list_consec p (q :: l) ->
  Forall_ccw p q l.
Proof.
  intros.
  induction l as [| r l IHl]; intros.
  + rewrite Forall_ccw_nil_iff.
    tauto.
  + rewrite Forall_ccw_cons_iff.
    change (ccw p q r /\ ccw_list_consec p (r :: l)) in H0.
    rewrite Forall_cons_iff in H.
    destruct H, H0.
    split; [tauto |].
    apply IHl; try tauto.
    destruct l as [| s l].
    1: { simpl; tauto. }
    change (ccw p r s /\ ccw_list_consec p (s :: l)) in H2.
    change (ccw p q s /\ ccw_list_consec p (s :: l)).
    destruct H2.
    split; [| tauto].
    rewrite Forall_cons_iff in H1.
    destruct H1.
    destruct H1 as [? | [? ?]]; [tauto |].
    pose proof ccw_ccw_colinear_shorter_impossible p q r s.
    tauto.
Qed.

Theorem ccw_convex_spec_origin: forall p l,
  g_ccw_list p l ->
  consec_ccw (p :: l) ->
  ccw_list p l.
Proof.
  intros.
  assert (ccw_list_consec p l).
  + destruct l as [| p0 [| p1 l]].
    1: { simpl; tauto. }
    1: { simpl; tauto. }
    rewrite consec_ccw_cons3_iff in H0.
    destruct H0.
    destruct H as [_ ?].
    change (ccw p p0 p1 /\ ccw_list_consec p (p1 :: l)).
    split; [tauto |].
    revert p0 p1 H H0 H1; induction l as [| p2 l IHl]; intros.
    1: { simpl; tauto. }
    rewrite consec_ccw_cons3_iff in H0.
    destruct H, H0.
    change (ccw p p1 p2 /\ ccw_list_consec p (p2 :: l)).
    assert (ccw p p1 p2).
    - rewrite Forall_cons_iff in H.
      destruct H as [? _].
      unfold g_ccw in H.
      destruct H; [tauto |].
      pose proof ccw_colinear_shorter_impossible p p0 p1 p2.
      tauto.
    - split; [tauto |].
      apply (IHl p1 p2); try tauto.
  + clear H0.
    induction l as [| p0 l IHl]; [simpl; tauto |].
    simpl in H |- *.
    destruct H.
    split.
    - clear - H H1.
      apply ccw_list_consec_Forall_g_ccw_ccw; tauto.
    - destruct H1.
      apply IHl; tauto.
Qed.

Theorem ccw_convex_spec_others: forall p l,
  g_ccw_list p l ->
  consec_ccw l ->
  ccw_convex l.
Proof.
  intros.
  apply ccw_convex_forall3.
  intros l1 q l2 r l3 s l4 ?.
  subst l.
  rewrite g_ccw_list_app_iff in H.
  destruct H as [_ [? _]].
  apply consec_ccw_app_inv2 in H0.
  clear l1.
  change (s :: l4) with (s :: nil ++ l4) in H, H0.
  rewrite !app_comm_cons in H, H0.
  change (r :: l3) with (r :: nil ++ l3) in H, H0.
  rewrite !app_comm_cons in H, H0.
  rewrite !app_assoc in H, H0.
  rewrite g_ccw_list_app_iff in H.
  destruct H as [? [_ _]].
  apply consec_ccw_app_inv1 in H0.
  pose proof consec_ccw_tail_elim _ _ _ _ H H0.
  clear H0.
  rewrite <- app_assoc in H.
  apply g_ccw_list_remove_middle in H.
  rewrite <- app_assoc in H, H1.
  simpl app in H, H1.
  revert H H1; apply consec_ccw_head_elim.
Qed.

Theorem ccw_convex_spec_simple: forall p l,
  ccw_list p l ->
  consec_ccw l ->
  ccw_convex (p :: l).
Proof.
  intros.
  simpl.
  split; [tauto |].
  apply g_ccw_ccw_list in H.
  revert H H0; apply ccw_convex_spec_others.
Qed.

Theorem ccw_convex_spec: forall p l,
  g_ccw_list p l ->
  consec_ccw (p :: l) ->
  ccw_convex (p :: l).
Proof.
  intros.
  simpl.
  split.
  + apply ccw_convex_spec_origin; tauto.
  + apply (ccw_convex_spec_others p).
    - tauto.
    - rewrite consec_ccw_cons_iff in H0.
      tauto.
Qed.

Theorem g_ccw_rep : forall p q ,
  g_ccw p p q /\ g_ccw q p p.
Proof.
  intros; repeat split.
  - unfold g_ccw; right.
    split.
    + unfold colinear, parallel, build_vec, cross_prod. simpl.
      lia.
    + unfold at_mid, backward_or_perp, build_vec, dot_prod. simpl.
      nia.
  - unfold g_ccw; right.
    split.
    + unfold colinear, parallel, build_vec, cross_prod. simpl.
      lia.
    + unfold at_mid, backward_or_perp, build_vec, dot_prod. simpl.
      nia.
Qed.

Lemma forall_inr_true : forall (A: Type) (P: Prop) (l: list A),
  Forall (fun q => P \/ True) l.
Proof.
  intros.
  induction l as [ | x l' IHl'].
  - apply Forall_nil.
  - apply Forall_cons.
    + tauto.
    + apply IHl'.
Qed.

Definition weak_rev_ccw (p q r: point): Prop :=
  ccw q p r \/ colinear p q r /\ at_mid r q p.

Lemma ccw_colinear_between_impossible : forall p q r s,
  colinear p q r ->
  at_mid r q p ->
  ccw q p s ->
  ccw s r q ->
  False.
Proof.
  intros p q r s Hcol Hmid Hqps Hsrq.
  pose proof ccw_cyclicity _ _ _ Hsrq as Hrqs.
  pose proof colinear_perm321 _ _ _ Hcol as Hrqp.
  assert (Hcross : cross_prod (build_vec r s) (build_vec r p) >= 0).
  {
    pose proof aux2 (build_vec r q) (build_vec r s) (build_vec r p) as Haux.
    pose proof left_than_nonzero2 _ _ Hrqs as Hnz_rq.
    rewrite nonzero_iff in Hnz_rq.
    assert (parallel (build_vec r p) (build_vec r q)) as Hprq.
    { apply parallel_sym. exact Hrqp. }
    unfold ccw, colinear, at_mid, left_than, parallel, backward_or_perp in *.
    rewrite dot_prod_comm with (v1 := build_vec r p) (v2 := build_vec r q) in Haux.
    nia.
  }
  unfold ccw, colinear, at_mid, left_than, parallel, backward_or_perp,
         build_vec, cross_prod, dot_prod in *; simpl in *.
  nia.
Qed.

Lemma ccw_double_colinear_between_impossible : forall p q r s,
  colinear p q r ->
  at_mid r q p ->
  colinear p q s ->
  at_mid s q p ->
  ccw s r q ->
  False.
Proof.
  intros p q r s Hcol Hmid Hcol_s Hmid_s Hsrq.
  assert (nonzero (build_vec p q)) as Hnz_pq.
  {
    unfold ccw in Hsrq.
    pose proof left_than_nonzero1 _ _ Hsrq as Hnz_sq.
    apply nonzero_sym in Hnz_sq.
    pose proof at_mid_nonzero1 _ _ _ Hmid_s Hnz_sq as Hnz_qp.
    apply nonzero_sym. exact Hnz_qp.
  }
  pose proof colinear_4p _ _ _ _ Hcol Hcol_s Hnz_pq as Hqrs.
  apply colinear_perm231 in Hqrs.
  unfold colinear, ccw, parallel, left_than, cross_prod, build_vec in *;
    simpl in *.
  nia.
Qed.

Lemma weak_rev_ccw_head_strict : forall p q r s,
  weak_rev_ccw p q r ->
  weak_rev_ccw p q s ->
  ccw s r q ->
  ccw r q p.
Proof.
  intros p q r s Hqr Hqs Hsrq.
  destruct Hqr as [Hqr | [Hcol Hmid]].
  - apply ccw_cyclicity_2. exact Hqr.
  - destruct Hqs as [Hqs | [Hcol_s Hmid_s]].
    + exact (False_rect _ (ccw_colinear_between_impossible p q r s
                             Hcol Hmid Hqs Hsrq)).
    + exact (False_rect _ (ccw_double_colinear_between_impossible p q r s
                             Hcol Hmid Hcol_s Hmid_s Hsrq)).
Qed.

Definition Forall_weak_rev_ccw (p q: point) (P: list point): Prop :=
  Forall (weak_rev_ccw p q) P.

Lemma Forall_weak_rev_ccw_cons_iff:
  forall p q a l,
    Forall_weak_rev_ccw p q (a :: l) <->
    weak_rev_ccw p q a /\ Forall_weak_rev_ccw p q l.
Proof. intros. apply Forall_cons_iff. Qed.

Lemma Forall_weak_rev_ccw_nil_iff:
  forall p q,
    Forall_weak_rev_ccw p q nil <-> True.
Proof. intros. apply Forall_nil_iff. Qed.

Lemma Forall_weak_rev_ccw_app:
  forall p q l1 l2,
    Forall_weak_rev_ccw p q (l1 ++ l2) <->
    Forall_weak_rev_ccw p q l1 /\ Forall_weak_rev_ccw p q l2.
Proof. intros. apply Forall_app. Qed.

Lemma Forall_weak_rev_ccw_forall:
  forall p q l,
    Forall_weak_rev_ccw p q l <->
    forall r, In r l -> weak_rev_ccw p q r.
Proof. intros. apply Forall_forall. Qed.

Lemma Forall_weak_rev_ccw_ind : forall (p q r : point) (P P' : list point),
  Forall_weak_rev_ccw p q (P ++ r :: P') ->
  Forall_weak_rev_ccw p q (P ++ P').
Proof.
  intros p q ? ? ?.
  rewrite !Forall_weak_rev_ccw_app.
  rewrite Forall_weak_rev_ccw_cons_iff.
  tauto.
Qed.

Lemma Forall_weak_rev_ccw_ind' : forall (p q : point) (T0 T : list point),
  Forall_weak_rev_ccw p q (T0 ++ T) -> Forall_weak_rev_ccw p q T.
Proof.
  intros p q ? ? .
  rewrite !Forall_weak_rev_ccw_app.
  tauto.
Qed.

Fixpoint weak_rev_ccw_list (p: point) (l: list point): Prop :=
  match l with
  | cons q l0 => Forall_weak_rev_ccw p q l0 /\ weak_rev_ccw_list p l0
  | nil => True
  end.

Lemma weak_rev_ccw_list_app_iff: forall p l1 l2,
  weak_rev_ccw_list p (l1 ++ l2) <->
    weak_rev_ccw_list p l1 /\
    weak_rev_ccw_list p l2 /\
    (forall q r, In q l1 -> In r l2 -> weak_rev_ccw p q r).
Proof.
  intros.
  split; induction l1; simpl.
  + tauto.
  + intros.
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_weak_rev_ccw_app in H.
    destruct IHl1 as [? [? ?]], H as [[? ?] ?].
    repeat split; try tauto.
    intros.
    destruct H5; [| apply H2; tauto].
    subst q.
    rewrite Forall_weak_rev_ccw_forall in H3.
    apply H3; tauto.
  + tauto.
  + intros [[? ?] [? ?]].
    assert (forall q r, In q l1 -> In r l2 -> weak_rev_ccw p q r)
      by (intros; apply H2; tauto).
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_weak_rev_ccw_app.
    repeat split; try tauto.
    rewrite Forall_weak_rev_ccw_forall.
    intros; apply H2; tauto.
Qed.

Lemma weak_rev_ccw_list_remove_middle: forall p l1 l2 l3,
  weak_rev_ccw_list p (l1 ++ l2 ++ l3) ->
  weak_rev_ccw_list p (l1 ++ l3).
Proof.
  intros.
  rewrite weak_rev_ccw_list_app_iff.
  rewrite !weak_rev_ccw_list_app_iff in H.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  split; [| split]; try tauto.
  intros.
  apply H1; try tauto.
  rewrite in_app_iff.
  tauto.
Qed.

Definition g_rev_ccw (p q r: point): Prop :=
  weak_rev_ccw p q r.

Definition Forall_g_rev_ccw (p q: point) (P: list point): Prop :=
  Forall_weak_rev_ccw p q P.

Definition g_rev_ccw_list (p: point) (l: list point): Prop :=
  weak_rev_ccw_list p l.

Lemma g_rev_ccw_iff_weak_rev_ccw : forall p q r,
  g_rev_ccw p q r <-> weak_rev_ccw p q r.
Proof. intros; reflexivity. Qed.

Lemma g_rev_ccw_iff_g_ccw_rev : forall p q r,
  g_rev_ccw p q r <-> g_ccw p r q.
Proof.
  intros p q r.
  unfold g_rev_ccw, weak_rev_ccw, g_ccw.
  split; intros [H | [Hcol Hmid]].
  - left.
    apply ccw_cyclicity.
    exact H.
  - right.
    split.
    + rewrite colinear_comm.
      exact Hcol.
    + rewrite at_mid_comm.
      exact Hmid.
  - left.
    apply ccw_cyclicity_2.
    exact H.
  - right.
    split.
    + rewrite colinear_comm.
      exact Hcol.
    + rewrite at_mid_comm.
      exact Hmid.
Qed.

Lemma g_rev_ccw_head_strict : forall p q r s,
  g_rev_ccw p q r ->
  g_rev_ccw p q s ->
  ccw s r q ->
  ccw r q p.
Proof.
  unfold g_rev_ccw.
  apply weak_rev_ccw_head_strict.
Qed.

Lemma Forall_g_rev_ccw_cons_iff:
  forall p q a l,
    Forall_g_rev_ccw p q (a :: l) <->
    g_rev_ccw p q a /\ Forall_g_rev_ccw p q l.
Proof.
  intros.
  unfold Forall_g_rev_ccw, g_rev_ccw.
  apply Forall_weak_rev_ccw_cons_iff.
Qed.

Lemma Forall_g_rev_ccw_nil_iff:
  forall p q,
    Forall_g_rev_ccw p q nil <-> True.
Proof.
  intros.
  unfold Forall_g_rev_ccw.
  apply Forall_weak_rev_ccw_nil_iff.
Qed.

Lemma Forall_g_rev_ccw_app:
  forall p q l1 l2,
    Forall_g_rev_ccw p q (l1 ++ l2) <->
    Forall_g_rev_ccw p q l1 /\ Forall_g_rev_ccw p q l2.
Proof.
  intros.
  unfold Forall_g_rev_ccw.
  apply Forall_weak_rev_ccw_app.
Qed.

Lemma Forall_g_rev_ccw_forall:
  forall p q l,
    Forall_g_rev_ccw p q l <->
    forall r, In r l -> g_rev_ccw p q r.
Proof.
  intros.
  unfold Forall_g_rev_ccw, g_rev_ccw.
  apply Forall_weak_rev_ccw_forall.
Qed.

Lemma Forall_g_rev_ccw_ind : forall (p q r : point) (P P' : list point),
  Forall_g_rev_ccw p q (P ++ r :: P') ->
  Forall_g_rev_ccw p q (P ++ P').
Proof.
  intros p q r P P' H.
  unfold Forall_g_rev_ccw in *.
  apply (Forall_weak_rev_ccw_ind p q r P P').
  exact H.
Qed.

Lemma Forall_g_rev_ccw_ind' : forall (p q : point) (T0 T : list point),
  Forall_g_rev_ccw p q (T0 ++ T) -> Forall_g_rev_ccw p q T.
Proof.
  intros p q T0 T H.
  unfold Forall_g_rev_ccw in *.
  apply (Forall_weak_rev_ccw_ind' p q T0 T).
  exact H.
Qed.

Lemma g_rev_ccw_list_app_iff: forall p l1 l2,
  g_rev_ccw_list p (l1 ++ l2) <->
    g_rev_ccw_list p l1 /\
    g_rev_ccw_list p l2 /\
    (forall q r, In q l1 -> In r l2 -> g_rev_ccw p q r).
Proof.
  intros.
  unfold g_rev_ccw_list, g_rev_ccw.
  apply weak_rev_ccw_list_app_iff.
Qed.

Lemma g_rev_ccw_list_remove_middle: forall p l1 l2 l3,
  g_rev_ccw_list p (l1 ++ l2 ++ l3) ->
  g_rev_ccw_list p (l1 ++ l3).
Proof.
  intros p l1 l2 l3 H.
  unfold g_rev_ccw_list in *.
  apply (weak_rev_ccw_list_remove_middle p l1 l2 l3).
  exact H.
Qed.

Fixpoint rev_consec_ccw (l: list point) : Prop :=
  match l with
  | p :: _l =>
    match _l with
    | q :: r :: _ => ccw q p r
    | _ => True
    end /\ rev_consec_ccw _l
  | _ => True
  end.

Lemma rev_consec_ccw_cons_iff: forall a l,
  rev_consec_ccw (a :: l) <->
  rev_consec_ccw l /\ (forall b c l0, l = b :: c :: l0 -> ccw b a c).
Proof.
  intros.
  split; intros.
  + destruct H.
    split; [tauto |].
    intros.
    subst l.
    tauto.
  + destruct H.
    split; [| tauto].
    destruct l as [| ? [|]]; try tauto.
    specialize (H0 _ _ _ ltac:(reflexivity)).
    tauto.
Qed.

Lemma rev_consec_ccw_snoc_iff: forall a l,
  rev_consec_ccw (l ++ a :: nil) <->
  rev_consec_ccw l /\ (forall b c l0, l = l0 ++ c :: b :: nil -> ccw a b c).
Proof.
  intros.
  destruct l as [| ? [|]].
  + simpl.
    assert (forall b c l0, [] = l0 ++ [c; b] -> ccw a b c); [| tauto].
    intros.
    destruct l0; discriminate H.
  + simpl.
    assert (forall b c l0, [p] = l0 ++ [c; b] -> ccw a b c); [| tauto].
    intros.
    destruct l0 as [| ? [|]]; discriminate H.
  + simpl app.
    revert p p0; induction l; intros.
    - simpl.
      assert (ccw p0 p a <->
              forall b c l0, [p; p0] = l0 ++ [c; b] -> ccw b c a);
      split.
      * intros.
        destruct l0 as [| ? [| ? [|]]]; [| discriminate H0 ..].
        injection H0 as ? ?.
        subst; tauto.
      * intros.
        apply (H _ _ nil).
        reflexivity.
      * intros _H; destruct _H as [_H _].
        split; [tauto|].
        intros.
        destruct l0 as [| ? [| ? [|]]]; [| discriminate H0 ..].
        injection H0 as ? ?.
        subst; apply ccw_cyclicity_2; tauto.
      * intros _H; destruct _H as [_ _H].
        split; [|tauto].
        destruct H as [_ ?].
        apply H.
        intros; specialize (_H _ _ _ H0).
        apply ccw_cyclicity; tauto.
    - simpl app.
      do 2 rewrite (rev_consec_ccw_cons_iff p).
      rewrite IHl.
      clear IHl.
      split; intros [[? ?] ?]; (split; [split |]); try tauto.
      * intros.
        injection H2 as ? ? ?; subst.
        apply (H1 _ _ (l0 ++ [a])).
        reflexivity.
      * intros.
        destruct l0; [discriminate H2 | simpl in H2].
        injection H2 as ? ?.
        subst.
        apply (H0 _ _ l0); tauto.
      * intros.
        apply (H1 _ _ (p :: l0)).
        rewrite H2; reflexivity.
      * intros.
        injection H2 as ? ? ?; subst.
        eapply H0.
        reflexivity.
Qed.

Lemma rev_consec_ccw_snoc3_iff: forall a b c l,
  rev_consec_ccw (l ++ c :: b :: a :: nil) <->
  rev_consec_ccw (l ++ c :: b :: nil) /\ ccw a b c.
Proof.
  intros.
  change (c :: b :: a :: nil) with ((c :: b :: nil) ++ (a :: nil)).
  rewrite app_assoc.
  rewrite rev_consec_ccw_snoc_iff.
  assert ((forall b0 c0 l0, l ++ [c; b] = l0 ++ [c0; b0] -> ccw a b0 c0) <->
          ccw a b c); [| split; tauto].
  split; intros.
  + eapply H; reflexivity.
  + change (c :: b :: nil) with ((c :: nil) ++ (b :: nil)) in H0.
    change (c0 :: b0 :: nil) with ((c0 :: nil) ++ (b0 :: nil)) in H0.
    rewrite !app_assoc in H0.
    rewrite !app_inj_tail_iff in H0.
    destruct H0 as [[? ?] ?]; subst.
    tauto.
Qed.

(** Shared polar-order and stack-convexity predicates used by hull algorithms. *)

Definition leftmost (p: point) (P: list point) : Prop :=
  Forall (fun (q: point) => p.(x) < q.(x) \/ (p.(x) = q.(x) /\ p.(y) <= q.(y))) P.

(* split the first point p with P *)
Definition sort (p: point) (P: list point) : Prop :=
  leftmost p P /\ g_rev_ccw_list p P.

(* split first point p with tail T *)
Fixpoint is_convex (p : point) (T : list point) : Prop :=
  match T with
  (* p3 := last point in stack *)
  | p3 :: T' =>
    match T' with
    | p2 :: p1 :: _ => ccw p1 p2 p3 /\ ccw p2 p3 p /\ is_convex p T'
    | _ => True
    end
  | _ => True
  end.

Lemma convex_ind : forall (p q : point) (T : list point),
  is_convex p (q :: T) -> is_convex p T.
Proof.
  destruct T; intros; try eauto.
  destruct T; intros; try eauto.
  destruct H as [_ [_ H]]. assumption.
Qed.

Lemma weak_rev_ccw_list_ind' : forall (p : point) (T0 T : list point),
  weak_rev_ccw_list p (T0 ++ T) -> weak_rev_ccw_list p T.
Proof.
  induction T0; intros; try assumption.
  specialize (IHT0 T). destruct H. apply (IHT0 H0).
Qed.

Lemma g_rev_ccw_list_ind' : forall (p : point) (T0 T : list point),
  g_rev_ccw_list p (T0 ++ T) -> g_rev_ccw_list p T.
Proof.
  intros p T0 T H.
  unfold g_rev_ccw_list in *.
  apply (weak_rev_ccw_list_ind' p T0 T).
  exact H.
Qed.

Lemma leftmost_ind : forall p T0 T,
  leftmost p (T0 ++ T) -> leftmost p T.
Proof.
  induction T0; intros; try assumption.
  specialize (IHT0 T).
  simpl in H. unfold leftmost in *.
  pose proof Forall_app (fun (q : point) => p.(x) < q.(x) \/ (p.(x) = q.(x) /\ p.(y) <= q.(y))) [a] (T0 ++ T).
  destruct H0 as [H0 _]. specialize (H0 H).
  destruct H0 as [_ H0]. specialize (IHT0 H0).
  tauto.
Qed.

Lemma sort_ind : forall p T0 T,
  sort p (T0 ++ T) -> sort p T.
Proof.
  induction T0; intros; try assumption.
  specialize (IHT0 T). destruct H.
  pose proof leftmost_ind p [a] (T0 ++ T) H.
  pose proof g_rev_ccw_list_ind' p [a] (T0 ++ T) H0.
  assert (sort p (T0 ++ T)). { split; tauto.  }
  tauto.
Qed.

(* Check if point p is inside or on the convex polygon CH *)

(* ===== Moved general lemmas: from Graham_Scan.v ===== *)

Lemma sort_g_rev_ccw_list : forall p T,
  sort p T ->
  g_rev_ccw_list p T.
Proof.
  intros. destruct H as [_ ?]. tauto.
Qed.
Lemma is_convex_rev_consec : forall p T,
  is_convex p T ->
  rev_consec_ccw T.
Proof.
  intros p T.
  induction T as [| a T IH]; intros Hconv; simpl in *; try tauto.
  destruct T as [| b T']; simpl in *; try tauto.
  destruct T' as [| c T'']; simpl in *; try tauto.
  destruct Hconv as [Habc [_ Htail]].
  split.
  - apply ccw_cyclicity.
    exact Habc.
  - apply IH.
    exact Htail.
Qed.

(* ===== Moved general lemmas: from Graham_Scan_M.v ===== *)

Definition first_anchor_strict (p : point) (l : list point) : Prop :=
  match l with
  | a :: b :: _ => ccw p a b
  | _ => True
  end.
Lemma g_rev_ccw_to_g_ccw_rev : forall p q r,
  g_rev_ccw p r q ->
  g_ccw p q r.
Proof.
  intros p q r H.
  rewrite g_rev_ccw_iff_g_ccw_rev in H.
  exact H.
Qed.
Lemma g_rev_ccw_list_to_g_ccw_list_rev : forall p l,
  g_rev_ccw_list p l ->
  g_ccw_list p (rev l).
Proof.
  intros p l.
  induction l as [| a l IH]; simpl; intros Hrev.
  - exact I.
  - destruct Hrev as [Ha Htail].
    rewrite g_ccw_list_app_iff.
    repeat split.
    + apply IH.
      exact Htail.
    + simpl.
      apply Forall_nil.
    + intros q r Hq Hr.
      simpl in Hr.
      destruct Hr as [Hr | []].
      subst r.
      rewrite Forall_g_rev_ccw_forall in Ha.
      apply g_rev_ccw_to_g_ccw_rev.
      apply Ha.
      rewrite in_rev.
      exact Hq.
Qed.
Lemma gs_rev_consec_ccw_rev_consec : forall l,
  rev_consec_ccw l ->
  consec_ccw (rev l).
Proof.
  intros l.
  pattern l.
  apply rev_ind.
  - simpl.
    tauto.
  - intros a l0 IH Hrev.
    rewrite rev_app_distr.
    change (rev [a]) with [a].
    change ([a] ++ rev l0) with (a :: rev l0).
    rewrite consec_ccw_cons_iff.
    rewrite rev_consec_ccw_snoc_iff in Hrev.
    destruct Hrev as [Hrev Hlast].
    split.
    + apply IH.
      exact Hrev.
    + intros b c l1 Hshape.
      apply Hlast with (l0 := rev l1).
      apply (f_equal (@rev point)) in Hshape.
      rewrite rev_involutive in Hshape.
      simpl in Hshape.
      rewrite <- app_assoc in Hshape.
      exact Hshape.
Qed.
Lemma gs_rev_consec_ccw_anchor_consec : forall p CH,
  rev_consec_ccw CH ->
  first_anchor_strict p (rev CH) ->
  consec_ccw (p :: rev CH).
Proof.
  intros p CH Hconsec Hanchor.
  rewrite consec_ccw_cons_iff.
  split.
  - apply gs_rev_consec_ccw_rev_consec.
    exact Hconsec.
  - intros b c l0 Hshape.
    destruct (rev CH) as [| a [| d l]] eqn:Hrev; try discriminate.
    inversion Hshape; subst.
    simpl in Hanchor.
    exact Hanchor.
Qed.
Lemma gs_ccw_convex_forall3_inv : forall l,
  ccw_convex l ->
  forall l1 p l2 q l3 r l4,
    l = l1 ++ p :: l2 ++ q :: l3 ++ r :: l4 ->
    ccw p q r.
Proof.
  intros l Hconv l1 p l2 q l3 r l4 Heq.
  subst l.
  pose proof (ccw_convex_app_comm l1 (p :: l2 ++ q :: l3 ++ r :: l4) Hconv)
    as Hrot.
  simpl in Hrot.
  destruct Hrot as [Hlist _].
  rewrite ccw_list_app_iff in Hlist.
  destruct Hlist as [Hprefix _].
  rewrite ccw_list_app_iff in Hprefix.
  destruct Hprefix as [_ [Htail _]].
  simpl in Htail.
  destruct Htail as [Hforall _].
  rewrite Forall_ccw_forall in Hforall.
  apply Hforall.
  rewrite in_app_iff.
  right; simpl; auto.
Qed.
Lemma gs_g_rev_ccw_not_ccw_tail : forall p a b,
  g_rev_ccw p a b ->
  ~ ccw a b p.
Proof.
  intros p a b H.
  apply g_rev_ccw_iff_weak_rev_ccw in H.
  destruct H as [Hccw | [Hcol _]].
  - apply ccw_anti_symmetry.
    exact Hccw.
  - unfold ccw, colinear, left_than, parallel, cross_prod, build_vec in *.
    simpl in *.
    nia.
Qed.
Lemma gs_leftmost_subset : forall p C L,
  leftmost p L ->
  (forall q, In q C -> In q L) ->
  leftmost p C.
Proof.
  intros p C L Hleft Hsub.
  unfold leftmost in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hleft.
  apply Hsub.
  exact Hq.
Qed.
Lemma gs_sort_cons_subset : forall p a C L,
  sort p (a :: L) ->
  sort p C ->
  (forall q, In q C -> In q L) ->
  sort p (a :: C).
Proof.
  intros p a C L Hsort_new Hsort_C Hsub.
  destruct Hsort_new as [Hleft_new [HaL _]].
  destruct Hsort_C as [Hleft_C Hweak_C].
  split.
  - unfold leftmost in *.
    rewrite Forall_cons_iff in *.
    rewrite Forall_forall in *.
    destruct Hleft_new as [Ha Hleft_L].
    split.
    + exact Ha.
    + intros q Hq.
      apply Hleft_L.
      apply Hsub.
      exact Hq.
  - split.
    + rewrite Forall_g_rev_ccw_forall in *.
      intros q Hq.
      apply HaL.
      apply Hsub.
      exact Hq.
    + exact Hweak_C.
Qed.
Lemma gs_rev_consec_ccw_tail : forall b C,
  rev_consec_ccw (b :: C) ->
  rev_consec_ccw C.
Proof.
  intros b C Hcon.
  apply rev_consec_ccw_cons_iff in Hcon.
  tauto.
Qed.
Lemma gs_first_anchor_tail : forall p b C,
  first_anchor_strict p (rev (b :: C)) ->
  first_anchor_strict p (rev C).
Proof.
  intros p b C Hanchor.
  destruct C as [| c C].
  - simpl.
    exact I.
  - destruct C as [| d C'].
    + simpl.
      exact I.
    + simpl in Hanchor |- *.
      remember (rev C') as R.
      destruct R as [| x [| y R]]; simpl in *; exact Hanchor.
Qed.
Lemma gs_sort_tail_from_cons : forall p a b C,
  sort p (a :: b :: C) ->
  sort p (a :: C).
Proof.
  intros p a b C Hsort.
  destruct Hsort as [Hleft Hweak].
  split.
  - unfold leftmost in *.
    rewrite !Forall_cons_iff in *.
    tauto.
  - pose proof (g_rev_ccw_list_remove_middle p [a] [b] C Hweak) as Hweak'.
    simpl in Hweak'.
    exact Hweak'.
Qed.
