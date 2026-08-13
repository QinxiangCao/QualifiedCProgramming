Require Import List.

Lemma fold_right_map: forall {A1 B1 A2 B2} (f1: A1 -> B1 -> B1) (f2: A2 -> B2 -> B2) gA gB,
  (forall a b, gB (f1 a b) = f2 (gA a) (gB b)) ->
  (forall l b, gB (fold_right f1 b l) = fold_right f2 (gB b) (map gA l)).
Proof.
  intros.
  induction l; auto.
  simpl.
  rewrite H.
  rewrite IHl.
  auto.
Qed.

Lemma fold_left_map: forall {A1 B1 A2 B2} (f1: A1 -> B1 -> A1) (f2: A2 -> B2 -> A2) gA gB,
  (forall a b, gA (f1 a b) = f2 (gA a) (gB b)) ->
  (forall l a, gA (fold_left f1 l a) = fold_left f2 (map gB l) (gA a)).
Proof.
  intros.
  revert a; induction l; auto; intros.
  simpl.
  rewrite <- H.
  rewrite IHl.
  auto.
Qed.

Lemma NoDup_app_iff {A}: forall l1 l2 : list A,
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ (forall a, In a l1 /\ In a l2 <-> False).
Proof.
  induction l1; intros.
  + simpl.
    split; intros.
    - split; [constructor |].
      split; auto.
      intros; tauto.
    - tauto.
  + split; intros.
    - simpl in H.
      inversion H; subst.
      rewrite IHl1 in H3; destruct H3 as [? [? ?]].
      split; [constructor | split]; auto.
      * rewrite in_app_iff in H2; tauto.
      * intros; specialize (H3 a0).
        simpl.
        split; [| tauto].
        intros [[? | ?] ?]; [| tauto].
        subst a0.
        rewrite in_app_iff in H2; tauto.
    - destruct H as [? [? ?]].
      simpl; constructor.
      * inversion H; subst.
        specialize (H1 a); simpl in H1.
        rewrite in_app_iff; tauto.
      * rewrite IHl1.
        split; [inversion H | split]; auto.
        intros; specialize (H1 a0); simpl in H1; tauto.
Qed.

        
