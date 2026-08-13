Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.

Module PTree.

  Inductive tree (A : Type) : Type :=
    | Leaf : tree A
    | Node : tree A -> option A -> tree A -> tree A.

  Arguments Leaf {A}.
  Arguments Node [A].

  Definition empty {A : Type} := (Leaf : tree A).

  Fixpoint get_rec' (A : Type) (i : positive) (m : tree A) (f : tree A -> tree A) : tree A :=
    match i with
    | xH => f m
    | xO ii => get_rec' A ii m (fun m0 : tree A => match f m0 with
                                      | Leaf => Leaf
                                      | Node l o r => l
                                      end)
    | xI ii => get_rec' A ii m (fun m0 : tree A => match f m0 with
                                      | Leaf => Leaf
                                      | Node l o r => r
                                      end)
    end.
  Definition get_rec (A : Type) (i : positive) (m : tree A) : option A :=
    match get_rec' A i m (fun m0 : tree A => m0) with
    | Leaf => None
    | Node l o r => o
    end.

  Fixpoint set_rec' (A : Type) (i : positive) (v : A) (m : tree A) (f : tree A -> tree A) : tree A :=
    match m with
    | Leaf =>
        match i with
        | xH => f (Node Leaf (Some v) Leaf)
        | xO ii => set_rec' A ii v Leaf (fun hole : tree A => f (Node hole None Leaf))
        | xI ii => set_rec' A ii v Leaf (fun hole : tree A => f (Node Leaf None hole))
        end
    | Node l o r =>
        match i with
        | xH => f (Node l (Some v) r)
        | xO ii => set_rec' A ii v l (fun hole : tree A => f (Node hole o r))
        | xI ii => set_rec' A ii v r (fun hole : tree A => f (Node l o hole))
        end
    end.
  Definition set_rec (A : Type) (i : positive) (v : A) (m : tree A) : tree A :=
    set_rec' A i v m (fun hole : tree A => hole).

  Fixpoint xelements (A : Type) (m : tree A) (k : list A) {struct m} : list A :=
  match m with
  | Leaf => k
  | Node l None r =>
    xelements A l (xelements A r k)
  | Node l (Some x) r =>
    xelements A l (x :: xelements A r k)
  end.
  Definition elements (A : Type) (m : tree A) :=
  xelements A m nil.

  Lemma get_empty : forall A p,
  get_rec A p empty = None.
Proof.
  intros.
  unfold get_rec, empty.
  set (f := fun  m0 : tree A => m0).
  assert (f Leaf = Leaf).
  subst; auto.
  clearbody f.
  revert f H.
  induction p; intros.
  - apply IHp. rewrite H. auto.
  - apply IHp. rewrite H. auto.
  - compute. rewrite H. auto.
Qed.

  Lemma elements_set_empty : forall A p x,
  elements A (set_rec A p x empty) = x :: nil.
Proof.
  intros.
  unfold set_rec.
  set (f := fun hole : tree A => hole).
  assert (forall t, elements A t = elements A (f t)).
  subst; auto.
  clearbody f.
  revert f H.
  induction p; intros.
  - apply IHp.
    intros; rewrite <- H.
    subst; auto.
  - apply IHp.
    intros; rewrite <- H.
    subst; auto.
  - unfold set_rec', empty.
    rewrite <- H.
    subst; auto.
Qed.

  Lemma get_node0 : forall A p m1 o m2,
  (get_rec A p~0 (Node m1 o m2)) = (get_rec A p m1).
Proof.
  intros.
  unfold get_rec, get_rec'; fold get_rec'.
  set (f1 := fun m0 : tree A => match m0 with
                        | Leaf => Leaf
                        | Node l _ _ => l
                        end).
  set (f2 := fun m0 : tree A => m0).
  assert (forall m1 o m2, f1 (Node m1 o m2) = f2 m1).
  subst; auto.
  clearbody f1 f2.
  revert f1 f2 H.
  induction p; intros.
  - unfold get_rec'; fold get_rec'.
    apply IHp.
    intros; rewrite H. auto.
  - unfold get_rec'; fold get_rec'.
    apply IHp.
    intros; rewrite H. auto.
  - compute. rewrite H. auto.
Qed.

  Lemma get_node1 : forall A p m1 o m2,
  (get_rec A p~1 (Node m1 o m2)) = (get_rec A p m2).
Proof.
  intros.
  unfold get_rec, get_rec'; fold get_rec'.
  set (f1 := fun m0 : tree A => match m0 with
                        | Leaf => Leaf
                        | Node _ _ r => r
                        end).
  set (f2 := fun m0 : tree A => m0).
  assert (forall m1 o m2, f1 (Node m1 o m2) = f2 m2).
  subst; auto.
  clearbody f1 f2.
  revert f1 f2 H.
  induction p; intros.
  - unfold get_rec'; fold get_rec'.
    apply IHp.
    intros; rewrite H. auto.
  -unfold get_rec'; fold get_rec'.
    apply IHp.
    intros; rewrite H. auto.
  - compute. rewrite H. auto.
Qed.

  Lemma set_node0 : forall A p x m1 o m2,
  (set_rec A p~0 x (Node m1 o m2)) = Node (set_rec A p x m1) o m2.
Proof.
  intros.
  unfold set_rec, set_rec'; fold set_rec'.
  set (f1 := fun hole : tree A => Node hole o m2) at 1.
  set (f2 := fun hole : tree A => hole).
  assert (forall t, f1 t = Node (f2 t) o m2).
  subst; auto.
  clearbody f1 f2.
  revert m1 f1 f2 H.
  induction p; intros.
  - unfold set_rec'; fold set_rec'.
    destruct m1.
    + apply IHp. intros; apply H.
    + apply IHp. intros; apply H.
  - unfold set_rec'; fold set_rec'.
    destruct m1.
    + apply IHp. intros; apply H.
    + apply IHp. intros; apply H.
  - unfold set_rec'; fold set_rec'.
    destruct m1.
    + apply H.
    + apply H.
Qed.

  Lemma set_node1 : forall A p x m1 o m2,
  (set_rec A p~1 x (Node m1 o m2)) = Node m1 o (set_rec A p x m2).
Proof.
  intros.
  unfold set_rec, set_rec'; fold set_rec'.
  set (f1 := fun hole : tree A => Node m1 o hole) at 1.
  set (f2 := fun hole : tree A => hole).
  assert (forall t, f1 t = Node m1 o (f2 t)).
  subst; auto.
  clearbody f1 f2.
  revert m2 f1 f2 H.
  induction p; intros.
  - unfold set_rec'; fold set_rec'.
    destruct m2.
    + apply IHp. intros; apply H.
    + apply IHp. intros; apply H.
  - unfold set_rec'; fold set_rec'.
    destruct m2.
    + apply IHp. intros; apply H.
    + apply IHp. intros; apply H.
  - unfold set_rec'; fold set_rec'.
    destruct m2.
    + apply H.
    + apply H.
Qed.

  Lemma xelements_append : forall A m l1 l2,
    xelements A m (l1 ++ l2) = xelements A m l1 ++ l2.
Proof.
    induction m; intros; simpl.
  - auto.
  - destruct o; rewrite IHm2; rewrite <- IHm1; auto.
  Qed.

  Lemma elements_set_none : forall A p x m,
  get_rec A p m = None ->
  exists l1 l2, elements A m = l1 ++ l2 /\
  elements A (set_rec A p x m) = l1 ++ (x :: l2).
Proof.
  intros.
  revert p H.
  induction m.
  - exists nil, nil.
    split; simpl.
    + auto.
    + apply elements_set_empty.
  - destruct p.
    + rewrite get_node1; intros.
      apply IHm2 in H; unfold elements in H.
      destruct H as [s1]; destruct H as [s2]; destruct H as [H1 H2].
      rewrite set_node1.
      destruct o; unfold elements; unfold xelements; fold xelements.
      * rewrite H1, H2.
        exists (xelements A m1 (a :: s1)), s2.
        split. apply (xelements_append A m1 (a :: s1) s2).
        apply (xelements_append A m1 (a :: s1) (x :: s2)).
      * rewrite H1, H2.
        exists (xelements A m1 s1), s2.
        split. apply (xelements_append A m1 s1 s2).
        apply (xelements_append A m1 s1 (x :: s2)).
    + rewrite get_node0; intros.
      apply IHm1 in H; unfold elements in H.
      destruct H as [s1]; destruct H as [s2]; destruct H as [H1 H2].
      rewrite set_node0.
      destruct o; unfold elements; unfold xelements; fold xelements.
      * exists s1, (s2 ++ a :: xelements A m2 nil). 
        rewrite app_comm_cons. repeat rewrite app_assoc. rewrite <- H1, <- H2.
        split.
        apply (xelements_append A m1 nil (a :: xelements A m2 nil)).
        apply (xelements_append A (set_rec A p x m1) nil (a :: xelements A m2 nil)).
      * exists s1, (s2 ++ xelements A m2 nil).
        rewrite app_comm_cons. repeat rewrite app_assoc. rewrite <- H1, <- H2.
        split.
        apply (xelements_append A m1 nil (xelements A m2 nil)).
        apply (xelements_append A (set_rec A p x m1) nil (xelements A m2 nil)).
    + unfold get_rec, get_rec', set_rec, set_rec'.
      intros. rewrite H.
      unfold elements; unfold xelements; fold xelements.
      exists (xelements A m1 nil), (xelements A m2 nil).
      split.
      apply (xelements_append A m1 nil (xelements A m2 nil)).
      apply (xelements_append A m1 nil (x :: xelements A m2 nil)).
Qed.

  Lemma elements_set_some : forall A p x x' m,
  get_rec A p m = Some x ->
  exists l1 l2, elements A m = l1 ++ (x :: l2) /\
  elements A (set_rec A p x' m) = l1 ++ (x' :: l2).
Proof.
  intros.
  revert p H.
  induction m.
  - intros.
    pose proof get_empty A p; unfold empty in H0.
    congruence.
  - destruct p.
    + rewrite get_node1; intros.
      apply IHm2 in H; unfold elements in H.
      destruct H as [s1]; destruct H as [s2]; destruct H as [H1 H2].
      rewrite set_node1.
      destruct o; unfold elements; unfold xelements; fold xelements.
      * rewrite H1, H2.
        exists (xelements A m1 (a :: s1)), s2.
        split. apply (xelements_append A m1 (a :: s1) (x :: s2)).
        apply (xelements_append A m1 (a :: s1) (x' :: s2)).
      * rewrite H1, H2.
        exists (xelements A m1 s1), s2.
        split. apply (xelements_append A m1 s1 (x :: s2)).
        apply (xelements_append A m1 s1 (x' :: s2)).
    + rewrite get_node0; intros.
      apply IHm1 in H; unfold elements in H.
      destruct H as [s1]; destruct H as [s2]; destruct H as [H1 H2].
      rewrite set_node0.
      destruct o; unfold elements; unfold xelements; fold xelements.
      * exists s1, (s2 ++ a :: xelements A m2 nil). 
        repeat rewrite app_comm_cons. repeat rewrite app_assoc.
        rewrite <- H1, <- H2.
        split.
        apply (xelements_append A m1 nil (a :: xelements A m2 nil)).
        apply (xelements_append A (set_rec A p x' m1) nil (a :: xelements A m2 nil)).
      * exists s1, (s2 ++ xelements A m2 nil).
        repeat rewrite app_comm_cons. repeat rewrite app_assoc.
        rewrite <- H1, <- H2.
        split.
        apply (xelements_append A m1 nil (xelements A m2 nil)).
        apply (xelements_append A (set_rec A p x' m1) nil (xelements A m2 nil)).
    + unfold get_rec, get_rec', set_rec, set_rec'.
      intros. rewrite H.
      unfold elements; unfold xelements; fold xelements.
      exists (xelements A m1 nil), (xelements A m2 nil).
      split.
      apply (xelements_append A m1 nil (x :: xelements A m2 nil)).
      apply (xelements_append A m1 nil (x' :: xelements A m2 nil)).
Qed.

End PTree.