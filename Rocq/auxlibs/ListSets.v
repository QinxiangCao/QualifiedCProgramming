Require Import SetsClass.SetsClass. Import SetsNotation.
Local Open Scope sets.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.


Section listset.
Context {A: Type}.

Definition listset (l: list A) : A -> Prop := fun x => In x l.

Lemma listset_nil : listset (@nil A) == ∅.
Proof. sets_unfold. reflexivity. Qed.

Lemma listset_cons (x : A) (l : list A) :
  (listset (x :: l) == [x] ∪ listset l)%sets.
Proof. sets_unfold. reflexivity. Qed.

Lemma listset_app (l1 l2 : list A) :
  (listset (l1 ++ l2) == listset l1 ∪ listset l2)%sets.
Proof. sets_unfold. unfold listset. intros x. apply in_app_iff. Qed.

Lemma listset_subset (l1 l2 : list A) :
  listset l1 ⊆ listset l2 <-> incl l1 l2.
Proof. sets_unfold. reflexivity. Qed.

Definition list_setequiv (l1 l2 : list A) : Prop :=
  incl l1 l2 /\ incl l2 l1.

#[export] Instance list_setequiv_equivalence : Equivalence list_setequiv.
Proof.
  unfold list_setequiv.
  constructor.
  - intros l. split; apply incl_refl.
  - intros l1 l2 [H12 H21]. split; assumption.
  - intros l1 l2 l3 [H12 H21] [H23 H32]. split; eapply incl_tran; eauto.
Qed.
End listset.


Section general_union_intersect.
Context {T: Type} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}.

Lemma Sets_general_union_singleton :
  forall (x : T), ⨆ (Sets.singleton x : T -> Prop) == x.
Proof.
  intros x.
  sets_unfold.
  apply Sets_equiv_Sets_included. split.
  - apply Sets_general_union_included. intros y Hy. subst. reflexivity.
  - apply Sets_included_general_union. reflexivity.
Qed.

Lemma Sets_general_union_mono :
  forall (x y : T -> Prop), x ⊆ y -> ⨆ x ⊆ ⨆ y.
Proof.
  intros x y Hxy.
  apply Sets_general_union_included. intros z Hz.
  apply Sets_included_general_union.
  apply Hxy. apply Hz.
Qed.

Lemma Sets_general_union_union :
  forall (x y : T -> Prop), ⨆ (x ∪ y) == (⨆ x) ∪ (⨆ y).
Proof.
  intros x y.
  apply Sets_equiv_Sets_included. split.
  - apply Sets_general_union_included. intros z Hz.
    destruct Hz as [Hxz | Hyz].
    + transitivity (⨆ x).
      * apply Sets_included_general_union; apply Hxz.
      * apply Sets_included_union1.
    + transitivity (⨆ y).
      * apply Sets_included_general_union; apply Hyz.
      * apply Sets_included_union2.
  - apply Sets_union_included.
    + apply Sets_general_union_included. intros z Hz.
      apply Sets_included_general_union. left; apply Hz.
    + apply Sets_general_union_included. intros z Hz.
      apply Sets_included_general_union. right; apply Hz.
Qed.

Lemma Sets_general_intersect_empty :
  ⨅ ∅ == Sets.full.
Proof.
  apply Sets_equiv_Sets_included. split.
  - apply Sets_included_full.
  - apply Sets_included_general_intersect. intros x Hx. exfalso. apply Hx.
Qed.

Lemma Sets_general_intersect_singleton :
  forall (x : T), ⨅ (Sets.singleton x : T -> Prop) == x.
Proof.
  intros x.
  sets_unfold.
  apply Sets_equiv_Sets_included. split.
  - apply Sets_general_intersect_included. reflexivity.
  - apply Sets_included_general_intersect. intros y Hy. subst. reflexivity.
Qed.

Lemma Sets_general_intersect_mono :
  forall (x y : T -> Prop), x ⊆ y -> ⨅ y ⊆ ⨅ x.
Proof.
  intros x y Hxy.
  apply Sets_included_general_intersect. intros z Hz.
  apply Sets_general_intersect_included.
  apply Hxy. apply Hz.
Qed.

Lemma Sets_general_intersect_union :
  forall (x y : T -> Prop), ⨅ (x ∪ y) == (⨅ x) ∩ (⨅ y).
Proof.
  intros x y.
  apply Sets_equiv_Sets_included. split.
  - apply Sets_included_intersect.
    + apply Sets_included_general_intersect. intros z Hz.
      apply Sets_general_intersect_included. left; apply Hz.
    + apply Sets_included_general_intersect. intros z Hz.
      apply Sets_general_intersect_included. right; apply Hz.
  - apply Sets_included_general_intersect. intros z Hz.
    destruct Hz as [Hxz | Hyz].
    + transitivity (⨅ x).
      * apply Sets_intersect_included1.
      * apply Sets_general_intersect_included; apply Hxz.
    + transitivity (⨅ y).
      * apply Sets_intersect_included2.
      * apply Sets_general_intersect_included; apply Hyz.
Qed.

End general_union_intersect.


Section list_union.

Context {T: Type} {_SETS: Sets.SETS T}.

Definition list_union (l : list T) : T :=
  fold_left (fun acc x => acc ∪ x) l ∅.

Context {_SETS_Properties: SETS_Properties T}.

Lemma list_union_nil : list_union (@nil T) == ∅.
Proof. reflexivity. Qed.

Lemma list_union_app (l1 l2 : list T) :
  list_union (l1 ++ l2) == list_union l1 ∪ list_union l2.
Proof.
  rewrite <- (rev_involutive l2).
  generalize (rev l2) as l2'. clear l2.
  revert l1.
  induction l2'.
  - intros. simpl.
    rewrite app_nil_r. rewrite list_union_nil.
    rewrite Sets_union_empty_r. reflexivity.
  - revert IHl2'. simpl. unfold list_union. rewrite !fold_left_app. simpl.
    intros. rewrite IHl2'.
    rewrite Sets_union_assoc. reflexivity.
Qed.

Lemma list_union_singleton (x : T) :
  list_union (x :: nil) == x.
Proof.
  unfold list_union. simpl.
  rewrite Sets_union_empty_l.
  reflexivity.
Qed.

Lemma list_union_cons (x : T) (l : list T) :
  list_union (x :: l) == x ∪ list_union l.
Proof.
  change (x :: l) with (app (x :: nil) l).
  rewrite list_union_app, list_union_singleton. reflexivity.
Qed.

Lemma list_union_listset (t : list T) : list_union t == ⨆ (listset t).
Proof.
  induction t as [|h t' IH].
  - rewrite listset_nil, list_union_nil.
    rewrite Sets_empty_general_union. reflexivity.
  - rewrite listset_cons, list_union_cons.
    rewrite IH.
    rewrite Sets_general_union_union. rewrite Sets_general_union_singleton.
    reflexivity.
Qed.

Lemma list_union_map_mono {A} (f g: A -> T) (l: list A) :
  Forall (fun x => f x ⊆ g x) l ->
  list_union (map f l) ⊆ list_union (map g l).
Proof.
  induction l; intros H.
  - simpl. sets_unfold. reflexivity.
  - simpl. rewrite !list_union_cons.
    apply Sets_union_mono.
    + apply Forall_inv in H. apply H.
    + apply IHl. apply Forall_inv_tail in H. apply H.
Qed.

End list_union.


Section list_intersect.

Context {T: Type} {_SETS: Sets.SETS T}.

Definition list_intersect (l : list T) : T :=
  fold_left (fun acc x => acc ∩ x) l (Sets.full).

Context {_SETS_Properties: SETS_Properties T}.

Lemma list_intersect_nil : list_intersect (@nil T) == Sets.full.
Proof. reflexivity. Qed.

Lemma list_intersect_app (l1 l2 : list T) :
  list_intersect (l1 ++ l2) == list_intersect l1 ∩ list_intersect l2.
Proof.
  rewrite <- (rev_involutive l2).
  generalize (rev l2) as l2'. clear l2.
  revert l1.
  induction l2'.
  - intros. simpl.
    rewrite app_nil_r. rewrite list_intersect_nil.
    rewrite Sets_intersect_full_r. reflexivity.
  - revert IHl2'. simpl. unfold list_intersect. rewrite !fold_left_app. simpl.
    intros. rewrite IHl2'.
    rewrite Sets_intersect_assoc. reflexivity.
Qed.

Lemma list_intersect_singleton (x : T) :
  list_intersect (x :: nil) == x.
Proof.
  unfold list_intersect. simpl.
  rewrite Sets_intersect_full_l.
  reflexivity.
Qed.

Lemma list_intersect_cons (x : T) (l : list T) :
  list_intersect (x :: l) == x ∩ list_intersect l.
Proof.
  change (x :: l) with (app (x :: nil) l).
  rewrite list_intersect_app, list_intersect_singleton. reflexivity.
Qed.

Lemma list_intersect_listset (t : list T) : list_intersect t == ⨅ (listset t).
Proof.
  induction t as [|h t' IH].
  - rewrite listset_nil, list_intersect_nil.
    rewrite Sets_general_intersect_empty. reflexivity.
  - rewrite listset_cons, list_intersect_cons.
    rewrite IH.
    rewrite Sets_general_intersect_union. rewrite Sets_general_intersect_singleton.
    reflexivity.
Qed.

End list_intersect.
