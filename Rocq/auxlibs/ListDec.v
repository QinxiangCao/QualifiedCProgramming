From Coq Require Import Bool List.
Import ListNotations.
From AUXLib Require Import EqDec Decision.


(** Wrap [Lists.List.remove] using [EqDec] *)
Definition remove_eqdec {A: Type} {eqd: EqDec A eq} := @remove A equiv_dec.

(** Define a more readable version of deciding membership in a list *)
Fixpoint inb {A: Type} {eqd: EqDec A eq} (x: A) (l: list A) : bool :=
  match l with
  | nil => false
  | y :: ys => (x ==b y) || (inb x ys)
  end.

Lemma inb_true_iff {A: Type} {eqd: EqDec A eq} (x: A) (l: list A) :
  inb x l = true <-> List.In x l.
Proof.
  induction l; simpl.
  - split; [congruence|tauto].
  - split.
    + destruct (_ ==b _) eqn:H1; simpl; intros H; [left|right].
      * apply equiv_decb_true_eq in H1. auto.
      * apply IHl. auto.
    + intros H. destruct H.
      * apply eq_sym in H. apply eq_equiv_decb_true in H.
        rewrite H. reflexivity.
      * destruct (_ ==b _); simpl; auto. apply IHl. auto.
Defined.

Lemma inb_false_iff {A: Type} {eqd: EqDec A eq} (x: A) (l: list A) :
  inb x l = false <-> ~ List.In x l.
Proof.
  transitivity (~ inb x l = true).
  { generalize (inb x l). intros b. destruct b; split; auto; congruence. }
  apply not_iff_compat. apply inb_true_iff.
Qed.

Lemma inb_rev {A: Type} {eqd: EqDec A eq} (x: A) (l: list A) :
  inb x (rev l) = inb x l.
Proof.
  destruct (inb x l) eqn:Hin1, (inb x (rev l)) eqn:Hin2; simpl; auto.
  - apply inb_true_iff in Hin1. apply inb_false_iff in Hin2.
    exfalso. apply Hin2. rewrite <- in_rev. apply Hin1.
  - apply inb_false_iff in Hin1. apply inb_true_iff in Hin2.
    exfalso. apply Hin1. rewrite in_rev. apply Hin2.
Qed.

#[export] Instance In_dec {A: Type} {eqd: EqDec A eq} (x: A) (l: list A)
    : Decision (List.In x l) :=
  match inb x l as b return (inb x l = b -> _) with
  | true => fun H => left (proj1 (inb_true_iff x l) H)
  | false => fun H => right (proj1 (inb_false_iff x l) H)
  end eq_refl.


#[export] Instance incl_trans {A: Type} : Transitive (@incl A) := @incl_tran A.
#[export] Instance incl_refl {A: Type} : Reflexive (@incl A) := @incl_refl A.

Lemma incl_app_iff {A: Type} (l1 l2 l3: list A) :
  incl (l1 ++ l2) l3 <-> incl l1 l3 /\ incl l2 l3.
Proof.
  split.
  - apply incl_app_inv.
  - intros [H1 H2]. apply incl_app; auto.
Qed.

Definition inclb {A: Type} {eqd: EqDec A eq} (l1 l2: list A) : bool :=
  forallb (fun x => inb x l2) l1.

Lemma inclb_true_iff {A: Type} {eqd: EqDec A eq} (l1 l2: list A) :
  inclb l1 l2 = true <-> incl l1 l2.
Proof.
  unfold inclb, incl.
  rewrite forallb_forall.
  enough (forall x, inb x l2 = true <-> In x l2) as H.
  1: split; intros; apply H; auto.
  intros. apply inb_true_iff.
Qed.

Lemma inclb_false_iff {A: Type} {eqd: EqDec A eq} (l1 l2: list A) :
  inclb l1 l2 = false <-> ~ incl l1 l2.
Proof.
  transitivity (~ inclb l1 l2 = true).
  { generalize (inclb l1 l2). intros b. destruct b; split; auto; congruence. }
  apply not_iff_compat. apply inclb_true_iff.
Qed.

Lemma inclb_app {A: Type} {eqd: EqDec A eq} (l1 l2 l3: list A) :
  inclb (l1 ++ l2) l3 = (inclb l1 l3 && inclb l2 l3).
Proof.
  unfold inclb. rewrite forallb_app. reflexivity.
Qed.

Fixpoint diff {A: Type} {eqd: EqDec A eq} (l1 l2: list A) : list A :=
  match l1 with
  | nil => nil
  | x :: xs => if inb x l2 then diff xs l2 else x :: diff xs l2
  end.

Lemma In_diff {A: Type} {eqd: EqDec A eq} (x: A) (l1 l2: list A) :
  List.In x (diff l1 l2) <-> List.In x l1 /\ ~ List.In x l2.
Proof.
  induction l1 as [|hd l1 IH]; simpl.
  - split; intros; tauto.
  - destruct (inb hd l2) eqn:Hhd.
    + apply inb_true_iff in Hhd.
      rewrite IH. split; intros.
      * destruct H as [H1 H2]. split; auto.
      * destruct H as [H1 H2]. split; auto. destruct H1; auto. subst; tauto.
    + apply inb_false_iff in Hhd. simpl. rewrite IH. split; intros.
      * destruct H as [H | [H1 H2]]; subst; split; auto.
      * destruct H as [[H1 | H1] H2]; auto.
Qed.

Lemma diff_app_l {A: Type} {eqd: EqDec A eq} (l1 l2 k: list A) :
  diff (l1 ++ l2) k = diff l1 k ++ diff l2 k.
Proof.
  induction l1 as [|hd l1 IH]; simpl; auto.
  destruct (inb hd k); auto.
  rewrite IH. apply app_comm_cons.
Qed.

Lemma diff_app_r {A: Type} {eqd: EqDec A eq} (k l1 l2: list A) :
  diff k (l1 ++ l2) = diff (diff k l1) l2.
Proof.
  induction k as [|hd k IH]; simpl; auto.
  destruct (inb hd (l1 ++ l2)) eqn:Hhd.
  - apply inb_true_iff in Hhd.
    destruct (inb hd l1) eqn:Hhd1.
    + rewrite IH. reflexivity.
    + simpl. rewrite in_app_iff in Hhd.
      apply inb_false_iff in Hhd1.
      assert (Hhd2: inb hd l2 = true).
      { apply inb_true_iff. tauto. }
      rewrite Hhd2. rewrite IH. reflexivity.
  - apply inb_false_iff in Hhd.
    assert (Hhd1: inb hd l1 = false).
    { apply inb_false_iff. rewrite in_app_iff in Hhd. auto. }
    rewrite Hhd1. rewrite IH. simpl.
    assert (Hhd2: inb hd l2 = false).
    { apply inb_false_iff. rewrite in_app_iff in Hhd. auto. }
    rewrite Hhd2. reflexivity.
Qed.

Lemma diff_rev_l {A: Type} {eqd: EqDec A eq} (l1 l2: list A) :
  diff (rev l1) l2 = rev (diff l1 l2).
Proof.
  induction l1 as [|hd l1 IH]; simpl; auto.
  rewrite diff_app_l. rewrite IH. simpl.
  destruct (inb hd l2); auto. rewrite app_nil_r. reflexivity.
Qed.

Lemma diff_rev_r {A: Type} {eqd: EqDec A eq} (l1 l2: list A) :
  diff l1 (rev l2) = diff l1 l2.
Proof.
  induction l1; simpl; auto.
  rewrite !inb_rev. rewrite IHl1. reflexivity.
Qed.

Lemma diff_idem {A: Type} {eqd: EqDec A eq} (l1 l2: list A) :
  diff (diff l1 l2) l2 = diff l1 l2.
Proof.
  induction l1 as [|hd l1 IH]; simpl; auto.
  destruct (inb hd l2) eqn:Hhd; simpl; auto.
  rewrite Hhd, IH. reflexivity.
Qed.

Lemma diff_incl {A} {eqd: EqDec A eq} (l1 l2 l3: list A) :
  incl l1 (l2 ++ l3) ->
  incl (diff l1 l2) l3.
Proof.
  intros Hincl x Hx.
  apply In_diff in Hx as [Hx Hnotin].
  apply Hincl in Hx as Hx'.
  apply in_app_or in Hx' as [Hx' | Hx']; tauto.
Qed.

Definition disjoint {A: Type} (l1 l2: list A) : Prop :=
  forall x, In x l1 -> In x l2 -> False.

#[export] Instance disjoint_sym {A: Type} : Symmetric (@disjoint A).
Proof. unfold disjoint. intros l1 l2 H x H1 H2. eapply H; eauto. Qed.

Lemma disjoint_nil_l {A: Type} (l: list A) : disjoint [] l.
Proof. unfold disjoint. intros. tauto. Qed.
Lemma disjoint_nil_r {A: Type} (l: list A) : disjoint l [].
Proof. symmetry. apply disjoint_nil_l. Qed.

Lemma disjoint_cons_l {A: Type} (x: A) (l1 l2: list A) :
  disjoint (x :: l1) l2 <-> ~ In x l2 /\ disjoint l1 l2.
Proof.
  unfold disjoint. split.
  - intros H. split.
    + intros Hx. apply H with x; auto. left. reflexivity.
    + intros y Hin1 Hin2. apply H with y; auto. right. auto.
  - intros [Hxl2 Hdisj] y Hin_app1 Hin_app2.
    destruct Hin_app1 as [Hx | Hin1].
    + subst. apply Hxl2. auto.
    + eapply Hdisj; eauto.
Qed.

Lemma disjoint_cons_r {A: Type} (x: A) (l1 l2: list A) :
  disjoint l1 (x :: l2) <-> ~ In x l1 /\ disjoint l1 l2.
Proof.
  transitivity (disjoint (x :: l2) l1).
  1: split; symmetry; auto.
  etransitivity.
  1: apply disjoint_cons_l.
  split; intros [Hxl1 Hdisj]; split; auto; symmetry; auto.
Qed.

Lemma subset_disjoint {A: Type} (l1 l2 l1' l2': list A) :
  disjoint l1 l2 -> incl l1' l1 -> incl l2' l2 ->
  disjoint l1' l2'.
Proof.
  unfold disjoint, incl. intros Hdis Hincl1 Hincl2 x Hin1 Hin2.
  eapply Hdis; eauto.
Qed.

Lemma subset_disjoint_l {A: Type} (l1 l2 l1': list A) :
  disjoint l1 l2 -> incl l1' l1 ->
  disjoint l1' l2.
Proof. intros. eapply subset_disjoint; eauto. apply incl_refl. Qed.

Lemma subset_disjoint_r {A: Type} (l1 l2 l2': list A) :
  disjoint l1 l2 -> incl l2' l2 ->
  disjoint l1 l2'.
Proof. intros. eapply subset_disjoint; eauto. apply incl_refl. Qed.

Lemma disjoint_app_l {A: Type} (l1 l2 l3: list A) :
  disjoint (l1 ++ l2) l3 <-> disjoint l1 l3 /\ disjoint l2 l3.
Proof.
  split.
  - intros H. split.
    + eapply subset_disjoint_l; [apply H|]. apply incl_appl, incl_refl.
    + eapply subset_disjoint_l; [apply H|]. apply incl_appr, incl_refl.
  - intros [H1 H2] x Hin_app.
    apply in_app_or in Hin_app. destruct Hin_app; eauto.
Qed.

Lemma disjoint_app_r {A: Type} (l1 l2 l3: list A) :
  disjoint l1 (l2 ++ l3) <-> disjoint l1 l2 /\ disjoint l1 l3.
Proof.
  split; intros H.
  - symmetry in H. apply disjoint_app_l in H. split; symmetry; tauto.
  - symmetry. apply disjoint_app_l. split; symmetry; tauto.
Qed.

Lemma disjoint_notin_r {A: Type} (l1 l2: list A) :
  disjoint l1 l2 -> forall x, In x l1 -> ~ In x l2.
Proof. unfold disjoint, not. intros H x Hi H2. eapply H; eauto. Qed.

Lemma disjoint_notin_l {A: Type} (l1 l2: list A) :
  disjoint l1 l2 -> forall x, In x l2 -> ~ In x l1.
Proof. unfold disjoint, not. intros H x Hi H2. eapply H; eauto. Qed.

Definition disjointb {A: Type} {eqd: EqDec A eq} (l1 l2: list A) : bool :=
  forallb (fun x => negb (inb x l2)) l1.

Require Import Coq.Classes.Morphisms_Prop.

Lemma disjointb_true_iff {A: Type} {eqd: EqDec A eq} (l1 l2: list A) :
  disjointb l1 l2 = true <-> disjoint l1 l2.
Proof.
  unfold disjointb, disjoint.
  rewrite forallb_forall.
  enough (forall x, negb (inb x l2) = true <-> (In x l2 -> False)) as H.
  1: setoid_rewrite H; reflexivity.
  intros. rewrite negb_true_iff. apply inb_false_iff.
Qed.

Lemma disjointb_false_iff {A: Type} {eqd: EqDec A eq} (l1 l2: list A) :
  disjointb l1 l2 = false <-> ~ disjoint l1 l2.
Proof.
  transitivity (~ disjointb l1 l2 = true).
  { generalize (disjointb l1 l2). intros b. destruct b; split; auto; congruence. }
  apply not_iff_compat. apply disjointb_true_iff.
Qed.

#[export] Instance disjoint_dec {A: Type} {eqd: EqDec A eq} (l1 l2: list A)
    : Decision (disjoint l1 l2) :=
  match disjointb l1 l2 as b return (disjointb l1 l2 = b -> _) with
  | true => fun H => left (proj1 (disjointb_true_iff l1 l2) H)
  | false => fun H => right (proj1 (disjointb_false_iff l1 l2) H)
  end eq_refl.

Lemma disjoint_diff_id {A} {eqd: EqDec A eq} (l1 l2: list A) :
  disjoint l1 l2 -> diff l1 l2 = l1.
Proof.
  intros Hdisj.
  induction l1 as [|hd l1 IH]; simpl; auto.
  rewrite disjoint_cons_l in Hdisj.
  destruct Hdisj as [Hhd2 Hdisj].
  apply inb_false_iff in Hhd2. rewrite Hhd2.
  rewrite IH; auto.
Qed.

(** Transparent version of incl_dec *)
#[export] Instance incl_dec {A} (l1 l2 : list A) {dec : EqDec A eq} :
    Decision (incl l1 l2).
Proof.
  destruct (inclb l1 l2) eqn:H.
  - left. apply inclb_true_iff. apply H.
  - right. apply inclb_false_iff in H. apply H.
Defined.

(** Transparent version of NoDup_dec *)
#[export] Instance NoDup_dec {A} (l : list A) {dec : EqDec A eq} :
    Decision (NoDup l).
Proof.
  induction l as [|x xs IH].
  - left. constructor.
  - destruct IH as [Hndup | Hndup].
    + destruct (In_dec x xs) as [Hin | Hnin].
      * right. intros H. inversion_clear H. tauto.
      * left. constructor; auto.
    + right. intros H. inversion_clear H. tauto.
Defined.
