Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Export ListLib.Base.Inductive.
Require Export ListLib.Base.Positional.
Require Export ListLib.General.Length.
Require Export ListLib.General.Forall.
From AUXLib Require Import int_auto Axioms Feq Idents VMap EqDec.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.Common Require Import Notations.
Import ListNotations.
Local Open Scope sets.
Local Open Scope list.
Local Open Scope nat_scope.
Local Open Scope option_monad_scope.

(** Wrap [Lists.List.remove] using [EqDec] *)
Definition remove_eqdec {A: Type} {eqd: EqDec A eq} := @remove A equiv_dec.

(** Define a more readable version of deciding membership in a list *)
Fixpoint inb {A: Type} {eqd: EqDec A eq} (x: A) (l: list A) : bool :=
  match l with
  | nil => false
  | y :: ys => (x ==b y) || inb x ys
  end.

Lemma inb_true_iff {A: Type} {eqd: EqDec A eq} (x: A) (l: list A) :
  inb x l = true <-> List.In x l.
Proof.
  induction l; simpl.
  - split; [congruence | tauto].
  - split.
    + destruct (_ ==b _) eqn:H1; simpl; intros H; [left | right].
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

Definition In_dec {A: Type} {eqd: EqDec A eq} (x: A) (l: list A)
    : {List.In x l} + {~ List.In x l} :=
  match inb x l as b return (inb x l = b -> _) with
  | true => fun H => left (proj1 (inb_true_iff x l) H)
  | false => fun H => right (proj1 (inb_false_iff x l) H)
  end eq_refl.

Definition incl_dec {A} (l1 l2 : list A) {dec : EqDec A eq} :
    {incl l1 l2} + {~ incl l1 l2}.
Proof.
  destruct (forallb (fun x => inb x l2) l1) eqn:H.
  - left. intros x Hx. rewrite forallb_forall in H.
    specialize (H x Hx). apply inb_true_iff in H. apply H.
  - right. intros Hincl. eapply eq_true_false_abs. 2: apply H.
    apply forallb_forall. intros x Hx. specialize (Hincl x Hx).
    apply inb_true_iff. apply Hincl.
Defined.

Definition NoDup_dec {A} (l : list A) {dec : EqDec A eq} :
    {NoDup l} + {~ NoDup l}.
Proof.
  induction l as [|x xs IH].
  - left. constructor.
  - destruct IH as [Hndup | Hndup].
    + destruct (In_dec x xs) as [Hin | Hnin].
      * right. intros H. inversion_clear H. tauto.
      * left. constructor; auto.
    + right. intros H. inversion_clear H. tauto.
Defined.

Lemma Forall2_split_app1 : forall (A B : Type)
  (P : A -> B -> Prop) xs1 xs2 ys,
  Forall2 P (xs1 ++ xs2) ys ->
  exists ys1 ys2,
  ys = ys1 ++ ys2 /\ Forall2 P xs1 ys1 /\ Forall2 P xs2 ys2.
Proof.
  intros.
  apply Forall2_app_inv_l in H.
  destruct H as (ys1 & ys2 & Heq & ? & ?).
  subst ys.
  eauto.
Qed.

Lemma Forall2_split_app2 : forall (A B : Type)
  (P : A -> B -> Prop) xs ys1 ys2,
  Forall2 P xs (ys1 ++ ys2) ->
  exists xs1 xs2,
  xs = xs1 ++ xs2 /\ Forall2 P xs1 ys1 /\ Forall2 P xs2 ys2.
Proof.
  intros.
  apply Forall2_app_inv_r in H.
  destruct H as (xs1 & xs2 & Heq & ? & ?).
  subst xs.
  eauto.
Qed.

Lemma Forall2_merge : forall (A B : Type) (P : A -> B -> Prop) xs1 ys1 xs2 ys2,
  Forall2 P xs1 ys1 ->
  Forall2 P xs2 ys2 ->
  Forall2 P (xs1 ++ xs2) (ys1 ++ ys2).
Proof.
  intros.
  apply Forall2_app; auto.
Qed.

Lemma list_split_nth : forall (A : Type) (n : nat) (l : list A) (d : A),
  (n < length l)%nat ->
  l = firstn n l ++ nth n l d :: skipn (S n) l.
Proof.
  intros.
  apply (firstn_skipSn d); auto.
Qed.

Arguments list_split_nth _ n%_nat.

Lemma cons_length : forall (A : Type) (x : A) (l : list A),
  length (x :: l) = S (length l).
Proof.
  intros. simpl. auto.
Qed.

Lemma combine_app : forall {A B : Type} (l1 l2 : list A) (l1' l2' : list B),
  length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1; destruct l1'; simpl; intros; auto; try lia.
  f_equal. auto.
Qed.

Lemma forall_in_cons:
  forall {A: Type} (a: A) (l: list A) (P: A -> Prop),
    (forall a0, In a0 (a :: l) -> P a0) <->
    P a /\ (forall a0, In a0 l -> P a0).
Proof.
  intros; split; intros.
  + split.
    - exact (H _ (or_introl eq_refl)).
    - intros.
      exact (H _ (or_intror H0)).
  + destruct H0.
    - subst; tauto.
    - revert a0 H0; tauto.
Qed.

Lemma forall_in_app:
  forall {A: Type} (l1 l2: list A) (P: A -> Prop),
    (forall a, In a (l1 ++ l2) -> P a) <->
    (forall a, In a l1 -> P a) /\
    (forall a, In a l2 -> P a).
Proof.
  intros.
  induction l1; simpl app.
  + assert (forall a, False -> P a) by tauto.
    tauto.
  + rewrite !forall_in_cons.
    tauto.
Qed.

Definition prod_eq_dec {A B}
  (eq_dec1: forall a1 a2: A, {a1 = a2} + {a1 <> a2})
  (eq_dec2: forall b1 b2: B, {b1 = b2} + {b1 <> b2}):
  forall p1 p2: A * B, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [a1 b1] [a2 b2].
  destruct (eq_dec1 a1 a2), (eq_dec2 b1 b2).
  - left; congruence.
  - right; congruence.
  - right; congruence.
  - right; congruence.
Defined.

Definition list_eq_dec {A: Type} (eq_dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2}):
  forall l1 l2: list A, {l1 = l2} + {l1 <> l2}.
Proof.
  intros l1.
  induction l1; destruct l2; simpl.
  + left; auto.
  + right; congruence.
  + right; congruence.
  + destruct (eq_dec a a0), (IHl1 l2).
    - left; congruence.
    - right; congruence.
    - right; congruence.
    - right; congruence.
Defined.

Definition list_eqb {A B: Type} (eqb: A -> B -> bool) (l1 : list A) (l2 : list B): bool :=
  (fix list_eqb (l1 : list A) (l2 : list B): bool :=
    match l1, l2 with
    | nil, nil => true
    | cons a1 l1', cons a2 l2' => eqb a1 a2 && list_eqb l1' l2'
    | _, _ => false
    end) l1 l2.

Lemma list_eqb_eq_nil: forall {A B} (eqb: A -> B -> bool),
  forall l2: list B, list_eqb eqb nil l2 = true <-> nil = l2.
Proof.
  intros.
  destruct l2; simpl.
  + tauto.
  + split; intros; congruence.
Qed.

Lemma list_eqb_eq_cons: forall {A} eqb,
  forall a1 l1,
    (forall a2: A, eqb a1 a2 = true <-> a1 = a2) ->
    (forall l2: list A, list_eqb eqb l1 l2 = true <-> l1 = l2) ->
    forall l2, list_eqb eqb (cons a1 l1) l2 = true <-> cons a1 l1 = l2.
Proof.
  intros.
  destruct l2; simpl.
  + split; intros; congruence.
  + rewrite andb_true_iff, H, H0.
    split; [intros [? ?] | intros; split]; congruence.
Qed.

Lemma list_eqb_eq {A} eqb (eqb_eq : forall a1 a2: A, eqb a1 a2 = true <-> a1 = a2):
    forall l1 l2: list A, list_eqb eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros.
  revert l2.
  induction l1.
  + apply list_eqb_eq_nil.
  + apply list_eqb_eq_cons; auto.
Qed.

Lemma list_eqb_refl {A} eqb (eqb_refl : forall a: A, eqb a a = true):
  forall (l: list A), list_eqb eqb l l = true.
Proof.
  intros.
  induction l; simpl; auto.
  rewrite (eqb_refl a), IHl. auto.
Qed.

Lemma list_eqb_true {A} eqb (eqb_true : forall a1 a2: A, eqb a1 a2 = true -> a1 = a2):
  forall (l1 l2 : list A), list_eqb eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1; destruct l2; intros.
  - reflexivity.
  - simpl in H; discriminate H.
  - simpl in H; discriminate H.
  - simpl in H.
    apply andb_true_iff in H as [? ?].
    apply eqb_true in H; subst.
    f_equal; auto.
Qed.

Definition option_eqb {A: Type} (eqb: A -> A -> bool) (o1 o2: option A): bool :=
  match o1, o2 with
  | Some a1, Some a2 => eqb a1 a2
  | None, None => true
  | _, _ => false
  end.

Lemma option_eqb_eq:
  forall A eqb,
    (forall a1 a2: A, eqb a1 a2 = true <-> a1 = a2) ->
    forall o1 o2: option A, option_eqb eqb o1 o2 = true <-> o1 = o2.
Proof.
  intros.
  destruct o1, o2; simpl.
  + rewrite H.
    split; intros; congruence.
  + split; intros; congruence.
  + split; intros; congruence.
  + tauto.
Qed.

Definition lift_option {A: Type} (l: list (option A)) : option (list A) :=
  fold_right (fun x acc => do y <- x; do ys <- acc; Some (y :: ys)) (Some nil) l.

Lemma lift_option_map_some {A: Type} (l: list A):
  lift_option (map (fun x => Some x) l) = Some l.
Proof.
  induction l.
  + reflexivity.
  + simpl. rewrite IHl. reflexivity.
Qed.

Lemma lift_option_cons {A: Type} (x: option A) (l: list (option A)) :
  lift_option (x :: l) = do y <- x; do ys <- lift_option l; Some (y :: ys).
Proof.
  reflexivity.
Qed.

Lemma lift_option_app {A: Type} (l1 l2: list (option A)):
  lift_option (l1 ++ l2) = do l1' <- lift_option l1; do l2' <- lift_option l2; Some (l1' ++ l2').
Proof.
  induction l1 as [|hd l1']; simpl.
  - destruct (lift_option l2); reflexivity.
  - rewrite IHl1'.
    destruct hd; [| reflexivity].
    destruct (lift_option l1'); [| reflexivity].
    destruct (lift_option l2); reflexivity.
Qed.

Definition list_prod_split {A B: Type} (l: list (A * B)) : (list A) * (list B) :=
  (map (fun x => fst x) l, map (fun x => snd x) l).

Fixpoint list_prod_merge {A B: Type} (l1: list A) (l2: list B) : option (list (A * B)) :=
  match l1, l2 with
  | nil, nil => Some nil
  | a :: l1', b :: l2' =>
      do l' <- list_prod_merge l1' l2';
      Some ((a, b) :: l')
  | _, _ => None
  end.

Lemma incl_cons_iff : forall {A: Type} (a: A) (l m: list A),
  incl (a :: l) m <-> In a m /\ incl l m.
Proof.
  intros. split; [apply incl_cons_inv | intros [? ?]; apply incl_cons; auto].
Qed.

Definition nperm (s : list nat) : Prop := Permutation (seq O (length s)) s.

Definition do_nperm {A : Type} (s : list nat) (l : list A) (d : A) : list A :=
  map (fun n => nth n l d) s.

Definition trivial_nperm (n : nat) := seq O n.

Lemma trivial_nperm_nperm : forall n, nperm (trivial_nperm n).
Proof.
  intros. unfold nperm, trivial_nperm.
  rewrite length_seq.
  apply Permutation_refl.
Qed.

Lemma trivial_nperm_refl : forall (A : Type) (n : nat) (l : list A) (d : A),
  length l = n ->
  do_nperm (trivial_nperm n) l d = l.
Proof.
  unfold do_nperm. induction n; simpl; intros.
  - destruct l; auto. simpl in H. lia.
  - destruct l; simpl in *; try lia.
    inversion H. subst. f_equal.
    rewrite <- seq_shift. rewrite map_map. auto.
Qed.

Fixpoint find_index (l : list nat) (n : nat) : nat :=
  match l with
  | nil => O
  | n' :: l' =>
    if Nat.eqb n' n
    then O
    else S (find_index l' n)
  end.

Lemma find_index_nth : forall l n d,
  NoDup l ->
  (n < length l)%nat ->
  find_index l (nth n l d) = n.
Proof.
  intros. generalize dependent l.
  induction n; intros; destruct l; simpl in *; auto; try lia.
  - rewrite Nat.eqb_refl. auto.
  - inversion H. subst.
    assert ((n < length l)%nat) by lia.
    rewrite (IHn _ H4 H1).
    destruct (Nat.eqb n0 (nth n l d)) eqn:E; auto.
    rewrite Nat.eqb_eq in E. subst.
    contradict H3.
    apply nth_In with (d := d) in H1.
    exact H1.
Qed.

Lemma nth_find_index : forall l n d,
  In n l ->
  nth (find_index l n) l d = n.
Proof.
  intros. generalize dependent n.
  induction l; intros; simpl in *.
  - contradiction.
  - destruct (Nat.eqb a n) eqn:E.
    + rewrite Nat.eqb_eq in E. auto.
    + rewrite Nat.eqb_neq in E. destruct H; try congruence.
      apply IHl. auto.
Qed.

Lemma map_nth_len : forall (A B : Type) (f : A -> B) l n dx dy,
  (n < length l)%nat ->
  nth n (map f l) dx = f (nth n l dy).
Proof.
  intros. generalize dependent l.
  induction n; intros.
  - destruct l; simpl in *; auto. lia.
  - destruct l; simpl in *; try lia.
    apply IHn. lia.
Qed.

Lemma map_find_index_same : forall l,
  NoDup l ->
  map (find_index l) l = seq O (length l).
Proof.
  intros. apply (nth_ext _ _ O O).
  - rewrite length_map. rewrite length_seq. auto.
  - intros. rewrite length_map in H0.
    rewrite seq_nth; auto. simpl.
    rewrite (map_nth_len _ _ _ _ _ _ O); auto.
    rewrite find_index_nth; auto.
Qed.

Lemma do_nperm_length : forall (A : Type) s (l : list A) d,
  length (do_nperm s l d) = length s.
Proof.
  intros. unfold do_nperm. rewrite length_map. auto.
Qed.

Lemma nperm_range : forall s n0 d,
  nperm s ->
  (n0 < length s)%nat ->
  (nth n0 s d < length s)%nat.
Proof.
  intros.
  pose proof (nth_In s d H0).
  unfold nperm in H. symmetry in H.
  apply (Permutation_in _ H) in H1.
  apply in_seq in H1. simpl in *. lia.
Qed.

Lemma nperm_NoDup : forall s,
  nperm s -> NoDup s.
Proof.
  intros.
  apply (Permutation_NoDup H).
  apply seq_NoDup.
Qed.

Lemma nperm_map : forall (A B : Type) s (f : A -> B) (l : list A) dx,
  do_nperm s (map f l) (f dx) = map f (do_nperm s l dx).
Proof.
  intros. unfold do_nperm. rewrite map_map.
  apply map_ext. intros. apply map_nth.
Qed.

Lemma find_index_range : forall l n,
  In n l ->
  (find_index l n < length l)%nat.
Proof.
  intros. induction l; simpl in *.
  - contradiction.
  - destruct (Nat.eqb a n) eqn:E.
    + lia.
    + rewrite Nat.eqb_neq in E. destruct H; try congruence.
      specialize (IHl H). lia.
Qed.

Definition inverse_nperm (s : list nat) :=
  map (find_index s) (seq O (length s)).

Lemma inverse_nperm_nperm : forall s,
  nperm s ->
  nperm (inverse_nperm s).
Proof.
  intros. unfold inverse_nperm, nperm.
  pose proof (Permutation_map (find_index s) H).
  rewrite map_find_index_same in H0.
  - symmetry. rewrite length_map. rewrite length_seq. auto.
  - apply nperm_NoDup. auto.
Qed.

Definition inverse_nperm_compose_refl1 : forall (A : Type)
  (s : list nat) (l : list A) d,
  nperm s ->
  length l = length s ->
  do_nperm s (do_nperm (inverse_nperm s) l d) d = l.
Proof.
  intros. unfold do_nperm, inverse_nperm; simpl.
  apply (nth_ext _ _ d d).
  { rewrite length_map. auto. }
  intros. rewrite length_map in H1.
  rewrite <- H0 in H1. rewrite map_map.
  rewrite (map_nth_len _ _ _ _ n _ O) by lia.
  rewrite (map_nth_len _ _ _ _ _ _ O).
  2:{ rewrite length_seq. apply nperm_range; auto. lia. }
  rewrite seq_nth.
  2:{ apply nperm_range; auto. lia. }
  simpl. rewrite find_index_nth; auto.
  { apply nperm_NoDup. auto. }
  { lia. }
Qed.

Definition inverse_nperm_compose_refl2 : forall (A : Type)
  (s : list nat) (l : list A) d,
  nperm s ->
  length l = length s ->
  do_nperm (inverse_nperm s) (do_nperm s l d) d = l.
Proof.
  intros. unfold do_nperm, inverse_nperm; simpl.
  apply (nth_ext _ _ d d).
  { rewrite !length_map. rewrite length_seq. auto. }
  intros. rewrite length_map in H1. rewrite length_map in H1.
  rewrite length_seq in H1.
  rewrite (map_nth_len _ _ _ _ n _ O).
  2:{ rewrite length_map. rewrite length_seq. lia. }
  rewrite (map_nth_len _ _ _ _ n _ O).
  2:{ rewrite length_seq. lia. }
  rewrite (map_nth_len _ _ _ _ _ _ O).
  2:{ rewrite seq_nth; auto. simpl.
      apply find_index_range.
      apply (Permutation_in _ H). apply in_seq. lia. }
  rewrite seq_nth by lia. simpl.
  rewrite nth_find_index; auto.
  { apply (Permutation_in _ H). apply in_seq. lia. }
Qed.

Lemma do_nperm_permutation :
  forall (A : Type) (s : list nat) (l : list A) (d : A),
  nperm s ->
  length l = length s ->
  Permutation l (do_nperm s l d).
Proof.
  intros. rewrite <- (trivial_nperm_refl _ (length l) l d) at 1; auto.
  unfold do_nperm. apply Permutation_map. rewrite H0. apply H.
Qed.

Lemma Forall2_nperm_congr0 : forall (A B : Type)
  (P : A -> B -> Prop) xs ys (s : list nat) dx dy,
  nperm s ->
  length xs = length s ->
  Forall2 P xs ys ->
  Forall2 P (do_nperm s xs dx) (do_nperm s ys dy).
Proof.
  intros * HPerm **.
  apply (Forall2_nth_iff _ _ _ _ _ dx dy) in H0.
  apply (Forall2_nth_iff _ _ _ _ _ dx dy).
  destruct H0. split.
  - rewrite !do_nperm_length; auto.
  - intros. unfold do_nperm.
    rewrite do_nperm_length in H2; auto.
    rewrite (map_nth_len _ _ _ _ _ dx O) by lia.
    rewrite (map_nth_len _ _ _ _ _ dy O) by lia.
    apply H1; auto.
    pose proof (nperm_range s _ O HPerm H2). lia.
Qed.

Lemma Forall2_nperm_congr : forall (A B : Type)
  (P : A -> B -> Prop) xs ys (s : list nat) dx dy,
  nperm s ->
  length xs = length s ->
  length ys = length s ->
  Forall2 P xs ys <->
  Forall2 P (do_nperm s xs dx) (do_nperm s ys dy).
Proof.
  intros * HPerm **. split; intros.
  - apply Forall2_nperm_congr0; auto.
  - rewrite <- (inverse_nperm_compose_refl2 _ s xs dx HPerm H).
    rewrite <- (inverse_nperm_compose_refl2 _ s ys dy HPerm H0).
    apply Forall2_nperm_congr0; auto.
    + apply inverse_nperm_nperm. auto.
    + rewrite do_nperm_length. unfold inverse_nperm. rewrite length_map.
      rewrite length_seq. auto.
Qed.

Definition swap_nperm (n1 n2 n3 : nat) :=
  seq 0 n1 ++ 1 + n1 + n2 :: seq (1 + n1) n2 ++ n1 :: seq (2 + n1 + n2) n3.

Definition swap_nperm_nperm : forall (n1 n2 n3 : nat), nperm (swap_nperm n1 n2 n3).
Proof.
  intros. unfold nperm, swap_nperm.
  rewrite !length_app. rewrite length_seq. simpl.
  replace (2 + n1 + n2 + n3) with (n1 + (1 + n2 + (1 + n3))) by lia.
  rewrite (seq_app n1). apply Permutation_app; [apply Permutation_refl |].
  simpl. rewrite length_app. simpl. rewrite !length_seq.
  rewrite (seq_app n2). simpl.
  rewrite !(Permutation_app_comm (seq (S n1) n2)).
  simpl. apply perm_swap.
Qed.

Lemma swap_nperm_do_nperm : forall (A : Type) l1 i l2 j l3 (d : A),
  do_nperm (swap_nperm (length l1) (length l2) (length l3))
    (l1 ++ i :: l2 ++ j :: l3) d =
    (l1 ++ j :: l2 ++ i :: l3).
Proof.
  intros. unfold do_nperm, swap_nperm; simpl.
  rewrite map_app. simpl. rewrite map_app. simpl.
  f_equal.
  { apply (nth_ext _ _ d d).
    - rewrite length_map. rewrite length_seq. auto.
    - intros.
      rewrite length_map in H. rewrite length_seq in H.
      rewrite (map_nth_len _ _ _ _ _ d O); auto.
      + rewrite seq_nth; auto. simpl. apply app_nth1. auto.
      + rewrite length_seq. auto. }
  f_equal.
  { rewrite app_nth2; try lia.
    replace (S (length l1 + length l2) - length l1) with (S (length l2)) by lia.
    simpl. rewrite app_nth2; try lia.
    replace (length l2 - length l2) with 0 by lia. simpl. auto. }
  f_equal.
  { apply (nth_ext _ _ d d).
    - rewrite length_map. rewrite length_seq. auto.
    - intros.
      rewrite length_map in H. rewrite length_seq in H.
      rewrite (map_nth_len _ _ _ _ _ d O); auto.
      + rewrite seq_nth; auto. simpl. rewrite app_nth2; try lia.
        replace (S (length l1 + n) - length l1) with (S n) by lia.
        simpl. apply app_nth1. auto.
      + rewrite length_seq. auto. }
  f_equal.
  { rewrite app_nth2; try lia.
    replace (length l1 - length l1) with 0 by lia. simpl. auto. }
  { apply (nth_ext _ _ d d).
    - rewrite length_map. rewrite length_seq. auto.
    - intros.
      rewrite length_map in H. rewrite length_seq in H.
      rewrite (map_nth_len _ _ _ _ _ d O); auto.
      + rewrite seq_nth; auto. simpl. rewrite app_nth2; try lia.
        replace (S (S (length l1 + length l2 + n)) - length l1) with (2 + length l2 + n) by lia.
        simpl. rewrite app_nth2; try lia.
        replace (S (length l2 + n) - length l2) with (S n) by lia.
        simpl. auto.
      + rewrite length_seq. auto. }
Qed.

Definition list_swap_nperm (n1 n2 : nat) :=
  seq n1 n2 ++ seq 0 n1.

Definition list_swap_nperm_nperm : forall (n1 n2 : nat),
  nperm (list_swap_nperm n1 n2).
Proof.
  intros. unfold nperm, list_swap_nperm.
  rewrite length_app. rewrite !length_seq.
  replace (n2 + n1) with (n1 + n2) by lia.
  rewrite seq_app. simpl. apply Permutation_app_comm.
Defined.

Lemma list_swap_nperm_do_nperm : forall (A : Type) l1 l2 (d : A),
  do_nperm (list_swap_nperm (length l1) (length l2))
    (l1 ++ l2) d = l2 ++ l1.
Proof.
  intros. unfold do_nperm, list_swap_nperm; simpl.
  rewrite map_app. simpl. f_equal.
  - apply (nth_ext _ _ d d).
    { rewrite length_map. rewrite length_seq. auto. }
    intros. rewrite length_map in H. rewrite length_seq in H.
    rewrite (map_nth_len _ _ _ _ _ d 0).
    2:{ rewrite length_seq. lia. }
    rewrite seq_nth; auto. rewrite app_nth2; try lia.
    replace (length l1 + n - length l1) with n by lia.
    auto.
  - apply (nth_ext _ _ d d).
    { rewrite length_map. rewrite length_seq. auto. }
    intros. rewrite length_map in H. rewrite length_seq in H.
    rewrite (map_nth_len _ _ _ _ _ d 0).
    2:{ rewrite length_seq. lia. }
    rewrite seq_nth; auto. simpl. rewrite app_nth1; try lia.
    auto.
Qed.

Lemma NoDup_map_fst : forall (A B : Type) (l : list (A * B)) x y y',
  NoDup (map fst l) ->
  In (x, y) l ->
  In (x, y') l ->
  y = y'.
Proof.
  intros. induction l; simpl in *.
  - contradiction.
  - inversion H. subst. clear H.
    destruct H0; destruct H1; subst.
    + congruence.
    + apply (in_map fst) in H0. simpl in H0. contradiction.
    + apply (in_map fst) in H. simpl in H. contradiction.
    + auto.
Qed.

Local Open Scope Z_scope.

Fixpoint Zseq (start : Z) (len : nat) : list Z :=
  match len with
  | O => nil
  | S len' => start :: Zseq (Z.succ start) len'
  end.

Lemma Zseq_length : forall s n,
  length (Zseq s n) = n.
Proof.
  intros. revert s. induction n; intros; simpl; auto.
Qed.

Lemma Zseq_app : forall start len1 len2,
  Zseq start (len1 + len2) = Zseq start len1 ++ Zseq (start + Z.of_nat len1) len2.
Proof.
  intros start len1. revert start.
  induction len1; intros; simpl in *.
  - f_equal. lia.
  - rewrite IHlen1. f_equal. f_equal. f_equal. lia.
Qed.

Local Close Scope Z_scope.

Fixpoint nat_list_insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if Nat.leb i h then i :: h :: t else h :: nat_list_insert i t
  end.

Fixpoint nat_sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => nat_list_insert h (nat_sort t)
  end.

Lemma nat_list_insert_perm : forall x l,
    Permutation (x :: l) (nat_list_insert x l).
Proof.
  intros x l. induction l.
  - auto.
  - simpl. destruct (Nat.leb x a) eqn:?.
    + apply Permutation_refl.
    + apply perm_trans with (a :: x :: l).
      * apply perm_swap.
      * apply perm_skip. assumption.
Qed.

Lemma nat_sort_perm : forall l, Permutation l (nat_sort l).
Proof.
  intros l. induction l.
  - auto.
  - simpl. apply perm_trans with (a :: nat_sort l).
    + apply perm_skip. assumption.
    + apply nat_list_insert_perm.
Qed.

Lemma nat_sort_nperm : forall s,
  nat_sort s = seq O (length s) ->
  nperm s.
Proof.
  intros. unfold nperm.
  rewrite <- H. symmetry. apply nat_sort_perm.
Qed.

Definition list_update_nth {A : Type} (l : list A) (n : nat) (v : A) :=
  firstn n l ++ v :: skipn (S n) l.

Lemma list_eq_nth : forall (A : Type) (l1 l2 : list A) (d : A),
  length l1 = length l2 ->
  (forall n, (n < length l1)%nat -> nth n l1 d = nth n l2 d) ->
  l1 = l2.
Proof.
  induction l1; intros; destruct l2; simpl in *; auto; try lia.
  f_equal.
  - apply (H0 O). lia.
  - apply (IHl1 _ d).
    + lia.
    + intros. apply (H0 (S n)). lia.
Qed.

Lemma Zseq_nth : forall start len n,
  (n < len)%nat ->
  nth n (Zseq start len) 0%Z = (start + Z.of_nat n)%Z.
Proof.
  intros. generalize dependent len. revert start.
  induction n; intros.
  - simpl. destruct len; [lia |]. simpl. lia.
  - destruct len; [lia |]. simpl. rewrite IHn; lia.
Qed.

Lemma combine_skipn : forall (A B : Type) (l : list A) (l' : list B) n,
  skipn n (combine l l') = combine (skipn n l) (skipn n l').
Proof.
  intros *. revert l l'. induction n; intros; simpl.
  - auto.
  - destruct l; destruct l'; simpl in *; auto.
    rewrite combine_nil. auto.
Qed.

Lemma Zseq_firstn : forall start len n,
  (n <= len)%nat ->
  firstn n (Zseq start len) = Zseq start n.
Proof.
  intros. generalize dependent len. revert start.
  induction n; intros; simpl; auto.
  destruct len; [lia |].
  simpl. rewrite IHn; auto. lia.
Qed.

Lemma Zseq_skipn : forall start len n,
  skipn n (Zseq start len) = Zseq (start + Z.of_nat n) (len - n).
Proof.
  intros. generalize dependent len. revert start.
  induction n; intros; simpl.
  - f_equal; lia.
  - destruct len; simpl; auto.
    rewrite IHn; auto. f_equal; lia.
Qed.

Local Open Scope Z_scope.

Definition factorial (n : Z) : Z :=
  Z.of_nat (fact (Z.to_nat n)).

Lemma factorial_inc : forall n : Z,
  n >= 0 ->
  factorial (n + 1) = factorial n * (n + 1).
Proof.
  intros.
  unfold factorial.
  rewrite Z2Nat.inj_add; try lia.
  replace (Z.to_nat 1) with (S O) by auto.
  replace (Z.to_nat n + 1)%nat with (S (Z.to_nat n)) by lia.
  simpl. lia.
Qed.

Definition zeros (n : Z) := repeat 0 (Z.to_nat n).

Definition sum (l: list Z): Z :=
  fold_right Z.add 0 l.

Lemma sum_app: forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  intros.
  revert l2.
  induction l1; simpl; intros; auto.
  rewrite IHl1.
  lia.
Qed.

Lemma sum_bound : forall b l, (forall i, 0 <= i -> 0 <= Znth i l 0 <= b) -> 0 <= sum l <= Z.of_nat (length l) * b.
Proof.
  intros.
  revert H; induction l; intros; simpl in *; try lia.
  assert (forall i, 0 <= i -> 0 <= Znth i l 0 <= b).
  {
    intros.
    specialize (H (i + 1)). unfold Znth in *.
    replace (Z.to_nat (i + 1)) with (length ([a]) + Z.to_nat i)%nat in H by (simpl; lia).
    replace (a :: l) with ([a] ++ l) in H by auto.
    rewrite app_nth2_plus in H. lia.
  }
  pose proof (IHl H0).
  assert (0 <= a <= b) by (apply (H 0); simpl; lia).
  destruct b; lia.
Qed.

Lemma sum_bound_lt : forall b l, l <> [] -> (forall i, 0 <= i < Z.of_nat (length l) -> 0 <= Znth i l 0 < b) -> 0 <= sum l < Z.of_nat (length l) * b.
Proof.
  intros.
  revert H H0; induction l; intros; simpl in *; try lia.
  + contradiction.
  + assert (pureH : 0 <= a < b).
    {
      assert (0 <= 0 < Z.pos (Pos.of_succ_nat (length l))) by lia. simpl in *.
      specialize (H0 0 H1). unfold Znth in H0. simpl in H0.
      lia.
    }
    assert (forall i, 0 <= i < Z.of_nat (length l) -> 0 <= Znth i l 0 < b).
    {
      intros.
      specialize (H0 (i + 1)). unfold Znth in *.
      replace (Z.to_nat (i + 1)) with (length ([a]) + Z.to_nat i)%nat in H0 by (simpl; lia).
      replace (a :: l) with ([a] ++ l) in H0 by auto.
      rewrite app_nth2_plus in H0. lia.
    }
    destruct l; simpl in *.
    * destruct b; lia.
    * assert (z :: l <> []).
      { intro. inversion H2. }
      pose proof (IHl H2 H1).
      destruct b; lia.
Qed.

Inductive interval_list (pace lo hi : Z): list Z -> Prop :=
  | interval_list_nil: interval_list pace lo hi []
  | interval_list_cons: forall l x,
      interval_list pace lo hi l ->
      lo <= x -> x + pace <= hi ->
      Forall (fun x' => x + pace < x' \/ x' + pace < x) l ->
      interval_list pace lo hi (x :: l).

Theorem interval_list_valid1: forall l pace lo hi, interval_list pace lo hi l -> pace > 0 ->
  Forall (fun x => lo <= x < hi) l.
Proof.
  intros.
  induction H; simpl; auto.
  constructor; auto. lia.
Qed.

Theorem interval_list_valid2: forall l pace lo hi, interval_list pace lo hi l -> pace > 0 -> NoDup l.
Proof.
  intros.
  induction H; simpl; constructor; auto.
  rewrite Forall_forall in H3.
  intro.
  apply H3 in H4.
  lia.
Qed.

Theorem interval_list_valid3: forall l pace lo hi, interval_list pace lo hi l -> Forall (fun x => lo <= x /\ x + pace <= hi) l.
Proof.
  intros.
  induction H; simpl; constructor; auto.
Qed.

Definition Zlist_max (l: list Z) (lo : Z) : Z :=
  fold_right Z.max lo l.

Theorem interval_perm_keep: forall l l1 pace lo hi, interval_list pace lo hi l -> Permutation l l1 -> interval_list pace lo hi l1.
Proof.
  intros.
  induction H0; auto.
  - inversion H; subst.
    constructor; auto.
    rewrite <- H0. auto.
  - pose proof (interval_list_valid3 _ _ _ _ H).
    assert (Permutation (x :: y :: l) (y :: x :: l)).
    { constructor; auto. }
    rewrite <- H1 in H0.
    inversion H0. subst.
    inversion H; subst.
    inversion H5; subst.
    inversion H6; subst.
    inversion H9; subst.
    constructor; auto; try lia.
    + constructor; auto; try lia.
    + constructor; auto; try lia.
Qed.

Fixpoint increasing_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ increasing_aux l0 y
  end.

Definition increasing (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => increasing_aux l0 x
  end.

Lemma increasing_aux_tail_increasing :
  forall l x,
    increasing_aux l x ->
    increasing l.
Proof.
  intros l x Hinc.
  destruct l; simpl in *; auto.
  destruct Hinc as [_ Hinc].
  exact Hinc.
Qed.

Lemma increasing_aux_head_le_all_In :
  forall l x y,
    increasing_aux l x ->
    In y l ->
    x <= y.
Proof.
  induction l as [| a l IH]; intros x y Hinc Hin; simpl in *.
  - contradiction.
  - destruct Hinc as [Hxa Hinc].
    destruct Hin as [Hy | Hin].
    + subst. exact Hxa.
    + eapply Z.le_trans; [exact Hxa |].
      eapply IH; eauto.
Qed.

Fixpoint decreasing_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => y <= x /\ decreasing_aux l0 y
  end.

Definition decreasing (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => decreasing_aux l0 x
  end.

Lemma decreasing_aux_tail_decreasing :
  forall l x,
    decreasing_aux l x ->
    decreasing l.
Proof.
  intros l x Hdec.
  destruct l; simpl in *; auto.
  destruct Hdec as [_ Hdec].
  exact Hdec.
Qed.

Lemma decreasing_aux_head_ge_all_In :
  forall l x y,
    decreasing_aux l x ->
    In y l ->
    y <= x.
Proof.
  induction l as [| a l IH]; intros x y Hdec Hin; simpl in *.
  - contradiction.
  - destruct Hdec as [Hax Hdec].
    destruct Hin as [Hy | Hin].
    + subst. exact Hax.
    + eapply Z.le_trans; [| exact Hax].
      eapply IH; eauto.
Qed.

Fixpoint strict_decreasing_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => y < x /\ strict_decreasing_aux l0 y
  end.

Definition strict_decreasing (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => strict_decreasing_aux l0 x
  end.

Lemma strict_decreasing_aux_tail_strict_decreasing :
  forall l x,
    strict_decreasing_aux l x ->
    strict_decreasing l.
Proof.
  intros l x Hdec.
  destruct l; simpl in *; auto.
  destruct Hdec as [_ Hdec].
  exact Hdec.
Qed.

Lemma strict_decreasing_aux_head_gt_all_In :
  forall l x y,
    strict_decreasing_aux l x ->
    In y l ->
    y < x.
Proof.
  induction l as [| a l IH]; intros x y Hdec Hin; simpl in *.
  - contradiction.
  - destruct Hdec as [Hax Hdec].
    destruct Hin as [Hy | Hin].
    + subst. exact Hax.
    + eapply Z.lt_trans; [| exact Hax].
      eapply IH; eauto.
Qed.

Fixpoint upperbound (x: Z) (l: list Z): Prop :=
  match l with
  | nil => True
  | y :: l' => y <= x /\ upperbound x l'
  end.

Definition upper_bound := upperbound.

Fixpoint strict_upperbound (x: Z) (l: list Z): Prop :=
  match l with
  | nil => True
  | y :: l' => y < x /\ strict_upperbound x l'
  end.

Fixpoint lowerbound (x: Z) (l: list Z): Prop :=
  match l with
  | nil => True
  | y :: l' => x <= y /\ lowerbound x l'
  end.

Definition lower_bound := lowerbound.

Fixpoint strict_lowerbound (x: Z) (l: list Z): Prop :=
  match l with
  | nil => True
  | y :: l' => x < y /\ strict_lowerbound x l'
  end.

Definition prefix_suffix_sorted (prefix suffix: list Z): Prop :=
  forall x, In x prefix -> lowerbound x suffix.

Lemma upperbound_Znth :
  forall x l i,
    upperbound x l ->
    0 <= i < Zlength l ->
    Znth i l 0 <= x.
Proof.
  induction l as [| a l IH]; intros i Hbound Hi.
  - rewrite Zlength_nil in Hi. lia.
  - simpl in Hbound. destruct Hbound as [Ha Hbound].
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons. exact Ha.
    + rewrite Znth_cons by lia. apply IH; auto.
      rewrite Zlength_cons in Hi. lia.
Qed.

Lemma lowerbound_Znth :
  forall x l i,
    lowerbound x l ->
    0 <= i < Zlength l ->
    x <= Znth i l 0.
Proof.
  induction l as [| a l IH]; intros i Hbound Hi.
  - rewrite Zlength_nil in Hi. lia.
  - simpl in Hbound. destruct Hbound as [Ha Hbound].
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons. exact Ha.
    + rewrite Znth_cons by lia. apply IH; auto.
      rewrite Zlength_cons in Hi. lia.
Qed.

Lemma upperbound_intro_Znth :
  forall x l,
    (forall i, 0 <= i < Zlength l -> Znth i l 0 <= x) ->
    upperbound x l.
Proof.
  induction l as [| a l IH]; intros Hpoint; simpl; auto.
  pose proof (Zlength_nonneg l) as Hlen.
  split.
  - specialize (Hpoint 0 ltac:(rewrite Zlength_cons; lia)).
    rewrite Znth0_cons in Hpoint. exact Hpoint.
  - apply IH. intros i Hi.
    specialize (Hpoint (i + 1) ltac:(rewrite Zlength_cons; lia)).
    rewrite Znth_cons in Hpoint by lia.
    replace (i + 1 - 1) with i in Hpoint by lia.
    exact Hpoint.
Qed.

Lemma lowerbound_intro_Znth :
  forall x l,
    (forall i, 0 <= i < Zlength l -> x <= Znth i l 0) ->
    lowerbound x l.
Proof.
  induction l as [| a l IH]; intros Hpoint; simpl; auto.
  pose proof (Zlength_nonneg l) as Hlen.
  split.
  - specialize (Hpoint 0 ltac:(rewrite Zlength_cons; lia)).
    rewrite Znth0_cons in Hpoint. exact Hpoint.
  - apply IH. intros i Hi.
    specialize (Hpoint (i + 1) ltac:(rewrite Zlength_cons; lia)).
    rewrite Znth_cons in Hpoint by lia.
    replace (i + 1 - 1) with i in Hpoint by lia.
    exact Hpoint.
Qed.

Lemma strict_upperbound_app :
  forall x l v,
    strict_upperbound x l ->
    v < x ->
    strict_upperbound x (l ++ [v]).
Proof.
  intros x l.
  induction l as [| a l IH]; intros v Hbound Hv; simpl in *.
  - split; auto.
  - destruct Hbound as [Ha Hbound]. split; auto.
Qed.

Lemma upperbound_app :
  forall x l v,
    strict_upperbound x l ->
    v < x ->
    strict_upperbound x (l ++ [v]).
Proof.
  apply strict_upperbound_app.
Qed.

Lemma strict_lowerbound_cons :
  forall x l v,
    strict_lowerbound x l ->
    x < v ->
    strict_lowerbound x (v :: l).
Proof.
  intros. simpl. tauto.
Qed.

Lemma lowerbound_app_cons :
  forall x l y,
    lowerbound x l ->
    x <= y ->
    lowerbound x (l ++ [y]).
Proof.
  intros x l.
  induction l as [| a l IH]; intros y Hbound Hy; simpl in *.
  - split; auto.
  - destruct Hbound as [Ha Hbound]. split; auto.
Qed.

Lemma lowerbound_trans :
  forall x y l,
    x <= y ->
    lowerbound y l ->
    lowerbound x l.
Proof.
  intros x y l Hxy.
  induction l as [| a l IH]; intros Hbound; simpl in *; auto.
  destruct Hbound as [Ha Hbound]. split; [lia | auto].
Qed.

Lemma lowerbound_perm :
  forall x l1 l2,
    Permutation l1 l2 ->
    lowerbound x l1 ->
    lowerbound x l2.
Proof.
  intros x l1 l2 Hperm.
  induction Hperm; intros Hbound; simpl in *.
  - exact Hbound.
  - destruct Hbound as [Hx Hbound]. split; auto.
  - destruct Hbound as [Hx [Hy Hbound]]. split; [exact Hy | split; auto].
  - apply IHHperm2. apply IHHperm1. exact Hbound.
Qed.

Lemma upperbound_sublist_elim :
  forall x l lo hi i,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    upperbound x (sublist lo hi l) ->
    lo <= i < hi ->
    Znth i l 0 <= x.
Proof.
  intros x l lo hi i Hlohi Hhi Hub Hi.
  pose proof (upperbound_Znth x (sublist lo hi l) (i - lo) Hub) as Hle.
  rewrite Znth_sublist in Hle by lia.
  replace (i - lo + lo) with i in Hle by lia.
  apply Hle.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma upperbound_sublist_intro :
  forall x l lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall i, lo <= i < hi -> Znth i l 0 <= x) ->
    upperbound x (sublist lo hi l).
Proof.
  intros x l lo hi Hlohi Hhi Hrange.
  apply upperbound_intro_Znth.
  intros i Hi.
  assert (Hi' : 0 <= i < hi - lo).
  { rewrite Zlength_sublist in Hi by lia. lia. }
  rewrite Znth_sublist by lia.
  apply Hrange.
  lia.
Qed.

Lemma lowerbound_sublist_elim :
  forall x l lo hi i,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    lowerbound x (sublist lo hi l) ->
    lo <= i < hi ->
    x <= Znth i l 0.
Proof.
  intros x l lo hi i Hlohi Hhi Hlb Hi.
  pose proof (lowerbound_Znth x (sublist lo hi l) (i - lo) Hlb) as Hle.
  rewrite Znth_sublist in Hle by lia.
  replace (i - lo + lo) with i in Hle by lia.
  apply Hle.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma lowerbound_sublist_intro :
  forall x l lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall i, lo <= i < hi -> x <= Znth i l 0) ->
    lowerbound x (sublist lo hi l).
Proof.
  intros x l lo hi Hlohi Hhi Hrange.
  apply lowerbound_intro_Znth.
  intros i Hi.
  assert (Hi' : 0 <= i < hi - lo).
  { rewrite Zlength_sublist in Hi by lia. lia. }
  rewrite Znth_sublist by lia.
  apply Hrange.
  lia.
Qed.

Fixpoint list_insert (i : Z) (l : list Z) :=
  match l with
  | [] => [i]
  | h :: t => if Z_le_gt_dec i h then i :: h :: t else h :: list_insert i t
  end.

Fixpoint sort (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => list_insert h (sort t)
  end.

Lemma list_insert_In : forall x a l, In x (list_insert a l) <-> In x l \/ x = a.
Proof.
  intros.
  induction l; simpl in *; split; intros.
  - destruct H; auto.
  - destruct H; auto.
  - destruct (Z_le_gt_dec a a0).
    + destruct H; auto.
    + destruct H; auto. rewrite IHl in H.
      destruct H; auto.
  - destruct (Z_le_gt_dec a a0); simpl.
    + destruct H as [[? | ?] | ?]; auto.
    + rewrite IHl.
      destruct H as [[? | ?] | ?]; auto.
Qed.

Lemma increasing_aux_list_insert :
  forall a l x,
    increasing_aux l x ->
    x <= a ->
    increasing_aux (list_insert a l) x.
Proof.
  intros a l.
  induction l as [| y l IH]; intros x Hinc Hxa; simpl in *; auto.
  destruct Hinc as [Hxy Hinc].
  destruct (Z_le_gt_dec a y).
  - repeat split; auto; lia.
  - split; auto.
    apply IH; auto; lia.
Qed.

Lemma increasing_list_insert :
  forall a l,
    increasing l ->
    increasing (list_insert a l).
Proof.
  intros a l Hinc.
  destruct l as [| y l]; simpl in *; auto.
  destruct (Z_le_gt_dec a y).
  - repeat split; auto; lia.
  - apply increasing_aux_list_insert; auto; lia.
Qed.

Theorem sort_list_increasing : forall l, increasing (sort l).
Proof.
  intros.
  induction l; simpl in *; auto.
  apply increasing_list_insert.
  exact IHl.
Qed.

Lemma list_insert_perm : forall x l, Permutation (x :: l) (list_insert x l).
Proof.
  intros.
  induction l; simpl in *; auto.
  destruct (Z_le_gt_dec x a).
  - constructor; auto.
  - rewrite perm_swap. constructor; auto.
Qed.

Theorem sort_list_perm : forall l, Permutation l (sort l).
Proof.
  intros.
  induction l; simpl in *; auto.
  apply perm_trans with (l' := a :: sort l); auto.
  apply list_insert_perm.
Qed.

Lemma interval_list_compress : forall l pace lo1 hi1 lo2 hi2, interval_list pace lo1 hi1 l -> lo1 <= lo2 -> hi2 <= hi1 ->
  Forall (fun x => lo2 <= x /\ x + pace <= hi2) l -> interval_list pace lo2 hi2 l.
Proof.
  intros.
  generalize dependent lo2. generalize dependent hi2.
  induction H; intros; simpl.
  - constructor.
  - constructor; auto.
    + apply IHinterval_list; auto.
      inversion H5; auto.
    + inversion H5; lia.
    + inversion H5; lia.
Qed.

Theorem increasing_interval_list_range : forall l pace lo hi, pace >= 0 ->
lo <= hi -> 
interval_list pace lo hi l -> increasing l ->
lo + Zlength l * (pace + 1) <= hi + pace + 1.
Proof.
  intros. generalize dependent lo.
  induction l as [| a l IHl]; simpl; intros; auto.
  - lia.
  - inversion H1 as [| ? ? Hinter Hlo_a Ha_hi Hsep]; subst.
    rewrite Zlength_cons.
    assert (Htail_interval : interval_list pace (a + pace + 1) hi l).
    {
      apply interval_list_compress with (lo1 := lo) (hi1 := hi); auto; try lia.
      pose proof (interval_list_valid3 _ _ _ _ Hinter) as Hvalid.
      rewrite Forall_forall in *.
      intros x Hx.
      specialize (Hvalid _ Hx).
      specialize (Hsep _ Hx).
      pose proof (increasing_aux_head_le_all_In _ _ _ H2 Hx).
      lia.
    }
    assert (Htail_inc : increasing l).
    {
      apply increasing_aux_tail_increasing with (x := a).
      exact H2.
    }
    destruct l as [| b l'].
    + rewrite Zlength_nil. lia.
    + assert (Htail_lo_hi : a + pace + 1 <= hi).
      {
        pose proof (interval_list_valid3 _ _ _ _ Hinter) as Hvalid.
        rewrite Forall_forall in Hvalid.
        rewrite Forall_forall in Hsep.
        specialize (Hvalid b (or_introl eq_refl)).
        specialize (Hsep b (or_introl eq_refl)).
        pose proof (increasing_aux_head_le_all_In _ _ _ H2 (or_introl eq_refl)).
        lia.
      }
      specialize (IHl Htail_inc (a + pace + 1) Htail_lo_hi Htail_interval).
      lia.
Qed.

Theorem interval_list_range : forall l pace lo hi, pace >= 0 ->
lo <= hi ->
interval_list pace lo hi l ->
lo + Zlength l * (pace + 1) <= hi + pace + 1.
Proof.
  intros.
  pose proof (sort_list_perm l).
  assert (Zlength l = Zlength (sort l)).
  {
     rewrite !Zlength_correct.
     rewrite (Permutation_length H2); auto.
  }
  rewrite H3.
  apply (increasing_interval_list_range (sort l) pace lo hi); auto.
  + apply (interval_perm_keep l); auto.
  + apply sort_list_increasing.
Qed.


Theorem Zlength_replace_Znth : forall {A : Type} (l : list A) n (v : A),
   Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros.
  revert n.
  induction l ; simpl in * ; intros ; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  + simpl. do 2 rewrite Zlength_cons. lia.
  + simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
