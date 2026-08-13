Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.
Require Import ListLib.Base.Positional.

Lemma Forall2_split {A B : Type}: 
  forall (P : A -> B -> Prop) (n : nat) (xs: list A) (ys: list B),
  Forall2 P xs ys ->
  Forall2 P (firstn n xs) (firstn n ys) /\
  Forall2 P (skipn n xs) (skipn n ys).
Proof.
  induction n; intros; simpl.
  - split.
    + constructor.
    + auto.
  - destruct xs; destruct ys; simpl in *; inversion H.
    + split; constructor.
    + destruct (IHn _ _ H5). split.
      * constructor; auto.
      * auto.
Qed.

Lemma Forall2_congr : forall (A B : Type) (p p' : A -> B -> Prop) xs ys,
  (forall x y, In x xs -> In y ys -> p x y -> p' x y) ->
  Forall2 p xs ys ->
  Forall2 p' xs ys.
Proof.
  intros. induction H0.
  - constructor.
  - constructor.
    + apply H; auto.
      * left. auto.
      * left. auto.
    + apply IHForall2. intros.
      apply H; auto.
      * right. auto.
      * right. auto.
Qed.
(* Forall2_impl *)

Lemma Forall2_cons_nil_l {A B: Type} {R: A -> B -> Prop}: 
  forall xs,
    Forall2 R nil xs ->
    xs = nil.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Lemma Forall2_cons_nil_inv_l {A B: Type} {R: A -> B -> Prop}: 
  forall x ys,
    Forall2 R [x] ys ->
    exists y, ys = [y] /\ R x y.
Proof.
  intros x ys H.
  inversion H.
  subst.
  apply Forall2_cons_nil_l in H4.
  subst.
  exists y.
  tauto.
Qed.

Lemma Forall2_cons_inv_l {A B: Type} {R: A -> B -> Prop}: 
  forall x xs ys,
  Forall2 R (x :: xs) ys ->
  exists y ys',
    ys = y :: ys' /\ R x y /\ Forall2 R xs ys'.
Proof.
  intros.
  assert (E : x :: xs = [x] ++ xs) by reflexivity.
  rewrite E in H; clear E.
  apply Forall2_app_inv_l in H.
  destruct H as (xs' & ys' & H1 & H2 & H3).
  apply Forall2_cons_nil_inv_l in H1.
  destruct H1 as [z [? ?] ].
  subst xs'.
  eauto.
Qed.

Lemma Forall2_cons_nil_r {A B: Type} {R: A -> B -> Prop}: 
  forall xs,
  Forall2 R xs nil ->
  xs = nil.
Proof.
  intros xs H.
  inversion H.
  reflexivity.
Qed.

Lemma Forall2_cons_nil_inv_r {A B: Type} {R: A -> B -> Prop}: 
  forall xs y,
  Forall2 R xs [y] ->
  exists x, xs = [x] /\ R x y.
Proof.
  intros y ys H.
  inversion H.
  subst.
  apply Forall2_cons_nil_r in H4.
  subst.
  exists x.
  tauto.
Qed.

Lemma Forall2_cons_inv_r {A B: Type} {R: A -> B -> Prop}: 
  forall xs y ys,
  Forall2 R xs (y :: ys) ->
  exists x xs',
    xs = x :: xs' /\ R x y /\ Forall2 R xs' ys.
Proof.
  intros.
  assert (E : y :: ys = [y] ++ ys) by reflexivity.
  rewrite E in H; clear E.
  apply Forall2_app_inv_r in H.
  destruct H as (xs' & ys' & H1 & H2 & H3).
  apply Forall2_cons_nil_inv_r in H1.
  destruct H1 as [x [? ?] ].
  subst xs'.
  eauto.
Qed.

Lemma Forall2_nth_iff : forall (A B : Type)
  (P : A -> B -> Prop) xs ys dx dy,
  Forall2 P xs ys <->
  (length xs = length ys /\
   forall n, n < length xs ->
     P (nth n xs dx) (nth n ys dy)).
Proof.
  intros. split; intros.
  - split. apply (@Forall2_length _ _ _ _ _ H).
    intros.
    assert (n < length ys).
    { rewrite <- (@Forall2_length _ _ _ _ _ H); auto. }
    rewrite (firstn_skipSn dx _ _ H0) in H. 
    rewrite (firstn_skipSn dy _ _ H1) in H.
    apply (Forall2_split _ n) in H.
    destruct H as [_ ?].
    rewrite ! skipn_app in H.
    assert (n = length (firstn n xs)).
    { rewrite length_firstn. rewrite min_l; auto. lia. }
    assert (skipn n (firstn n xs) = nil).
    { transitivity (skipn (length (firstn n xs)) (firstn n xs)).
      - congruence.
      - apply skipn_all. }
    assert (n = length (firstn n ys)).
    { rewrite length_firstn. rewrite min_l; auto. lia. }
    assert (skipn n (firstn n ys) = nil).
    { transitivity (skipn (length (firstn n ys)) (firstn n ys)).
      - congruence.
      - apply skipn_all. }
    rewrite H3 in H. rewrite H5 in H. simpl in H.
    replace (n - length (firstn n xs)) with O in H by lia.
    replace (n - length (firstn n ys)) with O in H by lia.
    simpl in H. inversion H. auto.
  - destruct H. generalize dependent ys.
    induction xs; intros; destruct ys; simpl in *; try lia.
    + constructor.
    + constructor.
      * specialize (H0 O). apply H0. lia.
      * apply IHxs; auto.
        intros. apply (H0 (S n)). lia.
Qed.


Lemma Forall2_map1 {A B C : Type} : 
forall (P : C -> B -> Prop) xs ys (f : A -> C),
  Forall2 (fun x y => P (f x) y) xs ys <->
  Forall2 P (map f xs) ys.
Proof.
  induction xs; intros; destruct ys; simpl; split; intros.
  - constructor.
  - constructor.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
Qed.

Lemma Forall2_map2 {A B C : Type} : 
forall (P : A -> C -> Prop) xs ys (f : B -> C),
  Forall2 (fun x y => P x (f y)) xs ys <->
  Forall2 P xs (map f ys).
Proof.
  induction xs; intros; destruct ys; simpl; split; intros.
  - constructor.
  - constructor.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
Qed.

Section Forall2And.

Context {A B : Type}.

(* ---------- 1. 合取构造 ---------- *)
Theorem Forall2_and (R1 R2 : A -> B -> Prop) l l' :
  Forall2 R1 l l' ->
  Forall2 R2 l l' ->
  Forall2 (fun a b => R1 a b /\ R2 a b) l l'.
Proof.
  intros H1 H2.
  generalize dependent H2.
  induction H1 as [| x y l l' H1R H1IH H1l]; intros H2.
  - constructor.
  - inversion H2; subst.
    constructor; tauto.
Qed.

(* ---------- 2. 合取拆解 ---------- *)
Theorem Forall2_and_inv (R1 R2 : A -> B -> Prop) l l' :
  Forall2 (fun a b => R1 a b /\ R2 a b) l l' ->
  Forall2 R1 l l' /\ Forall2 R2 l l'.
Proof.
  split.
  - induction H; constructor; tauto.
  - induction H; constructor; tauto.
Qed.

(* ---------- 3. 左加 Forall ---------- *)
Theorem Forall2_and_Forall_l (P : A -> Prop) (R : A -> B -> Prop) l l' :
  Forall P l ->
  Forall2 R l l' ->
  Forall2 (fun a b => P a /\ R a b) l l'.
Proof.
  intros HP HR.
  induction HR in HP |- *.
  - constructor.
  - inversion HP; constructor; tauto.
Qed.

(* ---------- 4. 右加 Forall ---------- *)
Theorem Forall2_and_Forall_r (P : A -> Prop) (R : A -> B -> Prop) l l' :
  Forall2 R l l' ->
  Forall P l ->
  Forall2 (fun a b => R a b /\ P a) l l'.
Proof.
  intros HR HP.
  induction HR in HP |- *.
  - constructor.
  - inversion HP; constructor; tauto.
Qed.

End Forall2And.

Lemma Forall_in_cons {A: Type}:
  forall (l: list A) e p,
    Forall (fun x => In x (e :: l)) p ->
    ~ In e p ->
    Forall (fun x => In x l) p.
Proof.
  intros l e p Hforall Hnotin.
  rewrite Forall_forall in *.
  intros x Hin.
  pose proof Hforall _ Hin as [|]; [subst; contradiction|auto].
Qed.