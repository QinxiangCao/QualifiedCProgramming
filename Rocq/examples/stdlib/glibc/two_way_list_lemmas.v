Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Orders.
Require Import SetsClass.SetsClass.
Require Import ListLib.Base.Inductive.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
Require Import ListLib.General.Presuffix.
From AUXLib Require Import ListLib relations.

Import ListNotations.
Import SetsNotation.

Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sets.

(* Shared list lemmas for the two_way high-level specification proof. *)

Lemma Zlength_zero_iff_nil {A : Type} (l : list A) :
  Zlength l = 0 -> l = nil.
Proof.
  apply Zlength_nil_inv.
Qed.

Section SublistExtend.

Lemma Zsublist_all {A : Type} (l : list A):
  sublist 0 (Zlength l) l = l.
Proof.
  unfold sublist. simpl.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  apply firstn_all.
Qed.

Lemma Zsublist_hi_plus_1 {A : Type} (default : A) (l1 l2 : list A) (lo hi lo' hi' : Z):
  (0 <= lo <= hi) ->
  (hi + 1 <= Zlength l1) ->
  (0 <= lo' <= hi') ->
  (hi' + 1 <= Zlength l2) ->
  sublist lo hi l1 = sublist lo' hi' l2 ->
  Znth hi l1 default = Znth hi' l2 default ->
  sublist lo (hi + 1) l1 = sublist lo' (hi' + 1) l2.
Proof.
  intros.
  rewrite (sublist_split lo (hi + 1) hi); try lia.
  rewrite (sublist_split lo' (hi' + 1) hi'); try lia.
  rewrite H3.
  rewrite (sublist_single default hi l1); try lia.
  rewrite (sublist_single default hi' l2); try lia.
  rewrite H4.
  easy.
Qed.

Lemma Zsublist_neg_iff_Zsublist_zero {A : Type} (lo hi : Z) (l : list A):
  lo <= 0 -> sublist lo hi l = sublist 0 hi l.
Proof.
  intros. unfold sublist.
  assert (Z.to_nat lo = 0)%nat by lia.
  rewrite H0. simpl. reflexivity.
Qed.

Lemma Zsublist_overflow_iff_Zsublist_Zlength {A : Type} (lo hi : Z) (l : list A): 
  0 <= Zlength l < hi -> sublist lo hi l = sublist lo (Zlength l) l.
Proof.
  intros.
  unfold sublist.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite firstn_all.
  assert (Z.to_nat hi > Z.to_nat (Zlength l))%nat.
  { apply Z2Nat.inj_lt; try lia. }
  assert (Z.to_nat hi > length l)%nat.
  { pose proof Zlength_correct l.
    apply (f_equal (fun z => Z.to_nat z)) in H1.
    rewrite H1 in H0.
    rewrite Nat2Z.id in H0.
    apply H0. }
  rewrite firstn_all2; try lia.
  reflexivity.
Qed.

Lemma Znth_neg_iff_Znth_zero {A : Type} (i : Z) (l : list A) (default : A):
  i < 0 -> Znth i l default = Znth 0 l default.
Proof.
  intros. unfold Znth.
  assert (Z.to_nat i = 0)%nat by lia.
  rewrite H0. simpl. reflexivity.
Qed.

Lemma Zsublist_app_exact2 {A : Type} (l1 l2 : list A):
  forall len,
    len = Zlength l1 + Zlength l2 ->
    sublist (Zlength l1) len (l1 ++ l2) = l2.
Proof.
  intros.
  rewrite (sublist_split_app_r _ _ (Zlength l1)).
  - replace (Zlength l1 - Zlength l1) with 0 by lia.
    replace (len - Zlength l1) with (Zlength l2) by lia.
    apply Zsublist_all.
  - reflexivity.
  - pose proof Zlength_nonneg l2.
    lia.
Qed.

Lemma Zsublist_suffix_inv {A : Type} (lo hi : Z) (w l : list A):
  0 <= lo <= hi /\ hi <= Zlength l ->
  is_suffix w (sublist lo hi l) ->
  w = sublist (hi - Zlength w) hi l.
Proof.
  intros H0 H.
  destruct H as [w' H].
  pose proof H as H'.
  apply (f_equal (fun l => Zlength l)) in H.
  rewrite Zlength_app in H.
  rewrite Zlength_sublist in H.
  assert (0 <= Zlength w /\ 0 <= Zlength w').
  { split; apply Zlength_nonneg. }
  apply (f_equal (fun l => sublist (Zlength w') (hi - lo) l)) in H'.
  rewrite Zsublist_Zsublist in H'; try auto; try lia.
  - rewrite (Zsublist_app_exact2 _ _ _) in H'; try lia.
    replace (Zlength w' + lo) with (hi - Zlength w) in H' by lia.
    replace (hi - lo + lo) with hi in H' by lia.
    auto.
  - auto.
Qed.

Lemma Zsublist_suffix_range {A : Type} (lo hi : Z) (w l : list A):
  0 <= lo <= hi /\ hi <= Zlength l ->
  is_suffix w (sublist lo hi l) ->
  lo <= hi - Zlength w.
Proof.
  intros.
  destruct H0 as [v ?].
  apply (f_equal (fun l => Zlength l)) in H0.
  rewrite Zlength_sublist in H0; try lia.
  rewrite Zlength_app in H0.
  pose proof Zlength_nonneg v.
  lia.
Qed.  

Lemma Zsublist_prefix_inv {A : Type} (lo hi : Z) (w l : list A):
  0 <= lo <= hi /\ hi <= Zlength l ->
  is_prefix w (sublist lo hi l) ->
  w = sublist lo (lo + Zlength w) l.
Proof.
  intros H0 H.
  destruct H as [w' H].
  pose proof H as H'.
  apply (f_equal (fun l => Zlength l)) in H.
  rewrite Zlength_app in H.
  rewrite Zlength_sublist in H.
  assert (0 <= Zlength w /\ 0 <= Zlength w').
  { split; apply Zlength_nonneg. }
  apply (f_equal (fun l => sublist 0 (Zlength w) l)) in H'.
  rewrite Zsublist_Zsublist in H'; simpl in *; try lia.
  - rewrite sublist_app_exact1 in H'.
    rewrite Z.add_comm. auto.
  - auto.
Qed.

Lemma Zsublist_prefix_range {A : Type} (lo hi : Z) (w l: list A):
  0 <= lo <= hi /\ hi <= Zlength l ->
  is_prefix w (sublist lo hi l) ->
  lo + Zlength w <= hi.
Proof.
  intros.
  destruct H0 as [v ?].
  apply (f_equal (fun l => Zlength l)) in H0.
  rewrite Zlength_sublist in H0; try lia.
  rewrite Zlength_app in H0.
  pose proof Zlength_nonneg v.
  lia.
Qed.

Lemma Zsublist_eq_ext {A : Type} (default : A) (l1 l2 : list A):
  Zlength l1 = Zlength l2 ->
  (forall i, 0 <= i < Zlength l1 ->
    Znth i l1 default = Znth i l2 default) ->
  l1 = l2.
Proof.
  intros.
  apply (nth_ext _ _ default default).
  - repeat rewrite Zlength_correct in H.
    apply (f_equal (fun z => Z.to_nat z)) in H.
    repeat rewrite Nat2Z.id in H.
    apply H.
  - intros.
    set (m := Z.of_nat n).
    assert (0 <= m < Zlength l1).
    { subst m.
      rewrite Zlength_correct.
      split; [lia|].
      apply Nat2Z.inj_lt. lia. }
    specialize (H0 m H2).
    unfold Znth in H0. subst m.
    rewrite Nat2Z.id in H0. auto.
Qed.

Lemma Zsublist_is_prefix {A : Type} (l : list A) (lo hi hi' : Z):
  0 <= lo <= hi ->
  hi <= hi' <= Zlength l ->
  is_prefix (sublist lo hi l) (sublist lo hi' l).
Proof.
  intros.
  unfold is_prefix.
  exists (sublist hi hi' l).
  rewrite (sublist_split _ _ hi) at 1; try lia.
  reflexivity.
Qed.

Lemma Zsublist_is_suffix {A : Type} (l : list A) (lo lo' hi : Z):
  0 <= lo <= lo' ->
  lo' <= hi <= Zlength l ->
  is_suffix (sublist lo' hi l) (sublist lo hi l).
Proof.
  intros.
  unfold is_suffix.
  exists (sublist lo lo' l).
  rewrite (sublist_split _ _ lo') at 1; try lia.
  reflexivity.
Qed.

Lemma is_prefix_refl {A : Type} (w : list A):
  is_prefix w w.
Proof.
  unfold is_prefix.
  exists nil.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma Znth_Zsublist_tail {A : Type} (default : A) (p : list A) (x : A):
  Znth (Zlength p) (p ++ x :: nil) default = x.
Proof.
  rewrite app_Znth2.
  - replace (Zlength p - Zlength p) with 0 by lia.
    rewrite Znth0_cons. reflexivity.
  - lia.
Qed.

Lemma Znth_Zsublist_single {A : Type} (default : A) (p l1 : list A) (x : A): 
  Znth (Zlength p) (p ++ x :: l1) default = x.
Proof.
  assert (p ++ x :: l1 = (p ++ x :: nil) ++ l1).
  { rewrite <- app_assoc. simpl. reflexivity. }
  rewrite H. rewrite app_Znth1.
  - apply Znth_Zsublist_tail.
  - rewrite Zlength_app.
    assert (Zlength [x] = 1).
    { rewrite Zlength_correct. simpl. reflexivity. }
    pose proof Zlength_nonneg p.
    lia.
Qed.

Lemma Zsublist_split_mid {A : Type} (default : A) (l : list A) (len : Z):
  0 <= len < Zlength l ->
  l = sublist 0 len l ++ (Znth len l default) :: sublist (len + 1) (Zlength l) l.
Proof.
  intros.
  rewrite <- (Zsublist_all l) at 1.
  rewrite (sublist_split _ _ len); try lia.
  rewrite (sublist_split len _ (len + 1)); try lia.
  rewrite (sublist_single default); try lia.
  simpl. reflexivity.
Qed.

End SublistExtend.
Section LexCompare.
Context (A : Type).
Context (default : A).

Class Cmp (cmp_fn : A -> A -> comparison)  := {
  cmp_Lt_Gt : forall x y, cmp_fn x y = Lt -> cmp_fn y x = Gt;
  cmp_Gt_Lt : forall x y, cmp_fn x y = Gt -> cmp_fn y x = Lt;
  cmp_Eq    : forall x y, cmp_fn x y = Eq -> x = y /\ cmp_fn y x = Eq;
  cmp_refl  : forall x, cmp_fn x x = Eq;
  cmp_trans : forall x y z, cmp_fn x y = Gt -> cmp_fn y z = Gt -> cmp_fn x z = Gt
}.

Context (cmp : A -> A -> comparison).
Context (CmpA : Cmp cmp).
Existing Instance CmpA.

Definition cmp_rev : A -> A -> comparison :=
  fun x y => CompOpp (cmp x y).

Instance Cmp_rev : Cmp cmp_rev.
Proof.
  constructor.
  - (* Lt -> Gt *)
    intros.
    unfold cmp_rev in *.
    pose proof cmp_Gt_Lt x y.
    destruct (cmp x y); try discriminate.
    rewrite H0; auto.
  - (* Gt -> Lt *)
    intros.
    unfold cmp_rev in *.
    pose proof cmp_Lt_Gt x y.
    destruct (cmp x y); try discriminate.
    rewrite H0; auto.
  - (* Eq *)
    intros.
    unfold cmp_rev in *.
    pose proof cmp_Eq x y.
    destruct (cmp x y); try discriminate.
    destruct H0; try auto.
    rewrite H1. auto.
  - (* refl *)
    intros.
    unfold cmp_rev.
    rewrite cmp_refl.
    auto.
  - (* trans *)
    intros.
    unfold cmp_rev in *.
    pose proof cmp_trans z y x.
    pose proof cmp_Lt_Gt x y.
    pose proof cmp_Lt_Gt y z.
    destruct (cmp x y); destruct (cmp y z); try discriminate.
    specialize (H2 ltac:(easy)).
    specialize (H3 ltac:(easy)).
    specialize (H1 H3 H2).
    pose proof cmp_Gt_Lt z x H1.
    rewrite H4. auto.
Qed.

(* =============== Two Instance ================ *)

Section list_lex_cmp.

Definition list_lex_gt_ex (cmp_fn : A -> A -> comparison) (l1 l2 : list A) : Prop :=
  exists p x y l1' l2',
    l1 = p ++ x :: l1' /\ 
    l2 = p ++ y :: l2' /\ 
    cmp_fn x y = Gt.

Definition list_lex_gt_ex' (cmp_fn : A -> A -> comparison) (l1 l2 : list A) (len : Z) : Prop :=
  sublist 0 len l1 = sublist 0 len l2 
    /\ cmp_fn (Znth len l1 default) (Znth len l2 default) = Gt.

Theorem list_lex_gt_ex_ex' (cmp_fn : A -> A -> comparison) (l1 l2 : list A):
  (list_lex_gt_ex cmp_fn l1 l2) <-> 
  (exists len, 0 <= len /\
    len < Zlength l1 /\
    len < Zlength l2 /\
    list_lex_gt_ex' cmp_fn l1 l2 len).
Proof.
  split; intros.
  - unfold list_lex_gt_ex in H.
    destruct H as [p [x [y [l1' [l2' H]]]]].
    destruct H as [? [? ?]].
    exists (Zlength p).
    split; [|split; [|split]].
    + apply Zlength_nonneg.
    + rewrite H.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      pose proof Zlength_nonneg l1'.
      lia.
    + rewrite H0.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      pose proof Zlength_nonneg l2'.
      lia.
    + unfold list_lex_gt_ex'.
      split; rewrite H; rewrite H0.
      * rewrite sublist_app_exact1;
        rewrite sublist_app_exact1.
        reflexivity.
      * repeat rewrite Znth_Zsublist_single.
        auto.
  - destruct H as [len [? [? [? ?]]]].
    destruct H2.
    unfold list_lex_gt_ex.
    set (p := sublist 0 len l1).
    set (x := Znth len l1 default).
    set (y := Znth len l2 default).
    set (l1' := sublist (len + 1) (Zlength l1) l1).
    set (l2' := sublist (len + 1) (Zlength l2) l2).
    exists p. exists x. exists y.
    exists l1'. exists l2'.
    split; [|split].
    + subst p x l1'.
      rewrite <- (Zsublist_all l1) at 1.
      rewrite (sublist_split _ _ len l1); try lia.
      rewrite (sublist_split len _ (len + 1) l1); try lia.
      rewrite (sublist_single default); try lia.
      simpl. reflexivity.
    + subst p y l2'.
      rewrite <- (Zsublist_all l2) at 1.
      rewrite H2.
      rewrite (sublist_split _ _ len l2); try lia.
      rewrite (sublist_split len _ (len + 1) l2); try lia.
      rewrite (sublist_single default); try lia.
      simpl. reflexivity.
    + subst x y. auto.
Qed.

Definition is_proper_prefix (l1 l2 : list A): Prop :=
  is_prefix l1 l2 /\ Zlength l1 < Zlength l2.

(* two cases *)
Definition list_lex_gt (cmp_fn : A -> A -> comparison) (l1 l2 : list A) : Prop :=
  list_lex_gt_ex cmp_fn l1 l2 \/ is_proper_prefix l2 l1.

(* maximal suffix is unique, two cases *)
Definition list_lex_ge (cmp_fn : A -> A -> comparison) (l1 l2 : list A) : Prop :=
  list_lex_gt cmp_fn l1 l2 \/ l1 = l2.

Fact list_lex_ge_nil (cmp_fn : A -> A -> comparison):
  forall l, list_lex_ge cmp_fn l [].
Proof.
  intros.
  set (len := Zlength l).
  destruct (Z_lt_ge_dec len 0) as [H|H].
  - pose proof Zlength_nonneg l. lia.
  - destruct (Z_le_gt_dec len 0) as [H1|H1].
    + assert (len = 0) by lia.
      pose proof (Zlength_zero_iff_nil l H0).
      right. auto.
    + clear H. left. right.
      unfold is_proper_prefix.
      split.
      * apply nil_prefix.
      * rewrite Zlength_nil.
        lia. (* Note: Zlength does not simplify via simpl *)
Qed.

Lemma proper_prefix_discriminate_gt_ex (cmp_fn : A -> A -> comparison) (l1 l2 : list A):
  Cmp cmp_fn ->
  list_lex_gt_ex cmp_fn l1 l2 ->
  is_proper_prefix l2 l1 -> False.
Proof.
  intros Cmpfn. intros.
  destruct H as [p [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  destruct H0.
  destruct H0 as [l3 ?].
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite <- app_assoc in H.
  apply app_inv_head in H.
  simpl in H.
  injection H. intros.
  assert (cmp_fn x y = Eq).
  { rewrite H5. apply cmp_refl. }
  rewrite H6 in H2. discriminate.
Qed.

Lemma proper_prefix_discriminate_gt_ex' (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  Cmp cmp_fn ->
  list_lex_gt_ex cmp_fn l1 l2 ->
  is_proper_prefix l1 l2 -> False.
Proof.
  intros Cmpfn. intros.
  destruct H as [p [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  destruct H0.
  destruct H0 as [l3 ?].
  rewrite H0 in H1.
  rewrite H in H1.
  rewrite <- app_assoc in H1.
  apply app_inv_head in H1.
  simpl in H1.
  injection H1. intros.
  assert (cmp_fn x y = Eq).
  { rewrite H5. apply cmp_refl. }
  rewrite H6 in H2. discriminate.
Qed.

Lemma gtex_discriminate_gtex (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  Cmp cmp_fn ->
  list_lex_gt_ex cmp_fn l1 l2 ->
  list_lex_gt_ex cmp_fn l2 l1 -> False.
Proof.
  intros Cmpfn. intros.
  unfold list_lex_gt_ex in *.
  destruct H as [p [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  destruct H0 as [p' [x' [y' [l1'' [l2'' ?]]]]].
  destruct H0 as [? [? ?]].
  rewrite H3 in H.
  apply app_eq_app in H.
  rewrite H0 in H1.
  apply app_eq_app in H1.
  destruct H as [[lp [? ?]] | [lp [? ?]]];
  destruct H1 as [[lp' [? ?]] | [lp' [? ?]]].
  + rewrite H1 in H.
    apply app_inv_head in H.
    subst lp'. destruct lp.
    * simpl in *.
      injection H5.
      injection H6.
      intros. subst x' y'.
      apply cmp_Gt_Lt in H4.
      rewrite H4 in H2.
      discriminate.
    * simpl in *.
      injection H5.
      injection H6.
      intros.
      assert (cmp_fn x y = Eq).
      { rewrite H7. rewrite H9. apply cmp_refl. }
      rewrite H10 in H2.
      discriminate.
  + rewrite H1 in H.
    rewrite <- app_assoc in H.
    replace p' with (p' ++ nil) in H at 1.
    2:{ rewrite app_nil_r. reflexivity. }
    apply app_inv_head in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H. subst lp lp'.
    simpl in *.
    injection H5.
    injection H6.
    intros.
    rewrite H7 in H4.
    rewrite <- H9 in H4.
    apply cmp_Gt_Lt in H4.
    rewrite H4 in H2.
    discriminate.
  + rewrite H1 in H.
    rewrite <- app_assoc in H.
    replace p with (p ++ nil) in H at 1.
    2:{ rewrite app_nil_r. reflexivity. }
    apply app_inv_head in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H. subst lp lp'.
    simpl in *.
    injection H5.
    injection H6.
    intros.
    rewrite <- H7 in H4.
    rewrite H9 in H4.
    apply cmp_Gt_Lt in H4.
    rewrite H4 in H2.
    discriminate.
  + rewrite H1 in H.
    apply app_inv_head in H.
    subst lp'. destruct lp.
    * simpl in *.
      injection H5.
      injection H6.
      intros. subst x' y'.
      apply cmp_Gt_Lt in H4.
      rewrite H4 in H2.
      discriminate.
    * simpl in *.
      injection H5.
      injection H6.
      intros.
      assert (cmp_fn x' y' = Eq).
      { rewrite H7. rewrite H9. apply cmp_refl. }
      rewrite H10 in H4.
      discriminate.
Qed.

Lemma gt_discriminate_gt (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  Cmp cmp_fn ->
  list_lex_gt cmp_fn l1 l2 ->
  list_lex_gt cmp_fn l2 l1 -> False.
Proof.
  intros Cmpfn. intros.
  destruct H; destruct H0.
  - apply (gtex_discriminate_gtex _ _ _ _ H H0).
  - destruct H0 as [[l3 ?] ?].
    destruct H as [p [x [y [l1' [l2' ?]]]]].
    destruct H as [? [? ?]].
    rewrite H in H0. rewrite H2 in H0.
    rewrite <- app_assoc in H0. simpl in H0.
    apply app_inv_head in H0.
    injection H0. intros.
    rewrite H5 in H3.
    rewrite cmp_refl in H3.
    discriminate.
  - destruct H as [[l3 ?] ?].
    destruct H0 as [p [x [y [l1' [l2' ?]]]]].
    destruct H0 as [? [? ?]].
    rewrite H0 in H. rewrite H2 in H.
    rewrite <- app_assoc in H. simpl in H.
    apply app_inv_head in H.
    injection H. intros.
    rewrite H5 in H3.
    rewrite cmp_refl in H3.
    discriminate.
  - destruct H as [[l3 ?] ?].
    destruct H0 as [[l4 ?] ?].
    rewrite H0 in H.
    rewrite <- (app_nil_r l1) in H at 1.
    rewrite <- app_assoc in H.
    apply app_inv_head in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H. subst l3 l4.
    rewrite app_nil_r in H0.
    rewrite H0 in H1.
    lia.
Qed.

Lemma ge_discriminate_gt (cmp_fn : A -> A -> comparison) (l1 l2 : list A): 
  Cmp cmp_fn ->
  list_lex_ge cmp_fn l1 l2 ->
  list_lex_gt cmp_fn l2 l1 -> False.
Proof.
  intros Cmpfn. intros.
  destruct H.
  - apply (gt_discriminate_gt _ _ _ _ H H0).
  - rewrite H in H0.
    unfold list_lex_gt in H0.
    destruct H0.
    + unfold list_lex_gt_ex in H0.
      destruct H0 as [p [x [y [l1' [l2' ?]]]]].
      destruct H0 as [? [? ?]].
      rewrite H1 in H0.
      apply app_inv_head in H0.
      injection H0. intros.
      rewrite H4 in H2. rewrite cmp_refl in H2.
      discriminate.
    + destruct H0 as [[l3 ?] ?].
      lia.
Qed.

Lemma list_lex_gt_ex_trans (cmp_fn : A -> A -> comparison):
  Cmp cmp_fn ->
  forall l1 l2 l3,
    list_lex_gt_ex cmp_fn l1 l2 ->
    list_lex_gt_ex cmp_fn l2 l3 ->
    list_lex_gt_ex cmp_fn l1 l3.
Proof.
  intros Cmpfn. intros.
  unfold list_lex_gt_ex in *.
  destruct H as [p [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  destruct H0 as [p' [x' [y' [l1'' [l2'' ?]]]]].
  destruct H0 as [? [? ?]].
  set (len := Zlength p).
  set (len' := Zlength p').
  assert (0 <= len /\ 0 <= len').
  { split; apply Zlength_nonneg. }
  destruct (Z.lt_trichotomy len len') as [Hlt | [Heq | Hgt]].
  - exists p. exists x. exists (Znth len l3 default).
    exists l1'. exists (sublist (len + 1) (Zlength l3) l3).
    split; [|split].
    + auto.
    + assert (p = sublist 0 len l3).
      { apply (f_equal (fun l => sublist 0 len l)) in H1.
        apply (f_equal (fun l => sublist 0 len l)) in H0.
        rewrite H3.
        rewrite sublist_split_app_l; try lia.
        rewrite sublist_split_app_l in H0; try lia.
        rewrite <- H0.
        rewrite (sublist_app_exact1 p) in H1.
        rewrite H1. reflexivity. }
      rewrite H6.
      apply Zsublist_split_mid.
      assert (len' < Zlength l3).
      { rewrite H3.
        rewrite Zlength_app.
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l2''.
        lia. }
      lia.
    + assert (y = Znth len l3 default).
      { apply (f_equal (fun l => Znth len l default)) in H1.
        apply (f_equal (fun l => Znth len l default)) in H0.
        apply (f_equal (fun l => Znth len l default)) in H3.
        rewrite app_Znth1 in H0, H3; try lia.
        subst len.
        rewrite (Znth_Zsublist_single default) in H1.
        rewrite <- H1. rewrite H0. rewrite H3.
        reflexivity. }
      rewrite <- H6.
      auto.
  - exists p. exists x. exists y'.
    exists l1'. exists l2''.
    split; [|split].
    + auto.
    + assert (p = p').
      { apply (f_equal (fun l => sublist 0 len l)) in H1.
        apply (f_equal (fun l => sublist 0 len l)) in H0.
        subst len len'.
        rewrite sublist_app_exact1 in H1.
        rewrite Heq in H0 at 2.
        rewrite sublist_app_exact1 in H0.
        rewrite <- H1. rewrite H0. reflexivity. }
      rewrite H6. auto.
    + assert (y = x').
      { apply (f_equal (fun l => Znth len l default)) in H1.
        apply (f_equal (fun l => Znth len l default)) in H0.
        subst len len'.
        rewrite Znth_Zsublist_single in H1.
        rewrite Heq in H0 at 2.
        rewrite Znth_Zsublist_single in H0.
        rewrite <- H1. rewrite H0. reflexivity. }
      rewrite <- H6  in H4.
      apply (cmp_trans _ y _); auto.
  - exists p'. exists (Znth len' l1 default). exists y'.
    exists (sublist (len' + 1) (Zlength l1) l1). exists l2''.
    split; [|split].
    + assert (p' = sublist 0 len' l1).
      { apply (f_equal (fun l => sublist 0 len' l)) in H1.
        apply (f_equal (fun l => sublist 0 len' l)) in H0.
        rewrite H.
        rewrite sublist_split_app_l; try lia.
        rewrite sublist_split_app_l in H1; try lia.
        rewrite <- H1.
        rewrite (sublist_app_exact1 p') in H0.
        rewrite H0. reflexivity. }
      rewrite H6.
      apply Zsublist_split_mid.
      assert (len' < Zlength l1).
      { rewrite H.
        rewrite Zlength_app.
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l1'.
        lia. }
      lia.
    + auto.
    + assert (x' = Znth len' l1 default).
      { apply (f_equal (fun l => Znth len' l default)) in H.
        apply (f_equal (fun l => Znth len' l default)) in H1.
        apply (f_equal (fun l => Znth len' l default)) in H0.
        rewrite app_Znth1 in H, H1; try lia.
        subst len'.
        rewrite (Znth_Zsublist_single default) in H0.
        rewrite <- H0. rewrite H1. rewrite H.
        reflexivity. }
      rewrite <- H6.
      auto. 
Qed.

Lemma list_lex_gt_ex_trans' (cmp_fn : A -> A -> comparison):
  Cmp cmp_fn ->
  forall l1 l2 l3,
    list_lex_gt cmp_fn l1 l2 ->
    list_lex_gt_ex cmp_fn l2 l3 ->
    list_lex_gt_ex cmp_fn l1 l3.
Proof.
  intros Cmpfn. intros.
  destruct H.
  - apply (list_lex_gt_ex_trans _ _ l1 l2 l3); auto.
  - destruct H as [[l4 ?] ?].
    destruct H0 as [p [x [y [l2' [l3' ?]]]]].
    destruct H0 as [? [? ?]].
    unfold list_lex_gt_ex.
    exists p. exists x. exists y.
    exists (l2' ++ l4). exists l3'.
    split; [|split].
    + rewrite H0 in H.
      rewrite <- app_assoc in H.
      simpl in H. auto.
    + auto.
    + auto.
Qed.

Lemma list_lex_gt_trans (cmp_fn : A -> A -> comparison):
  Cmp cmp_fn ->
  forall l1 l2 l3,
    list_lex_gt cmp_fn l1 l2 ->
    list_lex_gt cmp_fn l2 l3 ->
    list_lex_gt cmp_fn l1 l3.
Proof.
  intros Cmpfn. intros.
  destruct H0.
  - left. apply (list_lex_gt_ex_trans' _ _ l1 l2 l3); auto.
  - destruct H0 as [[l4 ?] ?].
    destruct H.
    + destruct H as [p [x [y [l1' [l2' ?]]]]].
      destruct H as [? [? ?]].
      set (len := Zlength p).
      pose proof Zlength_nonneg p.
      destruct (Z.lt_trichotomy len (Zlength l3)) as [Hlt | [Heq | Hgt]].
      * left. unfold list_lex_gt_ex.
        exists p. exists x. exists y.
        exists l1'. exists (sublist (len + 1) (Zlength l3) l3).
        split; [|split]; try auto.
        rewrite H0 in H2.
        apply (f_equal (fun l => sublist 0 (len + 1) l)) in H2.
        rewrite sublist_split_app_l in H2; try lia.
        rewrite (sublist_split _ _ len (p ++ y :: l2')) in H2; try lia.
        2:{ rewrite Zlength_app. rewrite Zlength_cons. 
            pose proof Zlength_nonneg l2'. lia. }
        subst len.
        rewrite sublist_app_exact1 in H2.
        rewrite (sublist_single default) in H2.
        2:{ rewrite Zlength_app. rewrite Zlength_cons. 
            pose proof Zlength_nonneg l2'. lia. }
        rewrite Znth_Zsublist_single in H2.
        rewrite <- (Zsublist_all l3) at 1.
        rewrite (sublist_split _ _ (Zlength p + 1) l3) at 1; try lia.
        rewrite H2. rewrite <- app_assoc. simpl.
        reflexivity.
      * assert (p = l3).
        { rewrite H0 in H2.
          apply (f_equal (fun l => sublist 0 len l)) in H2.
          rewrite Heq in H2 at 1. unfold len in H2.
          repeat rewrite sublist_app_exact1 in H2.
          auto. }
        subst l3. right. split.
        1:{ exists (x :: l1'). auto. }
        rewrite H. rewrite Zlength_app.
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l1'.
        lia.
      * pose proof Zlength_nonneg l3.
        assert (l3 = sublist 0 (Zlength l3) l1).
        { apply (f_equal (fun l => sublist 0 (Zlength l3) l)) in H.
          apply (f_equal (fun l => sublist 0 (Zlength l3) l)) in H2.
          apply (f_equal (fun l => sublist 0 (Zlength l3) l)) in H0.
          subst len.
          rewrite sublist_split_app_l in H; try lia.
          rewrite sublist_split_app_l in H2; try lia.
          rewrite sublist_app_exact1 in H0; try lia.
          rewrite H. rewrite <- H2. rewrite H0.
          reflexivity. }
        assert (len < Zlength l1).
        { apply (f_equal (fun l => Zlength l)) in H.
          rewrite Zlength_app in H. rewrite Zlength_cons in H.
          pose proof Zlength_nonneg l1'. lia. }
        right. split.
        1:{ exists (sublist (Zlength l3) (Zlength l1) l1).
            rewrite H6 at 1.
            rewrite <- (Zsublist_all l1) at 1.
            rewrite (sublist_split _ _ (Zlength l3)); try lia.
            reflexivity. }
        lia.
    + destruct H as [[l5 ?] ?].
      right. split.
      * exists (l4 ++ l5).
        rewrite H. rewrite H0.
        rewrite <- app_assoc.
        reflexivity.
      * lia.
Qed.

Lemma list_lex_gt_ex_plus (cmp_fn :A -> A -> comparison) (l1' l2' l1 l2 : list A):
  Cmp cmp_fn ->
  is_prefix l1' l1 ->
  is_prefix l2' l2 ->
  list_lex_gt_ex cmp_fn l1' l2' ->
  list_lex_gt_ex cmp_fn l1 l2.
Proof. 
  intros Cmpfn. intros.
  destruct H as [l1s ?].
  destruct H0 as [l2s ?].
  unfold list_lex_gt_ex in *.
  destruct H1 as [p [x [y [l1xs [l2ys ?]]]]].
  destruct H1 as [? [? ?]].
  exists p. exists x. exists y.
  exists (l1xs ++ l1s). exists (l2ys ++ l2s).
  split; [|split].
  - rewrite H. rewrite H1.
    rewrite <- app_assoc. simpl.
    reflexivity.
  - rewrite H0. rewrite H2.
    rewrite <- app_assoc. simpl.
    reflexivity.
  - auto.
Qed.

Lemma list_lex_ge_param_prefix (cmp_fn :A -> A -> comparison) (l1 l2 p : list A): 
  list_lex_ge cmp_fn l1 l2 ->
  list_lex_ge cmp_fn (p ++ l1) (p ++ l2).
Proof.
  unfold list_lex_ge. intros.
  destruct H; [left|right].
  2:{ rewrite H. easy. }
  unfold list_lex_gt in *.
  destruct H; [left|right].
  2:{ unfold is_proper_prefix in *.
      unfold is_prefix in *.
      destruct H as [[l3 H] ?].
      split.
      - exists l3. 
        rewrite <- app_assoc.
        rewrite H. easy.
      - repeat rewrite Zlength_app. lia. }
  unfold list_lex_gt_ex in *.
  destruct H as [p' [x [y [l1' [l2' H]]]]].
  destruct H as [H1 [H2 H]].
  exists (p ++ p'). exists x. exists y.
  exists l1'. exists l2'.
  split; [|split].
  - rewrite H1. rewrite <- app_assoc.
    reflexivity.
  - rewrite H2. rewrite <- app_assoc.
    reflexivity.
  - apply H.
Qed.

Lemma list_lex_ge_param_prefix_inv (cmp_fn :A -> A -> comparison) (l1 l2 p : list A):
  Cmp cmp_fn ->
  list_lex_ge cmp_fn (p ++ l1) (p ++ l2) ->
  list_lex_ge cmp_fn l1 l2.
Proof.
  intros Cmpfn. intros.
  destruct H; [left|right].
  2:{ apply app_inv_head in H. rewrite H. easy. }
  unfold list_lex_gt in *.
  destruct H; [left|right].
  2:{ unfold is_proper_prefix in *.
      destruct H. unfold is_prefix in *.
      destruct H as [l3 H].
      split.
      - exists l3.
        rewrite <- app_assoc in H. 
        apply app_inv_head in H.
        auto.
      - repeat rewrite Zlength_app in H0.
        lia. }
  unfold list_lex_gt_ex in *.
  destruct H as [p' [x [y [l1' [l2' ?]]]]].
  destruct H as [? [? ?]].
  set (len := Zlength p).
  assert (len <= Zlength p').
  { assert (len > Zlength p' \/ len <= Zlength p') by lia.
    destruct H2; [| auto].
    pose proof Zlength_nonneg p'.
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H.
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H0.
    subst len.
    rewrite app_Znth1 in H; try lia.
    rewrite app_Znth2 in H; try lia.
    rewrite app_Znth1 in H0; try lia.
    rewrite app_Znth2 in H0; try lia.
    rewrite H0 in H.
    replace (Zlength p' - Zlength p') with 0 in H by lia.
    repeat rewrite Znth0_cons in H.
    rewrite H in H1. rewrite cmp_refl in H1.
    discriminate. }
  apply (f_equal (fun l => sublist len (Zlength l) l)) in H.
  apply (f_equal (fun l => sublist len (Zlength l) l)) in H0.
  subst len.
  rewrite Zsublist_app_exact2 in H.
  2:{ rewrite Zlength_app. reflexivity. }
  rewrite Zsublist_app_exact2 in H0.
  2:{ rewrite Zlength_app. reflexivity. }
  set (p0 := sublist 0 (Zlength p' - Zlength p) l1).
  exists p0. exists x. exists y.
  exists l1'. exists l2'.
  pose proof Zlength_nonneg p.
  pose proof Zlength_nonneg p'.
  split; [|split]; subst p0.
  - rewrite H.
    rewrite Zsublist_Zsublist; try lia.
    2:{ rewrite Zlength_app. 
        pose proof Zlength_nonneg (x :: l1'). 
        lia. }
    simpl.
    replace (Zlength p' - Zlength p + Zlength p) with (Zlength p') by lia.
    replace (x :: l1') with (sublist (Zlength p') 
            (Zlength (p' ++ x :: l1')) (p' ++ x :: l1')) at 4.
    2:{ rewrite Zsublist_app_exact2; try auto.
        rewrite Zlength_app. reflexivity. }
    rewrite <- sublist_split; try lia.
    2:{ rewrite Zlength_app.
        pose proof Zlength_nonneg (x :: l1').
        lia. }
    reflexivity.
  - rewrite H0. rewrite H.
    rewrite Zsublist_Zsublist; try lia.
    2:{ rewrite Zlength_app.
        pose proof Zlength_nonneg (x :: l1').
        lia. }
    simpl.
    replace (Zlength p' - Zlength p + Zlength p) with (Zlength p') by lia.
    rewrite (sublist_split _ _ (Zlength p') (p' ++ y :: l2')); try lia.
    2:{ rewrite Zlength_app.
        pose proof Zlength_nonneg (y :: l2').
        lia. }
    rewrite Zsublist_app_exact2.
    2:{ rewrite Zlength_app. reflexivity. }
    rewrite sublist_split_app_l; try lia.
    rewrite sublist_split_app_l; try lia.
    reflexivity.
  - auto.
Qed.

Lemma list_lex_ge_param_assym (cmp_fn : A -> A -> comparison) (l1 l2 : list A):
  Cmp cmp_fn ->
  list_lex_ge cmp_fn l1 l2 ->
  list_lex_ge cmp_fn l2 l1 ->
  l1 = l2.
Proof.
  intros Cmpfn. intros.
  unfold list_lex_ge in *.
  destruct H; destruct H0; [|easy |easy |easy].
  unfold list_lex_gt in *.
  destruct H; destruct H0.
  - unfold list_lex_gt_ex in *.
    destruct H as [p [x [y [l1' [l2' ?]]]]].
    destruct H as [? [? ?]].
    destruct H0 as [p' [x' [y' [l1'' [l2'' ?]]]]].
    destruct H0 as [? [? ?]].
    set (len := Zlength p).
    set (len' := Zlength p').
    pose proof Zlength_nonneg p.
    pose proof Zlength_nonneg p'.
    destruct (Z.lt_trichotomy len len') as [Hlt | [Heq | Hgt]].
    + apply (f_equal (fun l => Znth len l default)) in H.
      apply (f_equal (fun l => Znth len l default)) in H1.
      apply (f_equal (fun l => Znth len l default)) in H0.
      apply (f_equal (fun l => Znth len l default)) in H3.
      subst len len'.
      rewrite Znth_Zsublist_single in H, H1; try lia.
      rewrite app_Znth1 in H0, H3; try lia.
      rewrite H0 in H1. rewrite <- H3 in H1. rewrite H in H1.
      rewrite H1 in H2. rewrite cmp_refl in H2.
      discriminate.
    + apply (f_equal (fun l => Znth len l default)) in H.
      apply (f_equal (fun l => Znth len l default)) in H1.
      apply (f_equal (fun l => Znth len l default)) in H0.
      apply (f_equal (fun l => Znth len l default)) in H3.
      subst len len'. rewrite Heq in H0, H3.
      rewrite Znth_Zsublist_single in *.
      rewrite Heq in H. rewrite H3 in H.
      rewrite Heq in H1. rewrite H0 in H1.
      rewrite <- H in H2.
      rewrite H1 in H4.
      apply cmp_Gt_Lt in H4.
      rewrite H4 in H2.
      discriminate.
    + apply (f_equal (fun l => Znth len' l default)) in H.
      apply (f_equal (fun l => Znth len' l default)) in H1.
      apply (f_equal (fun l => Znth len' l default)) in H0.
      apply (f_equal (fun l => Znth len' l default)) in H3.
      subst len len'.
      rewrite Znth_Zsublist_single in H0, H3; try lia.
      rewrite app_Znth1 in H, H1; try lia.
      rewrite H0 in H1. rewrite H3 in H. rewrite <- H in H1.
      rewrite H1 in H4. rewrite cmp_refl in H4.
      discriminate.
  - pose proof proper_prefix_discriminate_gt_ex' _ _ _ Cmpfn H H0.
    tauto.
  - pose proof proper_prefix_discriminate_gt_ex' _ _ _ Cmpfn H0 H.
    tauto.
  - destruct H as [[l1' ?] ?].
    destruct H0 as [[l2' ?] ?].
    rewrite H0 in H.
    rewrite <- app_assoc in H.
    rewrite <- (app_nil_r l1) in H at 1.
    apply app_inv_head in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H. subst l1' l2'.
    rewrite app_nil_r in H0.
    rewrite H0. easy.
Qed.

End list_lex_cmp.

Section list_lex_lemma.

Lemma prefix_ordering (w w' : list A):
    list_lex_ge cmp w w' ->
    list_lex_ge cmp_rev w w' ->
    is_prefix w' w.
Proof.
  intros Hcmp Hcmp_rev.
  destruct Hcmp as [Hcmp|Hcmp].
  2:{ rewrite Hcmp. apply is_prefix_refl. }
  destruct Hcmp_rev as [Hcmp_rev|Hcmp_rev].
  2:{ rewrite Hcmp_rev. apply is_prefix_refl. }
  destruct Hcmp as [Hcmp|Hcmp].
  2:{ destruct Hcmp. auto. }
  destruct Hcmp_rev as [Hcmp_rev|Hcmp_rev].
  2:{ destruct Hcmp_rev. auto. }
  unfold list_lex_gt_ex in Hcmp.
  unfold list_lex_gt_ex in Hcmp_rev.
  destruct Hcmp as [p [x [y [l1 [l2 Hcmp]]]]].
  destruct Hcmp as [H1 [H2 Hcmp]].
  destruct Hcmp_rev as [p' [x' [y' [l1' [l2' Hcmp_rev]]]]].
  destruct Hcmp_rev as [H1' [H2' Hcmp_rev]].
  destruct (Z.lt_trichotomy (Zlength p) (Zlength p')) as [Hlt|[Heq|Hgt]].
  - apply (f_equal (fun l => sublist 0 (Zlength p') l)) in H1.
    apply (f_equal (fun l => sublist 0 (Zlength p') l)) in H2.
    rewrite H1' in H1. rewrite H2' in H2.
    rewrite sublist_app_exact1 in H1.
    rewrite sublist_app_exact1 in H2.
    assert (sublist 0 (Zlength p') (p ++ x :: l1) 
          = sublist 0 (Zlength p') (p ++ y :: l2)).
    { rewrite <- H1. rewrite <- H2. reflexivity. }
    apply (f_equal (fun l => Znth (Zlength p) l default)) in H.
    rewrite Znth_sublist in H; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    rewrite Znth_sublist in H; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    replace (Zlength p + 0) with (Zlength p) in H by lia.
    rewrite Znth_Zsublist_single in H.
    rewrite Znth_Zsublist_single in H.
    assert (cmp x y = Eq).
    { rewrite H. apply cmp_refl. }
    rewrite Hcmp in H0. discriminate.
  - apply (f_equal (fun l => Znth (Zlength p) l default)) in H1.
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H1'.
    rewrite Znth_Zsublist_single in H1.
    rewrite Znth_Zsublist_single in H1'.
    rewrite Heq in H1.
    rewrite H1 in H1'.
    apply (f_equal (fun l => Znth (Zlength p) l default)) in H2.
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H2'.
    rewrite Znth_Zsublist_single in H2.
    rewrite Znth_Zsublist_single in H2'.
    rewrite Heq in H2.
    rewrite H2 in H2'.
    rewrite H1' in Hcmp. rewrite H2' in Hcmp.
    unfold cmp_rev in Hcmp_rev.
    destruct (cmp x' y'); try discriminate.
  - apply (f_equal (fun l => sublist 0 (Zlength p) l)) in H1'.
    apply (f_equal (fun l => sublist 0 (Zlength p) l)) in H2'.
    rewrite H1 in H1'. rewrite H2 in H2'.
    rewrite sublist_app_exact1 in H1'.
    rewrite sublist_app_exact1 in H2'.
    assert (sublist 0 (Zlength p) (p' ++ x' :: l1') 
          = sublist 0 (Zlength p) (p' ++ y' :: l2')).
    { rewrite <- H1'. rewrite <- H2'. reflexivity. }
    apply (f_equal (fun l => Znth (Zlength p') l default)) in H.
    rewrite Znth_sublist in H; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    rewrite Znth_sublist in H; try lia.
    2:{ split; [ apply Zlength_nonneg | lia]. }
    replace (Zlength p' + 0) with (Zlength p') in H by lia.
    rewrite Znth_Zsublist_single in H.
    rewrite Znth_Zsublist_single in H.
    assert (cmp x' y' = Eq).
    { rewrite H. apply cmp_refl. }
    unfold cmp_rev in Hcmp_rev.
    destruct (cmp x' y'); try discriminate.
Qed.

End list_lex_lemma.
End LexCompare.

Section Period.

(* MARK: Relation between the period definition and the sequence length *)
Definition is_period {A : Type} (default : A) (l : list A) (p : Z) : Prop :=
  0 < p /\
  (forall (i : Z),
    0 <= i -> (* Note: switching to Z requires stricter range constraints *)
    i + p < Zlength l ->
    Znth i l default = Znth (i + p) l default).

Lemma is_period_ext {A : Type} (default : A) (p q i j: Z) (l : list A): 
  is_period default l p ->
  0 <= q -> (* Note *)
  0 <= i ->
  j = i + q * p ->
  j < Zlength l ->
  Znth i l default = Znth j l default.
Proof.
  intros.
  destruct H.
  subst j.
  set (nq := Z.to_nat q).
  replace q with (Z.of_nat nq) in * by lia.
  induction nq.
  - simpl.
    replace (i + 0) with i by lia.
    reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (i + Z.succ (Z.of_nat nq) * p) with
            (i + Z.of_nat nq * p + p) by lia.
    pose proof H4 (i + Z.of_nat nq * p).
    assert (0 <= i + Z.of_nat nq * p) by lia.
    assert (i + Z.of_nat nq * p + p < Zlength l) by lia.
    pose proof H2 H5 H6.
    rewrite <- H7.
    apply IHnq; try lia.
Qed.

Lemma periodic_segment' {A : Type} (default : A) (l : list A) (p q lo hi lo' hi' : Z): 
  is_period default l p ->
  (0 <= q) ->
  (0 <= lo) ->
  (lo <= hi <= Zlength l) ->
  (lo' <= hi' <= Zlength l) ->
  (lo' = lo + q * p) ->
  (hi - lo = hi' - lo') ->
  (sublist lo hi l = sublist lo' hi' l).
Proof.
  intros. destruct H.
  rewrite (list_eq_ext _ _ default).
  split.
  - repeat rewrite Zlength_sublist; try lia.
  - intros. rewrite Zlength_sublist in H7; try lia.
    repeat rewrite Znth_sublist; try lia.
    rewrite H4.
    apply (is_period_ext default p q); try lia.
    split; auto.
Qed.

Definition is_minimal_period {A : Type} (default : A) (l : list A) (p : Z) : Prop :=
  is_period default l p /\ 
    forall (p' : Z), is_period default l p' -> p' >= p.

Lemma minimal_period_le_Zlength {A : Type} (default : A) (l : list A) (p : Z):
  l <> nil ->
  is_minimal_period default l p ->
  p <= Zlength l.
Proof.
  intros.
  destruct H0.
  assert (is_period default l (Zlength l)).
  { unfold is_period.
    split.
    - pose proof Zlength_nonneg l.
      assert (0 < Zlength l \/ Zlength l = 0) by lia.
      destruct H3; [auto|].
      apply Zlength_zero_iff_nil in H3. contradiction.
    - intros. lia. }
  specialize (H1 (Zlength l) H2).
  lia.
Qed.

Definition border {A : Type} (l l1 : list A) : Prop :=
  is_prefix l1 l /\ is_suffix l1 l.

(* Specialized version of max_border_min_period *)
Lemma max_border_min_period_spec_1 {A : Type} (default : A) (l l1 : list A): 
  is_prefix l1 l ->
  is_suffix l1 l ->
  Zlength l1 + 1 = Zlength l ->
  is_period default l 1.
Proof.
  intros. unfold is_period.
  assert (0 <= Zlength l1 /\ 0 <= Zlength l).
  { split; apply Zlength_nonneg. } destruct H2.
  split; [lia|]. intros.
  replace l with (sublist 0 (Zlength l) l) in H, H0.
  2:{ apply Zsublist_all. }
  apply Zsublist_suffix_inv in H0; try lia.
  apply Zsublist_prefix_inv in H; try lia.
  replace (Zlength l - Zlength l1) with 1 in H0 by lia.
  replace (0 + Zlength l1) with (Zlength l - 1) in H by lia.
  assert (sublist 0 (Zlength l - 1) l = sublist 1 (Zlength l) l).
  { rewrite <- H. rewrite <- H0. reflexivity. }
  apply (f_equal (fun l => Znth i l default)) in H6.
  rewrite Znth_sublist in H6; try lia.
  rewrite Znth_sublist in H6; try lia.
  replace (i + 0) with i in H6 by lia.
  apply H6.
Qed.

Lemma prefix_contains_period {A : Type} (default : A) (l1 l : list A) (p : Z): 
  is_prefix l1 l ->
  is_period default l p ->
  is_period default l1 p.
Proof.
  unfold is_period. intros.
  destruct H0.
  rewrite <- (Zsublist_all l) in H.
  pose proof H as H'.
  apply Zsublist_prefix_inv in H.
  2:{ split; [split|]; try lia. apply Zlength_nonneg. }
  split; [auto|]. 
  rewrite H. rewrite Zlength_sublist.
  2:{ split.
      - pose proof Zlength_nonneg l1. lia.
      - apply Zsublist_prefix_range in H'; try lia.
        split; [split|]; try lia. apply Zlength_nonneg. }
  intros. rewrite Znth_sublist; try lia.
  rewrite Znth_sublist; try lia.
  repeat rewrite Z.add_0_r.
  apply Zsublist_prefix_range in H'.
  2:{ split; [split|]; try lia. apply Zlength_nonneg. }
  apply H1; try lia.
Qed.

Lemma suffix_contains_period {A : Type} (default : A) (l l1 : list A) (p: Z):
  is_suffix l1 l ->
  is_period default l p ->
  is_period default l1 p.
Proof.
  unfold is_suffix. intros.
  destruct H0.
  rewrite <- (Zsublist_all l) in H.
  pose proof H as H'.
  apply Zsublist_suffix_inv in H.
  2:{ split; [split|]; try lia. apply Zlength_nonneg. }
  split; [auto|]. 
  rewrite H. 
  pose proof Zlength_nonneg l.
  pose proof Zlength_nonneg l1.
  apply Zsublist_suffix_range in H'; try lia.
  rewrite Zlength_sublist; try lia.
  intros.
  rewrite Znth_sublist; try lia.
  rewrite Znth_sublist; try lia.
  specialize (H1 (i + (Zlength l - Zlength l1)) ltac:(lia) ltac:(lia)).
  replace (i + p + (Zlength l - Zlength l1)) with (i + (Zlength l - Zlength l1) + p) by lia.
  apply H1.
Qed.

(* Design note: this is about sublist containment, not prefix/suffix *)
Lemma suffix_less_period {A : Type} (default : A) (l1 l2 : list A) (p1 p2 : Z):
  is_suffix l2 l1 ->
  is_minimal_period default l1 p1 ->
  is_minimal_period default l2 p2 ->
  p2 <= p1.
Proof.
  intros.
  destruct H0. destruct H1.
  pose proof Zlength_nonneg l1.
  pose proof Zlength_nonneg l2.
  assert (is_period default l2 p1).
  { destruct H0.
    unfold is_period.
    split; [lia|]; intros.
    rewrite <- (Zsublist_all l1) in H.
    pose proof H as H'.
    apply Zsublist_suffix_inv in H; try lia.
    apply Zsublist_suffix_range in H'; try lia.
    specialize (H6 (i + Zlength l1 - Zlength l2) ltac:(lia) ltac:(lia)).
    rewrite H.
    repeat rewrite Znth_sublist; try lia.
    replace (i + (Zlength l1 - Zlength l2)) with (i + Zlength l1 - Zlength l2) by lia.
    replace (i + p1 + (Zlength l1 - Zlength l2)) with (i + Zlength l1 - Zlength l2 + p1) by lia.
    apply H6.
  }
  specialize (H3 p1 H6).
  lia.
Qed.

Lemma is_period_spec_repeat_twice {A : Type} (default : A) (l : list A) (p : Z): 
  0 < p ->
  p = Zlength l ->
  is_period default (l ++ l) p.
Proof.
  intros.
  unfold is_period.
  split; [lia|].
  intros.
  rewrite Zlength_app in H2.
  rewrite app_Znth1; try lia.
  rewrite app_Znth2; try lia.
  replace (i + p - Zlength l) with i by lia.
  reflexivity.
Qed.

Lemma is_period_spec_repeat_prefix {A : Type} (default : A) (u v z z': list A) (p : Z):
  0 < p ->
  p = Zlength (z ++ u) ->
  v = z ++ u ++ z' ->
  is_prefix z' v ->
  is_period default (u ++ v) p.
Proof.
  intros.
  unfold is_period.
  split;[lia|].
  intros i Hi Hip.
  assert (i < Zlength u \/ Zlength u <= i) by lia.
  destruct H3.
  - rewrite app_Znth1; try lia.
    rewrite app_Znth2; try lia.
    2:{ rewrite H0. rewrite Zlength_app.
        pose proof Zlength_nonneg z. lia. }
    rewrite H1.
    replace (i + p - Zlength u) with (i + Zlength z) by (rewrite H0, Zlength_app; lia).
    rewrite app_Znth2; try lia.
    rewrite app_Znth1; try lia.
    replace (i + Zlength z - Zlength z) with i by lia.
    reflexivity.
  - set (j := i - Zlength u).
    rewrite app_Znth2; try lia.
    rewrite app_Znth2; try lia.
    replace (i + p - Zlength u) with (j + p) by (subst j; lia).
    rewrite Zlength_app in Hip.
    assert (j + p < Zlength v) by (subst j; lia).
    destruct H2 as [w Hw].
    assert (p = Zlength v - Zlength z') by (rewrite H0, H1; repeat rewrite Zlength_app; lia).
    replace v with (z' ++ w) in *.
    assert (j < Zlength z') by lia.
    rewrite app_Znth1; try lia.
    rewrite H1.
    rewrite app_Znth2; try lia.
    2:{ rewrite H0. rewrite Zlength_app.
        pose proof Zlength_nonneg u. lia. }
    replace (j + p - Zlength z) with (j + Zlength u).
    2:{ rewrite H0. rewrite Zlength_app. lia. }
    rewrite app_Znth2; try lia.
    replace (j + Zlength u - Zlength u) with j by lia.
    unfold j. reflexivity.
Qed.


End Period.
