(** * Positional list facts

    Facts about [Znth], [sublist] and [replace_Znth] lists that the vector
    library ([dynvec_lib]) and its clients share, and two operations on them:
    [first_occurrence] and [remove_nth].  Nothing here is about vectors or
    separation logic; the facts are polymorphic in the element type. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list.

Lemma Znth_split : forall {A : Type} (d : A) (xs : list A) i,
  0 <= i < Zlength xs ->
  xs = sublist 0 i xs ++ Znth i xs d :: sublist (i + 1) (Zlength xs) xs.
Proof.
  intros A d xs i Hi.
  rewrite <- (sublist_self xs (Zlength xs) eq_refl) at 1.
  rewrite (sublist_split 0 (Zlength xs) i xs) by lia.
  rewrite (sublist_split i (Zlength xs) (i + 1) xs) by lia.
  rewrite (sublist_single d i xs) by lia. reflexivity.
Qed.

(** [sublist lo hi l] split around an interior index [a]. *)
Lemma sublist_Znth_mid : forall {A : Type} (d : A) lo a hi (l : list A),
  0 <= lo <= a -> a < hi <= Zlength l ->
  sublist lo hi l = sublist lo a l ++ Znth a l d :: sublist (a + 1) hi l.
Proof.
  intros A d lo a hi l Hlo Hhi.
  rewrite (sublist_split lo hi a) by lia.
  rewrite (sublist_split a hi (a + 1)) by lia.
  rewrite (sublist_single d a l) by lia.
  reflexivity.
Qed.

Lemma replace_Znth_split : forall {A : Type} k (w : A) (l : list A),
  0 <= k < Zlength l ->
  replace_Znth k w l = sublist 0 k l ++ w :: sublist (k + 1) (Zlength l) l.
Proof.
  intros A k w l Hk.
  destruct l as [|x l']; [rewrite Zlength_nil in Hk; lia|].
  rewrite (Znth_split x (x :: l') k Hk) at 1.
  rewrite replace_Znth_app_r by (rewrite Zlength_sublist by lia; lia).
  rewrite replace_Znth_nothing by (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia. replace (k - (k - 0)) with 0 by lia.
  reflexivity.
Qed.

Lemma sublist_replace_Znth_outside : forall {A : Type} k (w : A) (l : list A) lo hi,
  0 <= k < Zlength l -> 0 <= lo <= hi -> hi <= Zlength l ->
  (hi <= k \/ k < lo) ->
  sublist lo hi (replace_Znth k w l) = sublist lo hi l.
Proof.
  intros A k w l lo hi Hk Hlo Hhi Hout.
  rewrite replace_Znth_split by lia.
  destruct Hout as [Hbefore | Hafter].
  - rewrite sublist_split_app_l by (rewrite ?Zlength_sublist by lia; lia).
    apply Zsublist_Zsublist0; lia.
  - replace (sublist 0 k l ++ w :: sublist (k + 1) (Zlength l) l)
      with ((sublist 0 k l ++ [w]) ++ sublist (k + 1) (Zlength l) l)
      by (rewrite <- app_assoc; reflexivity).
    rewrite (sublist_split_app_r lo hi (k + 1) (sublist 0 k l ++ [w]) (sublist (k + 1) (Zlength l) l))
      by (rewrite ?Zlength_app, ?Zlength_sublist, ?Zlength_cons, ?Zlength_nil by lia; lia).
    rewrite Zsublist_Zsublist by lia.
    f_equal; lia.
Qed.

Lemma replace_Znth_comm : forall {A : Type} i j (wi wj : A) (l : list A),
  0 <= i < Zlength l -> 0 <= j < Zlength l -> i <> j ->
  replace_Znth i wi (replace_Znth j wj l) = replace_Znth j wj (replace_Znth i wi l).
Proof.
  intros A i j wi wj l Hi Hj Hne.
  apply (proj2 (list_eq_ext _ _ wi)).
  split; [rewrite !Zlength_replace_Znth; reflexivity|].
  intros k Hk. rewrite !Zlength_replace_Znth in Hk.
  assert (Hl : forall m (v : A), Zlength (replace_Znth m v l) = Zlength l)
    by (intros; apply Zlength_replace_Znth).
  destruct (Z.eq_dec k i) as [Hki|Hki].
  - subst k.
    rewrite (Znth_replace_Znth_Same wi (replace_Znth j wj l)) by (rewrite Hl; lia).
    rewrite (Znth_replace_Znth_Diff wi (replace_Znth i wi l) j i) by (rewrite ?Hl; lia).
    rewrite (Znth_replace_Znth_Same wi l) by lia. reflexivity.
  - destruct (Z.eq_dec k j) as [Hkj|Hkj].
    + subst k.
      rewrite (Znth_replace_Znth_Diff wi (replace_Znth j wj l) i j) by (rewrite ?Hl; lia).
      rewrite (Znth_replace_Znth_Same wi l) by lia.
      rewrite (Znth_replace_Znth_Same wi (replace_Znth i wi l)) by (rewrite Hl; lia).
      reflexivity.
    + rewrite (Znth_replace_Znth_Diff wi (replace_Znth j wj l) i k) by (rewrite ?Hl; lia).
      rewrite (Znth_replace_Znth_Diff wi l j k) by lia.
      rewrite (Znth_replace_Znth_Diff wi (replace_Znth i wi l) j k) by (rewrite ?Hl; lia).
      rewrite (Znth_replace_Znth_Diff wi l i k) by lia. reflexivity.
Qed.

Lemma sublist_snoc : forall {A : Type} (d : A) (l : list A) lo hi,
  0 <= lo <= hi -> hi < Zlength l ->
  sublist lo (hi + 1) l = sublist lo hi l ++ [Znth hi l d].
Proof.
  intros A d l lo hi Hlo Hhi.
  rewrite (sublist_split lo (hi + 1) hi l) by lia.
  rewrite (sublist_single d hi l) by lia. reflexivity.
Qed.

Lemma sublist_suffix_cons : forall {A : Type} (d : A) (l : list A) i,
  0 <= i < Zlength l ->
  sublist i (Zlength l) l = Znth i l d :: sublist (i + 1) (Zlength l) l.
Proof.
  intros A d l i Hi.
  rewrite (sublist_split i (Zlength l) (i + 1) l) by lia.
  rewrite (sublist_single d i l) by lia. reflexivity.
Qed.

(** [k] is the index of the first occurrence of [e] in [l]. *)
Definition first_occurrence {A : Type} (e : A) (l : list A) (k : Z) : Prop :=
  0 <= k < Zlength l /\
  Znth k l e = e /\
  Forall (fun x => x <> e) (sublist 0 k l).

(** [l] without its [k]-th element. *)
Definition remove_nth {A : Type} (k : Z) (l : list A) : list A :=
  sublist 0 k l ++ sublist (k + 1) (Zlength l) l.

(** Removing the first occurrence of [e] leaves a permutation of the rest. *)
Lemma first_occurrence_perm : forall {A : Type} (e : A) (l : list A) found,
    first_occurrence e l found ->
    Permutation l (e :: remove_nth found l).
Proof.
  intros A e l found [Hrange [He _]].
  unfold remove_nth. assert (Hwhole :
    l = sublist 0 found l ++
        Znth found l e :: sublist (found + 1) (Zlength l) l).
  {
    pose proof (sublist_split 0 (Zlength l) found l ltac:(lia) ltac:(lia)) as H1.
    pose proof
      (sublist_split found (Zlength l) (found + 1) l ltac:(lia) ltac:(lia))
      as H2.
    rewrite sublist_self in H1 by lia.
    rewrite (sublist_single e found l) in H2 by lia.
    rewrite H2 in H1. exact H1.
  }
  rewrite Hwhole at 1. rewrite He.
  apply Permutation_sym. apply Permutation_middle.
Qed.
