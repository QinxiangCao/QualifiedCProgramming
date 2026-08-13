
Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Local Open Scope Z.

Definition Znth {A: Type} (n: Z) (l: list A) (a: A): A := 
    nth (Z.to_nat n) l a.

Definition Znth_error {A: Type} (l: list A) (n: Z): option A :=
  if Z_le_gt_dec 0 n
  then nth_error l (Z.to_nat n)
  else None.

Definition tl_error {A: Type}(l: list A): option A := 
    nth_error l (length l - 1).

Fixpoint replace_nth {A: Type} (n: nat) (l: list A) (a: A) {struct l} :=
    match l, n with
    | [], _ => []
    | _ :: t, O => a :: t
    | h :: t, S n => h :: replace_nth n t a
    end.

Definition replace_Znth {A: Type} (n: Z) (a: A) (l: list A): list A :=
  replace_nth (Z.to_nat n) l a.

Definition Nsublist {A: Type} (lo hi: nat) (l: list A): list A :=
  skipn lo (firstn hi l).

Definition sublist {A: Type} (lo hi: Z) (l: list A): list A :=
  skipn (Z.to_nat lo) (firstn (Z.to_nat hi) l).


Section Index. 

Context {A: Type}
        (d: A).

(* Znth *)

Lemma Znth0_cons: forall a l,
  Znth 0 (a :: l) d = a.
Proof.
  intros.
  unfold Znth.
  simpl.
  reflexivity.
Qed.

Lemma Znth_cons: forall n a l,
  n > 0 ->
  Znth n (a :: l) d = Znth (n - 1) l d.
Proof.
  intros.
  unfold Znth.
  assert (Z.to_nat n = S (Z.to_nat (n - 1))) by lia.
  rewrite H0.
  simpl.
  reflexivity.
Qed.

Lemma Znth_error_cons_0:
  forall (x: A) (l: list A),
    Znth_error (x :: l) 0 = Some x.
Proof.
  intros.
  apply nth_error_cons_0.
Qed.

Lemma Znth_error_cons:
  forall (m n: Z) {A: Type} (x: A) (l: list A),
    n <> 0 ->
    n = m + 1 ->
    Znth_error (x :: l) n = Znth_error l m.
Proof.
  intros.
  subst.
  unfold Znth_error.
  destruct (Z_le_gt_dec 0 (m + 1)).
  + destruct (Z_le_gt_dec 0 m); try lia.
    rewrite Z2Nat.inj_add by lia.
    replace (Z.to_nat m + Z.to_nat 1)%nat with (S (Z.to_nat m)) by lia.
    simpl.
    reflexivity.
  + destruct (Z_le_gt_dec 0 m); try lia.
    reflexivity.
Qed.

Lemma Znth_repeat : forall {A} (d: A) (n: nat) (i: Z),
  Znth i (repeat d n) d = d.
Proof.
  intros.
  unfold Znth.
  rewrite nth_repeat.
  reflexivity.
Qed.

Lemma Znth_repeat_lt : forall {A} (a: A) (n: nat) (i: Z) (d : A),
  0 <= i < Z.of_nat n ->
  Znth i (repeat d n) a = d.
Proof.
  intros.
  unfold Znth.
  rewrite nth_repeat_lt ; try lia.
  auto.
Qed.

(* replace_Znth *)

Lemma replace_Znth_cons: forall n (a b: A) l,
  n > 0 ->
  replace_Znth n a (b :: l) =
  b :: replace_Znth (n - 1) a l.
Proof.
  intros.
  unfold replace_Znth.
  assert (Z.to_nat n = S (Z.to_nat (n - 1))) by lia.
  rewrite H0.
  simpl.
  reflexivity.
Qed.


Lemma replace_Znth_Znth: forall n l (a0: A),
  replace_Znth n (Znth n l a0) l = l.
Proof.
  intros.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat n); clearbody m; clear n.
  revert m; induction l; simpl; intros.
  + destruct m; reflexivity.
  + destruct m.
    - reflexivity.
    - simpl.
      rewrite IHl.
      reflexivity.
Qed.


Lemma Znth_replace_Znth_Same : forall {A} (d: A) (l: list A) (i: Z) (v: A),
  0 <= i < Zlength l ->
  Znth i (replace_Znth i v l) d = v.
Proof.
  intros.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat i).
  rewrite Zlength_correct in H.
  assert (0 <= m < length l)%nat by lia.
  clearbody m. clear H i.
  generalize dependent m.
  induction l; simpl in * ; intros.
  + lia.
  + destruct m.
    - reflexivity.
    - simpl.
      rewrite IHl; auto.
      lia.
Qed. 

Lemma Znth_replace_Znth_Diff : forall {A} (d: A) (l: list A) (i j: Z) (v: A),
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  i <> j ->
  Znth j (replace_Znth i v l) d = Znth j l d.
Proof.
  intros.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat i).
  set (n := Z.to_nat j).
  rewrite Zlength_correct in H, H0.
  assert (0 <= m < length l)%nat by lia.
  assert (0 <= n < length l)%nat by lia.
  assert (m <> n) by lia.
  clearbody m. clearbody n.
  clear H H0 H1 i j.
  generalize dependent m.
  generalize dependent n.
  induction l; simpl in * ; intros.
  + lia.
  + destruct m, n ; simpl in * ; try auto ; try lia.
    rewrite IHl; try lia. auto.
Qed.

(* Zsublist *)

Lemma Zsublist_nil:
  forall (l : list A) a b,
    b <= a -> sublist a b l = [].
Proof.
  intros. unfold sublist.
  apply skipn_all2.
  rewrite length_firstn; lia.
Qed.

Lemma Zsublist_of_nil:
  forall i j,
    sublist i j (@nil A) = [].
Proof.
  intros. unfold sublist.
  rewrite firstn_nil, skipn_nil. auto.
Qed.

Lemma Zsublist_Zsublist: forall i j k m (l:list A),
  0 <= m -> 
  0 <= k <=i -> 
  i <= j - m ->
  sublist k i (sublist m j l) = sublist (k + m) (i + m) l.
Proof.
  intros.
  unfold sublist.
  rewrite ! skipn_firstn_comm.
  rewrite firstn_firstn by lia.
  rewrite skipn_skipn.
  f_equal; [lia | ].
  f_equal; lia.
Qed.

Lemma Zsublist_Zsublist0: forall i j k (l:list A), 
  0 <= k -> 
  k <= i <=j ->
  sublist k i (sublist 0 j l) = sublist k i l.
Proof. intros. rewrite Zsublist_Zsublist; repeat rewrite Zplus_0_r; try lia; auto. Qed.

Lemma Zsublist_Zsublist00: forall i j (l:list A), 
  0 <= i <= j ->
  sublist 0 i (sublist 0 j l) = sublist 0 i l.
Proof. intros. apply Zsublist_Zsublist0; lia. Qed.

Local Open Scope nat.

(* nth *)

Lemma nth_firstn: forall (l: list A) n m d,
  (n < m)%nat ->
  nth n (firstn m l) d = nth n l d.
Proof.
  intros.
  rewrite nth_firstn. 
  destruct (n <? m) eqn:E; auto.
  rewrite Nat.ltb_ge in E; lia.
Qed.

Lemma firstn_skipSn: forall (n : nat) (l : list A),
  n < length l ->
  l = firstn n l ++ nth n l d :: skipn (S n) l.
Proof.
  induction n; intros.
  - destruct l; simpl in *; try lia. auto.
  - destruct l; simpl in *; try lia.
    f_equal. assert (n < length l) by lia.
    apply IHn. auto.
Qed.

(* sublist *)

Lemma length_sublist:
  forall (lo hi: nat) (l: list A),
    lo <= hi /\ hi <= length l ->
    length (Nsublist lo hi l) = hi-lo.
Proof.
  intros.
  unfold Nsublist.
  rewrite length_skipn.
  rewrite firstn_length_le by lia.
  reflexivity.
Qed.

Lemma length_sublist':
  forall (i j: nat) (l: list A),
    length (Nsublist i j l) = 
    (min j (length l) - i).
Proof.
  intros.
  unfold Nsublist.
  rewrite length_skipn.
  rewrite length_firstn.
  reflexivity.
Qed.

Lemma nth_sublist:
  forall (lo i hi: nat) (l: list A),
  i < hi-lo ->
  nth i (Nsublist lo hi l) d = nth (i+lo) l d.
Proof.
  intros.
  unfold Nsublist.
  rewrite nth_skipn.
  rewrite nth_firstn by lia.
  f_equal.
  lia.
Qed.

(* tl_error *)

Lemma tl_error_last: forall a (l: list A),
  tl_error (l ++ a :: nil) = Some a. 
Proof.
  intros.
  unfold tl_error.
  rewrite length_app.
  simpl.
  rewrite nth_error_app2; [|lia]. 
  replace (length l + 1 - 1 - length l) with O by lia. 
  reflexivity.
Qed.

Lemma tl_error_app_skipn_connected: forall (l1 l2: list A),
  l1 <> nil ->
  l2 <> nil ->
  tl_error l1 = hd_error l2 ->
  tl_error (l1 ++ skipn 1 l2) = tl_error l2.
Proof.
  intros. 
  apply exists_last in H0 as [x [b ->]].
  rewrite tl_error_last. 
  destruct x; simpl in *. 
  rewrite app_nil_r; auto. 
  rewrite app_assoc. 
  apply tl_error_last.
Qed.


End Index.