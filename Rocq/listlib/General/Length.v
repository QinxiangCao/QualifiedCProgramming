
Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ListLib.Base.Inductive.
Require Import ListLib.Base.Positional.

Import ListNotations.

Local Open Scope Z.



Section Length. 

Context {A: Type}
        (d: A).

Lemma Zlength_nonneg: forall (l: list A), 
  0 <= Zlength l.
Proof.
  intros. rewrite Zlength_correct.  lia.
Qed.

Lemma Zlength_app: forall (l1 l2: list A),
  Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof.
  intros.
  rewrite !Zlength_correct.
  rewrite length_app.
  lia.
Qed.


Lemma Zlength_app_cons: forall (l: list A) a,
  Zlength (l ++ (a :: nil)) = Zlength l + 1.
Proof.
  intros. 
  rewrite Zlength_app.
  rewrite Zlength_cons; simpl.
  lia.
Qed.

(* == about Znth == *)

Lemma app_Znth1: forall l l' i,
  0 <= i < Zlength l -> Znth i (l ++ l') d = Znth i l d.
Proof.
  intros.
  unfold Znth.
  assert (Z.to_nat i < length l)%nat by (rewrite Zlength_correct in H; lia).
  set (j := Z.to_nat i) in *; clearbody j; clear i H.
  apply app_nth1; auto.
Qed.

Lemma app_Znth2: forall l l' i,
  i >= Zlength l -> Znth i (l ++ l') d = Znth (i - Zlength l) l' d.
Proof.
  intros.
  unfold Znth.
  pose proof (Zlength_nonneg l).
  assert (Z.to_nat i >= length l)%nat by
    (rewrite Zlength_correct in H; lia).
  replace (Z.to_nat (i - Zlength l)) with (Z.to_nat i - length l)%nat
    by (rewrite Zlength_correct in *; lia).
  apply app_nth2; auto.
Qed.

Lemma Znth_indep: forall (l : list A) n (d d': A),
  0 <= n < Zlength l ->
  Znth n l d = Znth n l d'.
Proof.
  intros.
  unfold Znth.
  apply nth_indep.
  rewrite Zlength_correct in H.
  lia.
Qed.

(* == about replace_(Z)nth == *)
Lemma replace_nth_app_l : forall n (a: A) l1 l2,
  (n < length l1)%nat ->
  replace_nth n (l1 ++ l2) a = replace_nth n l1 a ++ l2.
Proof.
  intros.
  generalize dependent l1.
  revert l2.
  induction n.
  + intros.
    destruct l1; simpl in *; try lia.
    simpl.
    reflexivity.
  + intros.
    destruct l1; simpl in *; try lia.
    simpl.
    f_equal.
    apply IHn.
    lia. 
Qed. 

Lemma replace_nth_app_r: forall n (a: A) l1 l2,
  (n >= length l1)%nat ->
  replace_nth n (l1 ++ l2) a = replace_nth n l1 a ++ replace_nth (n - length l1) l2 a.
Proof.
  intros.
  generalize dependent l1.
  revert l2.
  induction n; intros.
  + destruct l1; simpl in *; try lia.
    simpl.
    reflexivity.
  + destruct l1; simpl in *; [ | rewrite IHn ; auto; try lia].
    reflexivity. 
Qed. 

Lemma replace_Znth_app_l : forall n (a: A) l1 l2,
  (0 <= n) -> 
  (n < Zlength l1) ->
  replace_Znth n a (l1 ++ l2) = replace_Znth n a l1 ++ l2.
Proof.
  intros.
  unfold replace_Znth.
  apply replace_nth_app_l.
  rewrite Zlength_correct in H0.
  lia.
Qed. 

Lemma replace_Znth_app_r : forall n (a: A) l1 l2,
  (n >= Zlength l1) ->
  replace_Znth n a (l1 ++ l2) = replace_Znth n a l1 ++ replace_Znth (n - Zlength l1) a l2.
Proof. 
  intros.
  unfold replace_Znth.
  rewrite Zlength_correct in *.
  replace (Z.to_nat (n - Z.of_nat (length l1))) with (Z.to_nat n - length l1)%nat by lia.
  rewrite replace_nth_app_r ; try lia.
  auto.
Qed.


Lemma replace_Znth_nothing : forall n (l: list A) (a: A),
  n >= Zlength l -> replace_Znth n a l = l.
Proof.
  intros.
  rewrite Zlength_correct in H.
  unfold replace_Znth.
  assert (Z.to_nat n >= length l)%nat by lia.
  clear H. 
  set (m := Z.to_nat n) in *; clearbody m ; clear n.
  generalize dependent l.
  induction m; intros. 
  + destruct l; simpl in * ; auto ; lia.
  + destruct l; simpl in * ; auto.
    rewrite IHm ; auto. lia. 
Qed.

(* == about Znth_error == *)

Lemma Znth_error_range: forall (l: list A) (n: Z) (a: A),
  Znth_error l n = Some a ->
  0 <= n < Zlength l.
Proof.
  intros.
  unfold Znth_error in H.
  destruct (Z_le_gt_dec 0 n) as [Hle|Hn].
  + pose proof nth_error_Some l (Z.to_nat n) as [? _].
    specialize (H0 ltac:(congruence)).
    rewrite Zlength_correct in *.
    lia.
  + congruence.
Qed.

Lemma Znth_error_Some_cons:
  forall (m n: Z) (x: A) (l: list A) (a: A),
    n = m + 1 ->
    Znth_error l m = Some a ->
    Znth_error (x :: l) n = Some a.
Proof.
  intros.
  pose proof Znth_error_range _ _ _ H0.
  rewrite (Znth_error_cons m) by lia.
  apply H0.
Qed.


(* == about sublist == *)

Lemma sublist_length : forall lo hi (l : list A),
  0 <= lo <= hi -> 
  hi <= Zlength l -> 
  length (sublist lo hi l) = Z.to_nat (hi - lo).
Proof.
  intros.
  unfold sublist.
  rewrite length_skipn, length_firstn.
  rewrite Zlength_correct in H0.
  lia.
Qed.

Lemma sublist_app_exact1: forall (l1 l2: list A),
  sublist 0 (Zlength l1) (l1 ++ l2) = l1.
Proof.
  intros.
  unfold sublist.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  replace (length l1) with (length l1 + O)%nat by lia.
  rewrite (firstn_app_2 O).
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma sublist_split_app_l : forall lo hi (l1 l2 : list A),
  0 <= lo <= hi -> 
  hi <= Zlength l1 -> 
  sublist lo hi (l1 ++ l2) = sublist lo hi l1.
Proof.
  intros.
  unfold sublist.
  rewrite firstn_app.
  simpl. 
  rewrite Zlength_correct in H0.
  replace (Z.to_nat hi - length l1)%nat with O by lia.
  rewrite app_nil_r. auto. 
Qed. 

Lemma sublist_single : forall n (l : list A),
  0 <= n < Zlength l -> sublist n (n + 1) l = [Znth n l d].
Proof.
  intros.
  rewrite Zlength_correct in *.
  rewrite (firstn_skipSn d (Z.to_nat n) l) at 1; try lia.
  unfold Znth. 
  unfold sublist.
  rewrite firstn_app.
  assert (length (firstn (Z.to_nat n) l) = Z.to_nat n) by (rewrite length_firstn; lia).
  rewrite firstn_all2; try lia. 
  replace (Z.to_nat (n + 1) - length (firstn (Z.to_nat n) l))%nat with 1%nat by lia.
  rewrite skipn_app.
  replace (Z.to_nat n - length (firstn (Z.to_nat n) l))%nat with 0%nat by lia.
  rewrite skipn_all2; try lia.
  simpl. reflexivity.
Qed. 

Lemma sublist_split: forall lo hi mid (l : list A),
  0 <= lo <= mid -> 
  mid <= hi <= Zlength l ->
  sublist lo hi l = sublist lo mid l ++ sublist mid hi l.
Proof.
  intros.
  rewrite <- (firstn_skipn (Z.to_nat hi) l).
  remember (firstn (Z.to_nat hi) l) as l1.
  remember (skipn (Z.to_nat hi) l) as l2.
  assert (Z.of_nat (length l1) = hi).
  {
    rewrite Heql1.
    rewrite length_firstn.
    rewrite Zlength_correct in *.
    lia.
  }
  assert (length l = length l1 + length l2)%nat.
  {
    rewrite Heql1, Heql2.
    rewrite length_firstn, length_skipn.
    lia.
  }
  rewrite Zlength_correct in H0.
  rewrite H2 in H0.
  clear Heql1 Heql2 H2 l.
  do 3 (rewrite sublist_split_app_l; rewrite ?Zlength_correct in *; try lia).
  unfold sublist.
  replace (Z.to_nat hi)%nat with (length l1) by lia.
  assert (mid <= Z.of_nat (length l1)) by lia.
  clear H0 H1 l2 hi.
  rewrite firstn_all2 ; try lia.
  rename l1 into l. 
  rewrite <- (firstn_skipn (Z.to_nat lo) l).
  remember (firstn (Z.to_nat lo) l) as l1.
  remember (skipn (Z.to_nat lo) l) as l2.
  assert (Z.of_nat (length l1) = lo).
  {
    rewrite Heql1.
    rewrite length_firstn.
    lia.
  }
  rewrite firstn_app.
  do 3 rewrite skipn_app.
  rewrite firstn_all2 ; try lia.
  replace (Z.to_nat lo - length l1)%nat with O by lia.
  simpl.
  do 2 (rewrite skipn_all2 ; try lia).
  rewrite! app_nil_l.
  rewrite firstn_skipn.
  reflexivity.
Qed.

Lemma Zlength_sublist: forall lo hi (l: list A),
  0 <= lo <= hi /\ hi <= Zlength l ->
  Zlength (sublist lo hi l) = hi-lo.
Proof.
  intros.
  rewrite Zlength_correct. unfold sublist.
  rewrite length_skipn.
  rewrite firstn_length_le; try lia.
  rewrite Zlength_correct in H.
  lia.
Qed. 

Lemma Zlength_sublist0: forall hi (l: list A),
  0 <= hi /\ hi <= Zlength l ->
  Zlength (sublist 0 hi l) = hi.
Proof.
  intros.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma sublist_self:
  forall (l1: list A) x,
    x = Zlength l1 ->
    sublist 0 x l1 = l1.
Proof.
  intros. unfold sublist; subst.
  rewrite skipn_O. rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length l1))) with (length l1) by lia.
  apply firstn_all.
Qed.

Lemma Zlength_sublist':
  forall (l: list A) i j,
    Zlength (sublist i j l) = 
    Z.of_nat (min (Z.to_nat j) (length l) - Z.to_nat i).
Proof.
  intros.
  rewrite Zlength_correct.
  unfold sublist.
  rewrite length_skipn.
  rewrite length_firstn.
  reflexivity.
Qed.

Lemma sublist_split_app_r:
  forall lo hi len (l1 l2: list A),
    Zlength l1 = len ->
    len <= lo <= hi ->
    sublist lo hi (l1 ++ l2) = sublist (lo - len) (hi - len) l2.
Proof.
  intros.
  unfold sublist.
  repeat rewrite skipn_firstn_comm.
  rewrite skipn_app.
  pose proof (length_skipn (Z.to_nat lo) l1).
  rewrite Zlength_correct in H.
  replace (length l1 - Z.to_nat lo)%nat with O in H1 by lia.
  rewrite length_zero_iff_nil in H1; rewrite H1.
  simpl.
  replace (Z.to_nat (hi - len) - Z.to_nat (lo - len))%nat with (Z.to_nat hi - Z.to_nat lo)%nat by lia.
  replace (Z.to_nat lo - Datatypes.length l1)%nat with (Z.to_nat (lo - len)) by lia.
  auto.
Qed.

Lemma sublist_cons1:
  forall n a (l: list A),
    1 <= n -> sublist 0 n (a::l) = a :: (sublist 0 (n - 1) l).
Proof.
  intros.
  unfold sublist.
  repeat rewrite skipn_firstn_comm.
  repeat rewrite skipn_O.
  replace (Z.to_nat n - Z.to_nat 0)%nat with (S(Z.to_nat (n - 1) - Z.to_nat 0)) by lia.
  apply firstn_cons.
Qed.

Lemma sublist_cons2:
  forall m n a (l: list A),
    1 <= m <= n -> n  <= Zlength (a :: l) ->
    sublist m n (a :: l) = sublist (m - 1) (n - 1) l.
Proof.
  intros.
  unfold sublist.
  repeat rewrite skipn_firstn_comm.
  replace (Z.to_nat m) with (S (Z.to_nat (m - 1))) at 2 by lia.
  rewrite skipn_cons.
  replace (Z.to_nat (n - 1) - Z.to_nat (m - 1))%nat with (Z.to_nat n - Z.to_nat m)%nat by lia.
  reflexivity.
Qed.

(* == about mixed indexed definitions == *)

Lemma Znth_sublist: forall lo i hi (l: list A),
  0 <= lo ->
  0 <= i < hi - lo ->
  Znth i (sublist lo hi l) d = Znth (i + lo) l d.
Proof.
  intros.
  unfold sublist, Znth.
  rewrite nth_skipn.
  rewrite nth_firstn by lia.
  f_equal.
  lia.
Qed.

Lemma Znth_sublist0: forall i hi (l: list A),
  0 <= i < hi ->
  Znth i (sublist 0 hi l) d = Znth i l d.
Proof.
  intros.
  rewrite Znth_sublist by lia.
  f_equal.
  lia.
Qed.


Lemma Znth_sublist_lt : forall lo hi (l : list A) i,
  0 <= lo <= hi -> 
  hi <= Zlength l -> 
  0 <= i < hi - lo -> 
  Znth i (sublist lo hi l) d = Znth (lo + i) l d.
Proof. 
  intros. unfold Znth.
  pose proof (firstn_skipn (Z.to_nat lo) l).
  rewrite <- H2 at 2.
  replace (Z.to_nat (lo + i)) with (length (firstn (Z.to_nat lo) l) + Z.to_nat i)%nat by (rewrite length_firstn ; rewrite Zlength_correct in *; lia).
  rewrite app_nth2_plus.
  replace (skipn (Z.to_nat lo) l) with (sublist lo hi l ++ sublist hi (Z.of_nat (length l)) l) .
  - rewrite app_nth1 ; auto. 
    rewrite sublist_length ; try lia.
  - replace (skipn (Z.to_nat lo) l) with (sublist lo (Z.of_nat (length l)) l).
    + rewrite <- sublist_split ; auto ; rewrite Zlength_correct in *; lia. 
    + unfold sublist. rewrite firstn_all2 ; auto. lia.
Qed.

Lemma Znth_sublist_ge : forall lo hi (l : list A) i,
  0 <= lo <= hi -> 
  hi <= Zlength l -> 
  hi - lo <= i -> 
  Znth i (sublist lo hi l) d = d.
Proof.
  intros. unfold Znth.
  rewrite nth_overflow ; auto.
  rewrite sublist_length ; lia.
Qed.

Lemma list_eq_ext: forall (l1 l2: list A) d,
  l1 = l2 <->
  (Zlength l1 = Zlength l2 /\
   forall i, 0 <= i < Zlength l1 -> Znth i l1 d = Znth i l2 d).
Proof.
  intros.
  split; [intros; subst; auto |].
  intros [? ?].
  revert l2 H H0; induction l1; simpl; intros.
  + destruct l2.
    - reflexivity.
    - rewrite !Zlength_correct in H. 
      simpl in H.
      lia.
  + destruct l2.
    - rewrite !Zlength_correct in H. 
      simpl in H.
      lia.
    - rewrite !Zlength_cons in H.
      specialize (IHl1 l2 ltac:(lia)).
      pose proof Zlength_nonneg l1.
      rewrite Zlength_cons in H0.
      pose proof H0 0 ltac:(lia).
      rewrite !Znth0_cons in H2.
      subst a0.
      f_equal.
      apply IHl1.
      intros.
      specialize (H0 (i + 1) ltac:(lia)).
      rewrite !Znth_cons in H0 by lia.
      replace (i + 1 - 1) with i in H0 by lia.
      tauto.
Qed.

(* based on nat *)

Local Open Scope nat.

Lemma length_nonnil: forall (l: list A),
  l <> [] -> length l > 0.
Proof. 
  intros.
  destruct l.
  - congruence.
  - simpl; lia.
Qed.

(* about nth *)

Lemma nth_sublist:
  forall (lo i hi: nat) (l: list A),
  i < hi - lo ->
  nth i (Nsublist lo hi l) d = nth (i + lo) l d.
Proof.
  intros.
  unfold Nsublist.
  rewrite nth_skipn.
  rewrite nth_firstn by lia.
  f_equal.
  lia.
Qed.

(* about sublist *)

Lemma length_sublist:
  forall (lo hi: nat) (l: list A),
    lo <= hi /\ hi <= length l ->
    length (Nsublist lo hi l) = hi - lo.
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

Lemma sublist_nil:
  forall (l : list A) a b,
    b <= a -> Nsublist a b l = [].
Proof.
  intros. unfold Nsublist.
  apply skipn_all2.
  rewrite length_firstn; lia.
Qed.

Lemma Nsublist_single: forall (n : nat) (l : list A),
  n < length l -> Nsublist n (n + 1) l = [nth n l d].
Proof.
  intros.
  rewrite (firstn_skipSn d _ _ H) at 1; try lia.
  unfold Nsublist.
  rewrite firstn_app.
  assert (length (firstn n l) = n) by (rewrite length_firstn; lia).
  rewrite firstn_all2; try lia. 
  replace ((n + 1) - length (firstn (n) l))%nat with 1%nat by lia.
  rewrite skipn_app.
  replace (n - length (firstn (n) l))%nat with 0%nat by lia.
  rewrite skipn_all2; try lia.
  simpl. reflexivity.
Qed.

Lemma sublist_one_ele: 
  forall i (text: list A) (ch: A),
    0 <= i < length text ->
    ch = nth i text d -> 
    Nsublist 0 i text ++ [ch] = Nsublist 0 (i + 1) text.
Proof.
  intros. 
  eapply nth_ext.
  + rewrite length_app.
    rewrite ! length_sublist by lia.
    simpl; lia.
  + intros.
    destruct (le_gt_dec i n).
    - rewrite app_nth2 by (rewrite length_sublist by lia; lia).
      rewrite length_app, length_sublist in H1 by lia.
      simpl in H1.
      rewrite !nth_sublist by lia.
      rewrite length_sublist by lia.
      replace (n - (i - 0)) with 0 by lia.
      simpl.
      subst ch.
      f_equal; lia.
    - rewrite app_nth1 by (rewrite length_sublist by lia; lia).
      rewrite !nth_sublist by lia.
      reflexivity.
Qed.

Lemma sublist_one_ele':
  forall i (text: list A),
    0 <= i < length text ->
    Nsublist 0 (i + 1) text = Nsublist 0 i text ++ [nth i text d].
Proof.
  intros. 
  erewrite sublist_one_ele; eauto.
Qed.

Lemma sublist_single':
  forall (n : nat) (l : list A),
    0 < n <= length l ->
    Nsublist (n - 1) n l = [nth (n - 1) l d].
Proof.
  intros.
  remember (n-1) as t.
  assert (n = t + 1) by lia.
  rewrite H0.
  apply Nsublist_single; lia.
Qed.

Lemma Nsublist_self:
  forall (l1: list A) x,
    x = length l1 ->
    Nsublist 0 x l1 = l1.
Proof.
  intros. unfold Nsublist; subst.
  rewrite skipn_O.
  apply firstn_all.
Qed.

Lemma Nsublist_split_app_l: forall (lo hi: nat) (l1 l2 : list A),
  lo <= hi -> hi <= length l1 -> Nsublist lo hi (l1 ++ l2) = Nsublist lo hi l1.
Proof.
  intros.
  unfold Nsublist.
  rewrite firstn_app.
  simpl. 
  replace (hi - length l1)%nat with O by lia.
  rewrite app_nil_r. auto. 
Qed.

Lemma Nsublist_split_app_r:
  forall lo hi len (l1 l2: list A),
    length l1 = len ->
    len <= lo <= hi ->
    Nsublist lo hi (l1 ++ l2) = Nsublist (lo - len) (hi - len) l2.
Proof.
  intros.
  unfold Nsublist.
  repeat rewrite skipn_firstn_comm.
  rewrite skipn_app.
  pose proof (length_skipn lo l1).
  replace (length l1 - lo) with O in H1 by lia.
  rewrite length_zero_iff_nil in H1; rewrite H1.
  simpl.
  replace (hi - len - (lo - len)) with (hi - lo) by lia.
  replace (lo - length l1) with (lo - len) by lia.
  auto.
Qed.

Lemma Nsublist_split: 
  forall (lo hi mid: nat) (l : list A),
    0 <= lo <= mid -> 
    mid <= hi <= length l ->
    Nsublist lo hi l = 
    Nsublist lo mid l ++ Nsublist mid hi l.
Proof.
  intros.
  rewrite <- (firstn_skipn hi l).
  remember (firstn hi l) as l1.
  remember (skipn hi l) as l2.
  assert (length l1 = hi).
  {
    rewrite Heql1.
    rewrite length_firstn.
    lia.
  }
  assert (length l = length l1 + length l2)%nat.
  {
    rewrite Heql1, Heql2.
    rewrite length_firstn, length_skipn.
    lia.
  }
  rewrite H2 in H0.
  clear Heql1 Heql2 H2 l.
  do 3 (rewrite Nsublist_split_app_l ; try lia).
  unfold Nsublist.
  replace hi%nat with (length l1) by lia.
  assert (mid <= length l1) by lia.
  clear H0 H1 l2 hi.
  rewrite firstn_all2 ; try lia.
  rename l1 into l. 
  rewrite <- (firstn_skipn ( lo) l).
  remember (firstn ( lo) l) as l1.
  remember (skipn ( lo) l) as l2.
  assert (length l1 = lo).
  {
    rewrite Heql1.
    rewrite length_firstn.
    lia.
  }
  rewrite firstn_app.
  do 3 rewrite skipn_app.
  rewrite firstn_all2 ; try lia.
  replace ( lo - length l1)%nat with O by lia.
  simpl.
  do 2 (rewrite skipn_all2 ; try lia).
  rewrite! app_nil_l.
  rewrite firstn_skipn.
  reflexivity.
Qed.

End Length.