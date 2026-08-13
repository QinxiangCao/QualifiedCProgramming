
Require Import Lia.
Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import MaxMinLib.MaxMin.
Require Import Coq.Logic.Classical_Prop.

Local Open Scope sets.

(* MaxMin in Z *)

Section Z.

Theorem Z_le_total: forall x y, {Z.le x y} + {Z.le y x}.
Proof. intros. destruct (Z_le_dec x y); [left | right]; lia. Qed.


Lemma max_n_in_range: forall (Q: Z -> Prop) (K: Z),
  (0 <= K)%Z ->
  (exists n, (0 <= n <= K)%Z /\ Q n) ->
  exists m, Q m /\ (0 <= m <= K)%Z /\ (forall k, (0 <= k <= K)%Z -> Q k -> k <= m)%Z.
Proof.
  intros Q K HK Hexists.
  remember (Z.to_nat K) as n.
  revert K Heqn Hexists HK.
  induction n; intros.
  - assert (K = 0)%Z by lia. subst.
    destruct Hexists as [x [[Hlow Hhigh] HP]].
    assert (x = 0)%Z by lia. subst.
    exists 0%Z. repeat split; auto; intros; lia.
  - destruct (classic (Q K)) as [HPK | HNPK].
    + exists K. repeat split; auto; intros; lia.
    + assert (Hexists': exists n, (0 <= n <= K - 1)%Z /\ Q n).
      { destruct Hexists as [x [[Hlx Hhx] HPx]].
        exists x. split; auto. 
        destruct (classic (x = K)); subst; [contradiction|lia]. }
      specialize (IHn (K - 1)%Z). 
      destruct IHn as [m [HPm [[Hlm Hhm] Hmax]]]; 
      [lia|auto|lia|].
      exists m. repeat split; auto; [lia |].
      intros k Hrange HPk.
      assert (k < K)%Z by (destruct (Z.eq_dec k K); [subst; contradiction | lia]).
      apply Hmax; [lia | auto].
Qed.

Lemma min_n_in_range: forall (Q: Z -> Prop) (K: Z),
  (0 <= K)%Z ->
  (exists n, (0 <= n <= K)%Z /\ Q n) ->
  exists m, Q m /\ (0 <= m <= K)%Z /\ (forall k, (0 <= k <= K)%Z -> Q k -> m <= k)%Z.
Proof.
  intros Q K HK Hexists.
  remember (Z.to_nat K) as n.
  revert Q K Heqn Hexists HK.
  induction n; intros.
  - assert (K = 0)%Z by lia. subst.
    destruct Hexists as [x [[Hlow Hhigh] HP]].
    assert (x = 0)%Z by lia. subst.
    exists 0%Z. repeat split; auto; intros; try lia.
  - destruct (classic (Q 0%Z)) as [Q0 | NotQ0].
    + exists 0%Z. split; [|split]; auto; intros; lia.
    + assert (Hexists': exists n, (0 <= n <= K - 1)%Z /\ (fun x => Q (x + 1)%Z) n).
      { destruct Hexists as [x [[Hlx Hhx] Qx]].
        assert (x > 0)%Z by (destruct (Z.eq_dec x 0); [subst; contradiction|lia]).
        exists (x - 1)%Z. split; [lia|].
        replace (x - 1 + 1)%Z with x by lia; auto. }
      specialize (IHn (fun x => Q (x + 1)%Z) (K - 1)%Z).
      destruct IHn as [m [Qm [[Hlm Hhm] Hmin]]]; [lia|auto|lia|].
      exists (m + 1)%Z. split; [|split]; auto; [lia|].
      intros k Hrange Qk.
      assert (k > 0)%Z by (destruct (Z.eq_dec k 0); [subst; contradiction|lia]).
      pose proof Hmin (k - 1)%Z ltac:(lia) ltac:(replace (k - 1 + 1)%Z with k by lia; auto) as Hle. 
      lia.
Qed.


End Z.

#[export] Instance Zle_TotalOrder: TotalOrder Z.le := {
  le_refl := Z.le_refl;
  le_trans := Z.le_trans;
  le_antisym := Z.le_antisymm;
  le_total := Z_le_total;
}.

(* MaxMin in Nat *)

Section Nat.

Theorem Nat_le_total: forall x y, {Nat.le x y} + {Nat.le y x}.
Proof. intros. destruct (le_ge_dec x y); [left | right]; auto. Qed. 

(* 只有在nat(良序关系)上且谓词为最小值时，存在性引理才成立 *)

Theorem min_nonempty_exists {A: Type}: 
  forall (f: A -> nat) (P: A -> Prop),
    (exists a, P a) -> 
    exists b, min_value_of_subset Nat.le P f b.
Proof.
  intros f P [a0 Ha0].
  remember (f a0) as n eqn:Heqn.
  revert a0 Ha0 Heqn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros a0 Ha0 Heqn.
  destruct (classic (exists a', P a' /\ f a' < f a0)) as [Hsmaller | Hminimal].
  - destruct Hsmaller as [a' [Ha' Hlt]].
    assert (f a' < n) by lia.
    eapply (IH (f a')); eauto.
  - exists (f a0).
    exists a0; split; auto. 
    split; auto.
    intros a Ha.
    destruct (Nat.le_gt_cases (f a0) (f a)) as [Hle | Hgt].
    * exact Hle.
    * exfalso. apply Hminimal.
      exists a; split; auto.
Qed.

(* 索引并集性质: 最小值的并集的最小值 = 并集的最小值 *)

Theorem min_union_iff {A: Type}:
  forall (f: A -> nat) (P Q: A -> Prop),
    min_value_of_subset Nat.le (P ∪ Q) f == 
    min_value_of_subset Nat.le (min_value_of_subset Nat.le P f ∪ min_value_of_subset Nat.le Q f) id.
Proof.
  intros; split; intros. 
  - destruct H as [? [[[]] ?]]; exists a; split; auto; split.
    * left; exists x; split; firstorder. 
    * intros; destruct H2; destruct H2 as [? [[] ?]]; subst; firstorder.  
    * right; exists x; split; firstorder. 
    * intros; destruct H2; destruct H2 as [? [[] ?]]; subst; firstorder.  
  - destruct H as [? []]; subst; unfold id. 
    destruct H as [[[a []]|[b []]] Hismin]; 
    [exists a | exists b]; split; auto.
    + split; [left; destruct H; auto| intros ? []]. 
      * apply H in H1; auto. 
      * pose proof min_nonempty_exists f Q ltac:(exists b; auto) as [fb' [b' []]].
        subst; unfold id in Hismin. 
        pose proof Hismin (f b') ltac:(right; exists b'; split; auto). 
        apply H2 in H1. 
        lia.  
    + split; [right; destruct H; auto| intros a []]. 
      * pose proof min_nonempty_exists f P ltac:(exists a; auto) as [fa' [a' []]].
        subst; unfold id in Hismin. 
        pose proof Hismin (f a') ltac:(left; exists a'; split; auto). 
        apply H2 in H1. 
        lia. 
      * apply H in H1; auto. 
Qed.

End Nat.

#[export] Instance NatLe_TotalOrder: TotalOrder Nat.le := {
  le_refl := Nat.le_refl;
  le_trans := Nat.le_trans;
  le_antisym := Nat.le_antisymm;
  le_total := Nat_le_total;
}.

Section Nat_op.

(* None is +inf *)

Definition Nat_op_le: option nat -> option nat -> Prop := 
  fun x y => match x, y with
  | Some x, Some y => Nat.le x y
  | _, None => True
  | None, _ => False
  end.

Definition Nat_op_plus: option nat -> option nat -> option nat :=
  fun x y => match x, y with
  | Some x, Some y => Some (x + y)
  | None, _ => None
  | _, None => None
  end.

Definition Nat_op_min (x y: option nat) : option nat :=
  match x, y with
  | Some xv, Some yv => Some (min xv yv)
  | Some xv, None    => Some xv
  | None,    Some yv => Some yv
  | None,    None    => None
  end.

Theorem Nat_op_le_refl: forall x, Nat_op_le x x.
Proof. intros. destruct x; simpl; auto. Qed.

Theorem Nat_op_le_trans: forall x y z, Nat_op_le x y -> Nat_op_le y z -> Nat_op_le x z. 
Proof. intros. destruct x, y, z; simpl in *; lia. Qed. 

Theorem Nat_op_le_antisym: forall x y, Nat_op_le x y -> Nat_op_le y x -> x = y.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  - f_equal; lia.
  - exfalso; auto.
  - exfalso; auto.
Qed.

Theorem Nat_op_le_total: forall x y, {Nat_op_le x y} + {Nat_op_le y x}.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  apply Nat_le_total.
Qed.

#[export] Instance Nat_op_le_TotalOrder: TotalOrder Nat_op_le := {
  le_refl := Nat_op_le_refl;
  le_trans := Nat_op_le_trans;
  le_antisym := Nat_op_le_antisym;
  le_total := Nat_op_le_total
}.

End Nat_op.




Section Z_op.

Local Open Scope Z.

(* None is +inf *)

Definition Z_op_le: option Z -> option Z -> Prop := 
  fun x y => match x, y with
  | Some x, Some y => Z.le x y
  | _, None => True
  | None, _ => False
  end.

Definition Z_op_plus: option Z -> option Z -> option Z :=
  fun x y => match x, y with
  | Some x, Some y => Some (x + y)
  | None, _ => None
  | _, None => None
  end.

Definition Z_op_min: option Z -> option Z -> option Z :=
  fun x y => match x, y with
  | Some xv, Some yv => Some (Z.min xv yv)
  | Some xv, None    => Some xv
  | None,    Some yv => Some yv
  | None,    None    => None
  end.

Theorem Z_op_le_refl: forall x, Z_op_le x x.
Proof. intros. destruct x; simpl; lia. Qed.

Theorem Z_op_le_trans: forall x y z, Z_op_le x y -> Z_op_le y z -> Z_op_le x z. 
Proof. intros. destruct x, y, z; simpl in *; lia. Qed. 

Theorem Z_op_le_antisym: forall x y, Z_op_le x y -> Z_op_le y x -> x = y.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  - f_equal; lia.
  - exfalso; auto.
  - exfalso; auto.
Qed. 

Theorem Z_op_le_total: forall x y, {Z_op_le x y} + {Z_op_le y x}.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  apply Z_le_total.
Qed.

#[export] Instance Z_op_le_TotalOrder: TotalOrder Z_op_le := {
  le_refl := Z_op_le_refl;
  le_trans := Z_op_le_trans;
  le_antisym := Z_op_le_antisym;
  le_total := Z_op_le_total
}.

Lemma Z_op_plus_mono: forall x1 x2 y1 y2,
  Z_op_le x1 x2 -> Z_op_le y1 y2 -> 
  Z_op_le (Z_op_plus x1 y1) (Z_op_plus x2 y2).
Proof.
  intros. destruct x1, x2, y1, y2; simpl in *; try tauto; try lia.
Qed.

Lemma Z_op_none_le_iff: forall x, 
  Z_op_le None x <-> x = None.
Proof.
  intros. split; intros.
  - destruct x; simpl in *; try tauto.
  - destruct x; simpl in *; try congruence; auto.
Qed. 

Lemma Z_op_le_ge_cases: forall x y, 
  Z_op_le x y \/ Z_op_le y x. 
Proof.
  intros. destruct x, y; simpl in *; auto.
  apply Z.le_ge_cases.
Qed.

Lemma Z_op_plus_O_r: forall x, 
  (Z_op_plus x (Some 0)) = x.
Proof. intros. destruct x; simpl in *; try f_equal; try lia. Qed. 

Lemma Z_op_plus_O_l: forall x, 
  (Z_op_plus (Some 0) x) = x.
Proof. intros. destruct x; simpl in *; try f_equal; try lia. Qed. 

Lemma Z_op_plus_none_r: forall x, 
  (Z_op_plus x None) = None.
Proof. destruct x; reflexivity. Qed.

Lemma Z_op_plus_comm :
  forall x y,
    Z_op_plus x y = Z_op_plus y x.
Proof.
  intros x y.
  destruct x, y; simpl; auto.
  f_equal; lia.
Qed.

Lemma Z_op_plus_assoc :
  forall x y z,
    Z_op_plus x (Z_op_plus y z) = Z_op_plus (Z_op_plus x y) z.
Proof.
  intros x y z.
  destruct x, y, z; simpl; auto.
  f_equal; lia.
Qed.

Lemma Z_op_min_none_r: forall x, 
  (Z_op_min x None) = x.
Proof. destruct x; reflexivity. Qed.

Lemma Z_op_min_le_l: forall x, 
  (Z_op_min None x) = x.
Proof. destruct x; reflexivity. Qed.

Lemma Z_op_le_none_r: forall x, 
  Z_op_le x None.
Proof. destruct x; reflexivity. Qed.

Lemma Z_op_le_min_l: forall x y, 
  Z_op_le x y -> Z_op_min x y = x.
Proof.
  intros. destruct x, y; simpl in *; try tauto. 
  f_equal; lia.
Qed.

Lemma Z_op_le_min_r: forall x y, 
  Z_op_le y x -> Z_op_min x y = y.
Proof.
  intros. destruct x, y; simpl in *; try tauto. 
  f_equal; lia.
Qed.

Lemma Z_op_le_min_imply: forall x y z, 
  Z_op_le x y -> Z_op_le x z -> Z_op_le x (Z_op_min y z). 
Proof.
  intros. destruct x, y, z; simpl in *; try tauto. lia.
Qed.

Lemma Z_op_le_min_le_l: 
  forall x y, Z_op_le (Z_op_min x y) x.
Proof.
  intros. destruct x, y; simpl in *; try tauto; lia.
Qed.

Lemma Z_op_le_min_le_r: 
  forall x y, Z_op_le (Z_op_min x y) y.
Proof.
  intros. destruct x, y; simpl in *; try tauto; lia.
Qed. 

(* 在满足条件的有限列表中，一定可以选出最小值 *)
Theorem Z_op_finite_min {A: Type}:
  forall (f: A -> option Z) (P: A -> Prop) xs x,
    In x xs -> P x -> (forall y, P y -> In y xs) ->
    exists m, min_object_of_subset Z_op_le P f m.
Proof.
  intros f P xs x Hinx HPx Hsub.
  revert P x Hinx HPx Hsub.
  induction xs as [|a xs IH]; intros P x Hinx HPx Hsub; 
  [contradiction|].
  destruct (classic (P a)) as [HPa | HPa].
  + destruct (classic (exists y, In y xs /\ P y)) as [[y [Hiny HPy]] | Hnone].
    * destruct (IH (fun z => P z /\ In z xs) y Hiny (conj HPy Hiny)) as [m [[HPm Hminxs] Hmin]];
      [intros; tauto|].
      destruct (Z_op_le_total (f a) (f m)) as [Ham | Hma].
      - exists a; split; auto. 
        intros z HPz.
        destruct (classic (z = a)); subst; [apply Z_op_le_refl|].
        apply Z_op_le_trans with (y := f m); auto.
        apply Hmin; split; auto.
        specialize (Hsub z HPz) as [|]; subst; auto; contradiction.
      - exists m; split; auto. 
        intros z HPz.
        destruct (classic (z = a)); subst; auto.
        apply Hmin; split; auto.
        specialize (Hsub z HPz) as [|]; subst; auto; contradiction. 
    * exists a; split; auto. 
      intros z HPz.
      destruct (Hsub z HPz) as [|]; subst; [apply Z_op_le_refl|].
      exfalso; apply Hnone; exists z; split; auto. 
  + assert (In x xs).
    destruct Hinx as [Hx | Hx]; subst; auto; contradiction. 
    destruct (IH P x H HPx) as [m [HPm Hmin]]; 
    [|exists m; split; auto].
    intros z HPz. 
    specialize (Hsub z HPz) as [|]; subst; auto; contradiction. 
Qed.

End Z_op.
