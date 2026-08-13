Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition permutation : list Z -> list Z -> Prop := @Permutation Z.

Fixpoint increasing_aux (l : list Z) (x : Z) : Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ increasing_aux l0 y
  end.

Definition increasing (l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: l0 => increasing_aux l0 x
  end.

Definition same_outside_range (l l1 : list Z) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 0 = Znth k l 0.

Definition partitioned_at (l : list Z) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => x <= Znth p l 0) (sublist low p l) /\
  Forall (fun x => Znth p l 0 < x) (sublist (p + 1) (high + 1) l).

Definition partition_scan_inv
    (l l1 : list Z) (low high pivot i j : Z) : Prop :=
  permutation l l1 /\
  same_outside_range l l1 low high /\
  Znth high l1 0 = pivot /\
  (forall k, low <= k <= i -> Znth k l1 0 <= pivot) /\
  (forall k, i < k < j -> pivot < Znth k l1 0).

Inductive sorted_range (l : list Z) (left right : Z) : Prop :=
| sorted_range_base :
    left >= right ->
    sorted_range l left right
| sorted_range_from_left : forall p,
    p >= right ->
    partitioned_at l left right p ->
    sorted_range l left (p - 1) ->
    sorted_range l left right
| sorted_range_from_right : forall p,
    p <= left ->
    partitioned_at l left right p ->
    sorted_range l (p + 1) right ->
    sorted_range l left right
| sorted_range_from_both : forall p,
    left <= p <= right ->
    partitioned_at l left right p ->
    sorted_range l left (p - 1) ->
    sorted_range l (p + 1) right ->
    sorted_range l left right.

Definition strict_increasing_prefix (l : list Z) (len : Z) : Prop :=
  0 <= len <= Zlength l /\
  forall i j,
    0 <= i < j ->
    j < len ->
    Znth i l 0 < Znth j l 0.

Definition strict_increasing (l : list Z) : Prop :=
  strict_increasing_prefix l (Zlength l).

Definition same_values_prefix
    (out : list Z) (out_len : Z) (src : list Z) (src_len : Z) : Prop :=
  forall x,
    In x (sublist 0 out_len out) <-> In x (sublist 0 src_len src).

Definition dedup_scan_inv
    (src sorted cur : list Z) (slow fast : Z) : Prop :=
  Zlength src = Zlength sorted /\
  Zlength cur = Zlength sorted /\
  permutation src sorted /\
  increasing sorted /\
  1 <= fast <= Zlength sorted /\
  0 <= slow < fast /\
  strict_increasing_prefix cur (slow + 1) /\
  same_values_prefix cur (slow + 1) sorted fast /\
  (forall k, fast <= k < Zlength sorted -> Znth k cur 0 = Znth k sorted 0) /\
  Znth slow cur 0 = Znth (fast - 1) sorted 0.

Definition discretize_result
    (src : list Z) (n : Z) (out : list Z) (ret : Z) : Prop :=
  Zlength src = n /\
  Zlength out = n /\
  1 <= n /\
  1 <= ret <= n /\
  strict_increasing_prefix out ret /\
  same_values_prefix out ret src n /\
  (forall i,
      0 <= i < n ->
      exists r,
        0 <= r < ret /\ Znth r out 0 = Znth i src 0) /\
  (forall r,
      0 <= r < ret ->
      exists i,
        0 <= i < n /\ Znth r out 0 = Znth i src 0) /\
  (forall i j ri rj,
      0 <= i < n ->
      0 <= j < n ->
      0 <= ri < ret ->
      0 <= rj < ret ->
      Znth ri out 0 = Znth i src 0 ->
      Znth rj out 0 = Znth j src 0 ->
      (Znth i src 0 = Znth j src 0 -> ri = rj) /\
      (Znth i src 0 < Znth j src 0 -> ri < rj)).

Definition query_forward_result
    (map : list Z) (map_size target ret : Z) : Prop :=
  ((exists i,
      0 <= i < map_size /\
      Znth i map 0 = target /\
      ret = i) /\
   (forall j,
      0 <= j < map_size ->
      Znth j map 0 = target ->
      ret = j)) \/
  ((forall i, 0 <= i < map_size -> Znth i map 0 <> target) /\
   ret = -1).

Definition query_forward_search_inv
    (map : list Z) (map_size target low high : Z) : Prop :=
  0 <= low /\
  high < map_size /\
  low <= high + 1 /\
  (forall i, 0 <= i < low -> Znth i map 0 < target) /\
  (forall i, high < i < map_size -> target < Znth i map 0).

Lemma same_outside_range_refl__partition_scan :
  forall l left right,
    same_outside_range l l left right.
Proof.
  intros.
  unfold same_outside_range.
  split; [reflexivity|].
  intros; reflexivity.
Qed.
Lemma same_outside_range_swap_inside__partition_scan :
  forall l l1 low high i j,
    same_outside_range l l1 low high ->
    low <= i <= high ->
    low <= j <= high ->
    0 <= i < Zlength l1 ->
    0 <= j < Zlength l1 ->
    same_outside_range l
      (replace_Znth j (Znth i l1 0) (replace_Znth i (Znth j l1 0) l1))
      low high.
Proof.
  intros l l1 low high i j Hsame Hi_range Hj_range Hi_len Hj_len.
  destruct Hsame as [Hlen Houtside].
  unfold same_outside_range.
  split.
  - repeat rewrite Zlength_replace_Znth. exact Hlen.
  - intros k Hk Houtside_range.
    rewrite Znth_replace_Znth_Diff.
    2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
    2:{ rewrite Zlength_replace_Znth. rewrite <- Hlen. exact Hk. }
    2:{ lia. }
    rewrite Znth_replace_Znth_Diff.
    2:{ exact Hi_len. }
    2:{ rewrite <- Hlen. exact Hk. }
    2:{ lia. }
    apply Houtside; auto.
Qed.
Lemma replace_Znth_swap_form__partition_scan :
  forall (l1 l2 l3: list Z) (xi xj: Z),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xi :: l2 ++ xj :: l3)) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := Z) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0: replace_Znth 0 xj (xi :: l2 ++ xj :: l3) = xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xj :: l2 ++ xj :: l3)) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := Z) (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := (xj :: l3)) by lia.
  rewrite (replace_Znth_nothing (A := Z) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1: replace_Znth 0 xi (xj :: l3) = xi :: l3) by reflexivity.
  rewrite H1.
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__partition_scan :
  forall (l: list Z) i j (d: Z),
    0 <= i /\ i < j /\ j < Zlength l ->
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hrange.
  unfold permutation.
  destruct Hrange as [Hi [Hij Hj]].
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i: l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr: (nj < List.length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j: lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert (Hnat: (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm.
      rewrite Hnat.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl: l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_Znth_swap_form__partition_scan.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.
Lemma replace_nth_comm_Z__partition_scan :
  forall ni nj (l: list Z) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros ni nj l a b Hneq.
  revert nj l Hneq.
  induction ni; intros nj l Hneq; destruct l as [ | x xs ]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal.
      apply IHni.
      intros Heq.
      apply Hneq.
      now f_equal.
Qed.
Lemma replace_Znth_comm__partition_scan :
  forall (l: list Z) i j (a b: Z),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm_Z__partition_scan.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.
Lemma permutation_swap_Znth__partition_scan :
  forall (l: list Z) i j (d: Z),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_Znth_lt__partition_scan.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm__partition_scan by lia.
      apply permutation_swap_Znth_lt__partition_scan.
      lia.
    + assert (i = j) by lia.
      subst j.
      unfold permutation.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.
Lemma partition_scan_inv_init__partition_scan :
  forall l low high,
    0 <= low ->
    low <= high ->
    partition_scan_inv l l low high (Znth high l 0) (low - 1) low.
Proof.
  intros.
  unfold partition_scan_inv.
  split.
  - unfold permutation. apply Permutation_refl.
  - split.
    + apply same_outside_range_refl__partition_scan.
    + split.
      * reflexivity.
      * split; intros; lia.
Qed.
Lemma partition_scan_inv_step_gt__partition_scan :
  forall l l1 low high pivot i j,
    pivot < Znth j l1 0 ->
    j < high ->
    partition_scan_inv l l1 low high pivot i j ->
    partition_scan_inv l l1 low high pivot i (j + 1).
Proof.
  intros l l1 low high pivot i j Hgt_guard Hj_high Hinv.
  destruct Hinv as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  unfold partition_scan_inv.
  split; [exact Hperm|].
  split; [exact Hsame|].
  split; [exact Hpivot|].
  split; [exact Hle|].
  intros k Hk.
  assert (k = j \/ i < k < j) as [-> | Hmid] by lia.
  - exact Hgt_guard.
  - apply Hgt. exact Hmid.
Qed.
Lemma partition_scan_inv_step_le__partition_scan :
  forall l l1 low high pivot i j,
    0 <= low ->
    low <= high ->
    high < Zlength l1 ->
    Znth j l1 0 <= pivot ->
    j < high ->
    low - 1 <= i ->
    i < j ->
    j <= high ->
    partition_scan_inv l l1 low high pivot i j ->
    partition_scan_inv l
      (replace_Znth j (Znth (i + 1) l1 0)
         (replace_Znth (i + 1) (Znth j l1 0) l1))
      low high pivot (i + 1) (j + 1).
Proof.
  intros l l1 low high pivot i j Hlow Hlow_high Hhigh_len Hguard Hj_high
         Hlow_i Hij Hj_le Hinv.
  destruct Hinv as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  assert (Hi1_len : 0 <= i + 1 < Zlength l1) by lia.
  assert (Hj_len : 0 <= j < Zlength l1) by lia.
  unfold partition_scan_inv.
  split.
  - eapply Permutation_trans.
    + exact Hperm.
    + apply permutation_swap_Znth__partition_scan; lia.
  - split.
    + apply same_outside_range_swap_inside__partition_scan; auto; lia.
    + split.
      * rewrite Znth_replace_Znth_Diff.
        2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
        2:{ rewrite Zlength_replace_Znth. lia. }
        2:{ lia. }
        rewrite Znth_replace_Znth_Diff by lia.
        exact Hpivot.
      * split.
        -- intros k Hk.
           destruct (Z.eq_dec k (i + 1)) as [Hki | Hki].
           ++ subst k.
              destruct (Z.eq_dec j (i + 1)) as [Hji | Hji].
              ** subst j.
                 rewrite Znth_replace_Znth_Same.
                 2:{ rewrite Zlength_replace_Znth. exact Hi1_len. }
                 exact Hguard.
              ** rewrite Znth_replace_Znth_Diff.
                 2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
                 2:{ rewrite Zlength_replace_Znth. exact Hi1_len. }
                 2:{ exact Hji. }
                 rewrite Znth_replace_Znth_Same by exact Hi1_len.
                 exact Hguard.
           ++ rewrite Znth_replace_Znth_Diff.
              2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
              2:{ rewrite Zlength_replace_Znth. lia. }
              2:{ lia. }
              rewrite Znth_replace_Znth_Diff by lia.
              apply Hle. lia.
        -- intros k Hk.
           destruct (Z.eq_dec k j) as [Hkj | Hkj].
           ++ subst k.
              rewrite Znth_replace_Znth_Same.
              2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
              apply Hgt. lia.
           ++ rewrite Znth_replace_Znth_Diff.
              2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
              2:{ rewrite Zlength_replace_Znth. lia. }
              2:{ lia. }
              rewrite Znth_replace_Znth_Diff by lia.
              apply Hgt. lia.
Qed.
Lemma Forall_sublist_by_Znth__partition_scan :
  forall (P : Z -> Prop) l lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> P (Znth k l 0)) ->
    Forall P (sublist lo hi l).
Proof.
  intros P l lo hi Hlohi Hhi_len Hrange.
  apply Forall_forall.
  intros x Hin.
  destruct (In_nth (sublist lo hi l) x 0 Hin) as [n [Hn Hnth]].
  assert (HnZ : 0 <= Z.of_nat n < Zlength (sublist lo hi l)).
  {
    rewrite Zlength_correct.
    lia.
  }
  rewrite Zlength_sublist in HnZ by lia.
  assert (Hz : Znth (Z.of_nat n) (sublist lo hi l) 0 = x).
  {
    unfold Znth.
    rewrite Nat2Z.id.
    exact Hnth.
  }
  rewrite <- Hz.
  rewrite Znth_sublist_lt by lia.
  apply Hrange.
  lia.
Qed.
Lemma partition_scan_inv_final_swap_partitioned_at__partition_scan :
  forall l l1 low high pivot i j,
    0 <= low ->
    low <= high ->
    low - 1 <= i ->
    high < Zlength l1 ->
    j >= high ->
    i < j ->
    j <= high ->
    partition_scan_inv l l1 low high pivot i j ->
    partitioned_at
      (replace_Znth high (Znth (i + 1) l1 0)
         (replace_Znth (i + 1) (Znth high l1 0) l1))
      low high (i + 1).
Proof.
  intros l l1 low high pivot i j Hlow Hlow_high Hlow_i Hhigh_len
         Hj_ge Hij Hj_le Hinv.
  assert (Hj_eq : j = high) by lia.
  subst j.
  destruct Hinv as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  set (l2 := replace_Znth high (Znth (i + 1) l1 0)
               (replace_Znth (i + 1) (Znth high l1 0) l1)).
  assert (Hi1_len : 0 <= i + 1 < Zlength l1) by lia.
  assert (Hhigh_len' : 0 <= high < Zlength l1) by lia.
  assert (Hpivot_l2 : Znth (i + 1) l2 0 = pivot).
  {
    subst l2.
    destruct (Z.eq_dec high (i + 1)) as [Hhi | Hhi].
    - subst high.
      rewrite Znth_replace_Znth_Same.
      2:{ rewrite Zlength_replace_Znth. exact Hi1_len. }
      exact Hpivot.
    - rewrite Znth_replace_Znth_Diff.
      2:{ rewrite Zlength_replace_Znth. exact Hhigh_len'. }
      2:{ rewrite Zlength_replace_Znth. exact Hi1_len. }
      2:{ exact Hhi. }
      rewrite Znth_replace_Znth_Same by exact Hi1_len.
      exact Hpivot.
  }
  unfold partitioned_at.
  split.
  - lia.
  - split.
    + apply Forall_sublist_by_Znth__partition_scan.
      * lia.
      * subst l2. repeat rewrite Zlength_replace_Znth. lia.
      * intros k Hk.
        rewrite Hpivot_l2.
        subst l2.
        rewrite Znth_replace_Znth_Diff.
        2:{ rewrite Zlength_replace_Znth. exact Hhigh_len'. }
        2:{ rewrite Zlength_replace_Znth. lia. }
        2:{ lia. }
        rewrite Znth_replace_Znth_Diff by lia.
        apply Hle. lia.
    + apply Forall_sublist_by_Znth__partition_scan.
      * lia.
      * subst l2. repeat rewrite Zlength_replace_Znth. lia.
      * intros k Hk.
        rewrite Hpivot_l2.
        subst l2.
        destruct (Z.eq_dec k high) as [Hkh | Hkh].
        -- subst k.
           rewrite Znth_replace_Znth_Same.
           2:{ rewrite Zlength_replace_Znth. exact Hhigh_len'. }
           apply Hgt. lia.
        -- rewrite Znth_replace_Znth_Diff.
           2:{ rewrite Zlength_replace_Znth. exact Hhigh_len'. }
           2:{ rewrite Zlength_replace_Znth. lia. }
           2:{ lia. }
           rewrite Znth_replace_Znth_Diff by lia.
           apply Hgt. lia.
Qed.
Lemma partition_scan_inv_final_same_outside__partition_scan :
  forall l l1 low high pivot i j,
    0 <= low ->
    low <= high ->
    low - 1 <= i ->
    high < Zlength l1 ->
    j >= high ->
    i < j ->
    j <= high ->
    partition_scan_inv l l1 low high pivot i j ->
    same_outside_range l
      (replace_Znth high (Znth (i + 1) l1 0)
         (replace_Znth (i + 1) (Znth high l1 0) l1))
      low high.
Proof.
  intros l l1 low high pivot i j Hlow Hlow_high Hlow_i Hhigh_len
         Hj_ge Hij Hj_le Hinv.
  assert (j = high) by lia.
  subst j.
  destruct Hinv as [_ [Hsame _]].
  apply same_outside_range_swap_inside__partition_scan; auto; lia.
Qed.
Lemma partition_scan_inv_final_permutation__partition_scan :
  forall l l1 low high pivot i j,
    0 <= low ->
    low <= high ->
    low - 1 <= i ->
    high < Zlength l1 ->
    j >= high ->
    i < j ->
    j <= high ->
    partition_scan_inv l l1 low high pivot i j ->
    permutation l
      (replace_Znth high (Znth (i + 1) l1 0)
         (replace_Znth (i + 1) (Znth high l1 0) l1)).
Proof.
  intros l l1 low high pivot i j Hlow Hlow_high Hlow_i Hhigh_len
         Hj_ge Hij Hj_le Hinv.
  assert (j = high) by lia.
  subst j.
  destruct Hinv as [Hperm [_]].
  eapply Permutation_trans.
  - exact Hperm.
  - apply permutation_swap_Znth__partition_scan; lia.
Qed.
Lemma same_outside_range_refl__quicksort_range :
  forall (l : list Z) left right,
    same_outside_range l l left right.
Proof.
  intros l left right.
  unfold same_outside_range.
  split.
  - reflexivity.
  - intros k Hk _.
    reflexivity.
Qed.
Lemma same_outside_range_trans__quicksort_range :
  forall (l l1 l2 : list Z) left right,
    same_outside_range l l1 left right ->
    same_outside_range l1 l2 left right ->
    same_outside_range l l2 left right.
Proof.
  intros l l1 l2 left right [Hlen1 Heq1] [Hlen2 Heq2].
  unfold same_outside_range.
  split.
  - rewrite Hlen1. exact Hlen2.
  - intros k Hk Hout.
    assert (Hk1 : 0 <= k < Zlength l1) by (rewrite <- Hlen1; exact Hk).
    rewrite (Heq2 k Hk1 Hout).
    apply Heq1; assumption.
Qed.
Lemma same_outside_range_weaken__quicksort_range :
  forall (l l1 : list Z) left1 right1 left2 right2,
    left2 <= left1 ->
    right1 <= right2 ->
    same_outside_range l l1 left1 right1 ->
    same_outside_range l l1 left2 right2.
Proof.
  intros l l1 left1 right1 left2 right2 Hleft Hright [Hlen Heq].
  unfold same_outside_range.
  split.
  - exact Hlen.
  - intros k Hk Hout.
    apply Heq; try assumption.
    destruct Hout as [Hout | Hout].
    + left; lia.
    + right; lia.
Qed.
Lemma Forall_permutation__quicksort_range :
  forall (P : Z -> Prop) l1 l2,
    permutation l1 l2 ->
    Forall P l1 ->
    Forall P l2.
Proof.
  intros P l1 l2 Hperm.
  induction Hperm; intros HForall.
  - exact HForall.
  - inversion HForall; subst.
    constructor; auto.
  - repeat match goal with
      | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end.
    constructor; auto.
  - apply IHHperm2.
    apply IHHperm1.
    exact HForall.
Qed.
Lemma Forall_Znth__quicksort_range :
  forall (P : Z -> Prop) (l : list Z) i (d : Z),
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l d).
Proof.
  intros P l i d HForall Hrange.
  apply Forall_forall with (x := Znth i l d) in HForall.
  - exact HForall.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrange.
    lia.
Qed.
Lemma sublist_eq_from_Znth__quicksort_range :
  forall (l1 l2 : list Z) lo hi,
    Zlength l1 = Zlength l2 ->
    0 <= lo <= hi ->
    hi <= Zlength l1 ->
    (forall k, lo <= k < hi -> Znth k l1 0 = Znth k l2 0) ->
    sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros l1 l2 lo hi Hlen Hlohi Hhilen Hpoint.
  apply (proj2 (list_eq_ext (sublist lo hi l1) (sublist lo hi l2) 0)).
  split.
  - repeat rewrite Zlength_correct.
    repeat rewrite sublist_length by
      (try exact Hlohi; try rewrite <- Hlen; exact Hhilen).
    lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    {
      rewrite Zlength_sublist in Hi by lia.
      exact Hi.
    }
    rewrite (@Znth_sublist_lt Z 0 lo hi l1 i).
    2: exact Hlohi.
    2: { exact Hhilen. }
    2: exact Hi'.
    rewrite (@Znth_sublist_lt Z 0 lo hi l2 i).
    2: exact Hlohi.
    2: { rewrite <- Hlen. exact Hhilen. }
    2: exact Hi'.
    apply Hpoint.
    lia.
Qed.
Lemma list_decompose_sublist__quicksort_range :
  forall (l : list Z) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    l = sublist 0 lo l ++ sublist lo hi l ++ sublist hi (Zlength l) l.
Proof.
  intros l lo hi Hlohi Hhilen.
  rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
  rewrite (sublist_split 0 (Zlength l) lo l).
  2: lia.
  2: {
    split.
    - transitivity hi; lia.
    - lia.
  }
  rewrite (sublist_split lo (Zlength l) hi l).
  2: lia.
  2: {
    split.
    - exact Hhilen.
    - lia.
  }
  reflexivity.
Qed.
Lemma same_outside_range_prefix__quicksort_range :
  forall (l l1 : list Z) left right,
    same_outside_range l l1 left right ->
    0 <= left <= Zlength l ->
    sublist 0 left l1 = sublist 0 left l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  apply sublist_eq_from_Znth__quicksort_range.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + lia.
    + left. lia.
Qed.
Lemma same_outside_range_suffix__quicksort_range :
  forall (l l1 : list Z) left right,
    same_outside_range l l1 left right ->
    0 <= right + 1 <= Zlength l ->
    sublist (right + 1) (Zlength l1) l1 = sublist (right + 1) (Zlength l) l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  rewrite <- Hlen.
  apply sublist_eq_from_Znth__quicksort_range.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + rewrite Hlen. lia.
    + right. lia.
Qed.
Lemma middle_permutation_of_same_outside__quicksort_range :
  forall (l l1 : list Z) left right,
    permutation l l1 ->
    same_outside_range l l1 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength l ->
    permutation (sublist left (right + 1) l) (sublist left (right + 1) l1).
Proof.
  intros l l1 left right Hperm Hsame Hlr Hlenr.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen _].
  pose proof (same_outside_range_prefix__quicksort_range _ _ _ _ Hsame0) as Hpre.
  pose proof (same_outside_range_suffix__quicksort_range _ _ _ _ Hsame0) as Hsuf.
  rewrite (list_decompose_sublist__quicksort_range l left (right + 1)) in Hperm by lia.
  assert (Hlenr1 : right + 1 <= Zlength l1) by (rewrite <- Hlen; exact Hlenr).
  rewrite (list_decompose_sublist__quicksort_range l1 left (right + 1)) in Hperm by lia.
  specialize (Hpre ltac:(lia)).
  specialize (Hsuf ltac:(lia)).
  rewrite Hpre, Hsuf in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.
Lemma Forall_sublist_by_Znth__quicksort_range :
  forall (P : Z -> Prop) (l : list Z) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> P (Znth k l 0)) ->
    Forall P (sublist lo hi l).
Proof.
  intros P l lo hi Hlohi Hhilen Hpoint.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert lo hi Hlohi Hhilen Hpoint Hn.
  induction n; intros lo hi Hlohi Hhilen Hpoint Hn.
  - assert (hi = lo) by lia.
    subst hi.
    rewrite Zsublist_nil by lia.
    constructor.
  - assert (lo < hi) by lia.
    rewrite (sublist_split lo hi (lo + 1) l).
    2: lia.
    2: {
      split.
      - lia.
      - exact Hhilen.
    }
    rewrite (@sublist_single Z 0 lo l) by lia.
    constructor.
    + simpl. apply Hpoint. lia.
    + apply IHn with (lo := lo + 1) (hi := hi).
      * lia.
      * exact Hhilen.
      * intros k Hk. apply Hpoint. lia.
      * assert (Hn' : Z.to_nat (hi - (lo + 1)) = n) by lia.
        symmetry. exact Hn'.
Qed.
Lemma partitioned_at_preserved_by_left__quicksort_range :
  forall l l1 left right p,
    permutation l l1 ->
    0 <= left ->
    same_outside_range l l1 left (p - 1) ->
    right < Zlength l ->
    partitioned_at l left right p ->
    partitioned_at l1 left right p.
Proof.
  intros l l1 left right p Hperm Hleft0 Hsame Hlen Hpart.
  destruct Hsame as [Hlen' Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 0 = Znth p l 0).
  {
    assert (Hp : 0 <= p < Zlength l) by lia.
    apply Heq.
    - exact Hp.
    - right. lia.
  }
  split.
  - lia.
  - split.
    + rewrite Hpiv.
      eapply (Forall_permutation__quicksort_range
                (fun x => x <= Znth p l 0)
                (sublist left p l)
                (sublist left p l1)).
      * assert (Hmid :
            permutation (sublist left (p - 1 + 1) l)
                        (sublist left (p - 1 + 1) l1)).
        {
          eapply middle_permutation_of_same_outside__quicksort_range
            with (left := left) (right := p - 1).
          - exact Hperm.
          - exact (conj Hlen' Heq).
          - lia.
          - lia.
        }
        replace (p - 1 + 1) with p in Hmid by lia.
        exact Hmid.
      * exact Hleft.
    + rewrite Hpiv.
      apply Forall_sublist_by_Znth__quicksort_range; try lia.
      intros k Hk.
      rewrite Heq by (try lia; right; lia).
      assert (Hk' : 0 <= k - (p + 1) < Zlength (sublist (p + 1) (right + 1) l)) by
        (rewrite Zlength_sublist by lia; lia).
      pose proof (Forall_Znth__quicksort_range _ _ (k - (p + 1)) 0 Hright Hk') as Hz.
      rewrite (@Znth_sublist_lt Z 0 (p + 1) (right + 1) l (k - (p + 1))) in Hz.
      2: lia.
      2: { lia. }
      2: {
        rewrite Zlength_sublist in Hk' by lia.
        exact Hk'.
      }
      replace (p + 1 + (k - (p + 1))) with k in Hz by lia.
      exact Hz.
Qed.
Lemma partitioned_at_preserved_by_right__quicksort_range :
  forall l l1 left right p,
    permutation l l1 ->
    0 <= left ->
    same_outside_range l l1 (p + 1) right ->
    right < Zlength l ->
    partitioned_at l left right p ->
    partitioned_at l1 left right p.
Proof.
  intros l l1 left right p Hperm Hleft0 Hsame Hlen Hpart.
  destruct Hsame as [Hlen' Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 0 = Znth p l 0).
  {
    assert (Hp : 0 <= p < Zlength l) by lia.
    apply Heq.
    - exact Hp.
    - left. lia.
  }
  split.
  - lia.
  - split.
    + rewrite Hpiv.
      assert (Hsub : sublist left p l1 = sublist left p l).
      {
        apply sublist_eq_from_Znth__quicksort_range.
        - symmetry. exact Hlen'.
        - lia.
        - lia.
        - intros k Hk.
          apply Heq.
          * lia.
          * left. lia.
      }
      rewrite Hsub.
      exact Hleft.
    + rewrite Hpiv.
      eapply (Forall_permutation__quicksort_range
                (fun x => Znth p l 0 < x)
                (sublist (p + 1) (right + 1) l)
                (sublist (p + 1) (right + 1) l1)).
      * assert (Hmid :
            permutation (sublist (p + 1) (right + 1) l)
                        (sublist (p + 1) (right + 1) l1)).
        {
          eapply middle_permutation_of_same_outside__quicksort_range
            with (left := p + 1) (right := right).
          - exact Hperm.
          - exact (conj Hlen' Heq).
          - lia.
          - lia.
        }
        exact Hmid.
      * exact Hright.
Qed.
Lemma partitioned_at_ext__quicksort_range :
  forall l l1 left right p,
    0 <= left ->
    right < Zlength l ->
    Zlength l = Zlength l1 ->
    (forall k, left <= k <= right -> Znth k l1 0 = Znth k l 0) ->
    partitioned_at l left right p ->
    partitioned_at l1 left right p.
Proof.
  intros l l1 left right p Hleft0 Hrightlen Hlen Heq [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 0 = Znth p l 0).
  { apply Heq. lia. }
  split.
  - lia.
  - split.
    + assert (Hsub : sublist left p l1 = sublist left p l).
      {
        apply sublist_eq_from_Znth__quicksort_range.
        - symmetry. exact Hlen.
        - lia.
        - rewrite <- Hlen. lia.
        - intros k Hk. apply Heq. lia.
      }
      rewrite Hpiv.
      rewrite Hsub.
      exact Hleft.
    + assert (Hsub : sublist (p + 1) (right + 1) l1 = sublist (p + 1) (right + 1) l).
      {
        apply sublist_eq_from_Znth__quicksort_range.
        - symmetry. exact Hlen.
        - lia.
        - rewrite <- Hlen. lia.
        - intros k Hk. apply Heq. lia.
      }
      rewrite Hpiv.
      rewrite Hsub.
      exact Hright.
Qed.
Lemma sorted_range_ext__quicksort_range :
  forall l l1 left right,
    0 <= left ->
    right < Zlength l ->
    Zlength l = Zlength l1 ->
    (forall k, left <= k <= right -> Znth k l1 0 = Znth k l 0) ->
    sorted_range l left right ->
    sorted_range l1 left right.
Proof.
  intros l l1 left right Hleft0 Hrightlen Hlen Heq Hsorted.
  revert l1 Hlen Heq.
  induction Hsorted; intros l1 Hlen Heq.
  - apply sorted_range_base. exact H.
  - apply sorted_range_from_left with (p := p).
    + exact H.
    + eapply partitioned_at_ext__quicksort_range.
      * exact Hleft0.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk. apply Heq. lia.
      * exact H0.
    + apply IHHsorted.
      * exact Hleft0.
      * pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        lia.
      * exact Hlen.
      * intros k Hk.
        pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        apply Heq.
        lia.
  - apply sorted_range_from_right with (p := p).
    + exact H.
    + eapply partitioned_at_ext__quicksort_range.
      * exact Hleft0.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk. apply Heq. lia.
      * exact H0.
    + apply IHHsorted.
      * pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        lia.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk.
        pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        apply Heq.
        lia.
  - apply sorted_range_from_both with (p := p).
    + exact H.
    + eapply partitioned_at_ext__quicksort_range.
      * exact Hleft0.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk. apply Heq. lia.
      * exact H0.
    + apply IHHsorted1.
      * exact Hleft0.
      * pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        lia.
      * exact Hlen.
      * intros k Hk.
        pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        apply Heq.
        lia.
    + apply IHHsorted2.
      * pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        lia.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk.
        pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        apply Heq.
        lia.
Qed.
Lemma increasing_aux_tail_increasing__quicksort_range :
  forall l x,
    increasing_aux l x ->
    increasing l.
Proof.
  intros l x Hinc.
  destruct l; simpl; auto.
  destruct Hinc as [_ Hrest].
  exact Hrest.
Qed.
Lemma increasing_aux_head_le_all__quicksort_range :
  forall l x k,
    increasing_aux l x ->
    0 <= k < Zlength l ->
    x <= Znth k l 0.
Proof.
  induction l; intros x k Hinc Hk.
  - rewrite Zlength_nil in Hk. lia.
  - simpl in Hinc.
    destruct Hinc as [Hxa Hrest].
    destruct (Z.eq_dec k 0) as [-> | Hneq].
    + reflexivity || exact Hxa.
    + rewrite Znth_cons by lia.
      eapply Z.le_trans.
      * exact Hxa.
      * apply IHl with (x := a); auto.
        rewrite Zlength_cons in Hk.
        lia.
Qed.
Lemma partitioned_at_left_Znth_le__quicksort_range :
  forall l left right p k,
    0 <= left ->
    p <= Zlength l ->
    partitioned_at l left right p ->
    left <= k < p ->
    Znth k l 0 <= Znth p l 0.
Proof.
  intros l left right p k Hleft0 Hp Hpart Hk.
  destruct Hpart as [_ [Hleft _]].
  pose proof (Forall_Znth__quicksort_range
                (fun x => x <= Znth p l 0)
                (sublist left p l)
                (k - left) 0 Hleft) as Hz.
  assert (Hk' : 0 <= k - left < Zlength (sublist left p l)).
  {
    rewrite Zlength_sublist by lia.
    lia.
  }
  specialize (Hz Hk').
  rewrite (@Znth_sublist_lt Z 0 left p l (k - left)) in Hz.
  2: lia.
  2: { exact Hp. }
  2: {
    rewrite Zlength_sublist in Hk' by lia.
    exact Hk'.
  }
  replace (left + (k - left)) with k in Hz by lia.
  exact Hz.
Qed.
Lemma partitioned_at_right_Znth_lt__quicksort_range :
  forall l left right p k,
    0 <= left ->
    right < Zlength l ->
    partitioned_at l left right p ->
    p < k <= right ->
    Znth p l 0 < Znth k l 0.
Proof.
  intros l left right p k Hleft0 Hrightlen Hpart Hk.
  destruct Hpart as [Hprange [_ Hright]].
  pose proof (Forall_Znth__quicksort_range
                (fun x => Znth p l 0 < x)
                (sublist (p + 1) (right + 1) l)
                (k - (p + 1)) 0 Hright) as Hz.
  assert (Hk' : 0 <= k - (p + 1) < Zlength (sublist (p + 1) (right + 1) l)).
  {
    rewrite Zlength_sublist by lia.
    lia.
  }
  specialize (Hz Hk').
  rewrite (@Znth_sublist_lt Z 0 (p + 1) (right + 1) l (k - (p + 1))) in Hz.
  2: lia.
  2: { lia. }
  2: {
    rewrite Zlength_sublist in Hk' by lia.
    exact Hk'.
  }
  replace (p + 1 + (k - (p + 1))) with k in Hz by lia.
  exact Hz.
Qed.
Lemma sorted_range_ordered__quicksort_range :
  forall l left right,
    0 <= left ->
    right < Zlength l ->
    sorted_range l left right ->
    forall i j,
      left <= i ->
      i <= j ->
      j <= right ->
      Znth i l 0 <= Znth j l 0.
Proof.
  intros l left right Hleft0 Hrightlen Hsorted.
  induction Hsorted; intros i j Hi Hij Hj.
  - assert (i = j) by lia.
    subst j.
    reflexivity.
  - pose proof H0 as Hpart.
    destruct H0 as [[Hp_left Hp_right] _].
    assert (p = right) by lia.
    subst p.
    destruct (Z.eq_dec j right) as [-> | Hjneq].
    + destruct (Z.eq_dec i right) as [-> | Hineq].
      * reflexivity.
      * eapply partitioned_at_left_Znth_le__quicksort_range.
        -- exact Hleft0.
        -- lia.
        -- exact Hpart.
        -- lia.
    + eapply IHHsorted; eauto; lia.
  - pose proof H0 as Hpart.
    destruct H0 as [[Hp_left Hp_right] _].
    assert (p = left) by lia.
    subst p.
    destruct (Z.eq_dec i left) as [-> | Hineq].
    + destruct (Z.eq_dec j left) as [-> | Hjneq].
      * reflexivity.
      * apply Z.lt_le_incl.
        eapply partitioned_at_right_Znth_lt__quicksort_range.
        -- exact Hleft0.
        -- exact Hrightlen.
        -- exact Hpart.
        -- lia.
    + eapply IHHsorted; eauto; lia.
  - pose proof H0 as Hpart.
    destruct H0 as [[Hp_left Hp_right] _].
    destruct (Z_lt_ge_dec j p) as [Hjp | Hpj].
    + eapply IHHsorted1; eauto; lia.
    + destruct (Z_gt_le_dec i p) as [Hip | Hpi].
      * eapply IHHsorted2; eauto; lia.
      * assert (Hip_cases : i = p \/ i < p) by lia.
        assert (Hj_cases : j = p \/ p < j) by lia.
        destruct Hip_cases as [-> | Hip'].
        {
          destruct Hj_cases as [-> | Hpj'].
          - reflexivity.
          - apply Z.lt_le_incl.
            eapply partitioned_at_right_Znth_lt__quicksort_range.
            + exact Hleft0.
            + exact Hrightlen.
            + exact Hpart.
            + lia.
        }
        {
          destruct Hj_cases as [-> | Hpj'].
          - eapply partitioned_at_left_Znth_le__quicksort_range.
            + exact Hleft0.
            + eapply Z.le_trans.
              * exact Hp_right.
              * apply Z.lt_le_incl. exact Hrightlen.
            + exact Hpart.
            + lia.
          - eapply Z.le_trans.
            + eapply partitioned_at_left_Znth_le__quicksort_range.
              * exact Hleft0.
              * eapply Z.le_trans.
                { exact Hp_right. }
                { apply Z.lt_le_incl. exact Hrightlen. }
              * exact Hpart.
              * lia.
            + apply Z.lt_le_incl.
              eapply partitioned_at_right_Znth_lt__quicksort_range.
              * exact Hleft0.
              * exact Hrightlen.
              * exact Hpart.
              * lia.
        }
Qed.
Lemma ordered_full_implies_increasing__quicksort_range :
  forall l,
    (forall i j,
      0 <= i ->
      i <= j ->
      j <= Zlength l - 1 ->
      Znth i l 0 <= Znth j l 0) ->
    increasing l.
Proof.
  induction l; intros Hord; simpl.
  - exact I.
  - destruct l.
    + exact I.
    + split.
      * assert (Hhead : Znth 0 (a :: z :: l) 0 <= Znth 1 (a :: z :: l) 0).
        {
          assert (Hbound0 : 1 <= Zlength (z :: l)).
          {
            rewrite Zlength_cons.
            pose proof Zlength_nonneg l.
            lia.
          }
          assert (Hbound : 1 <= Zlength (a :: z :: l) - 1).
          {
            rewrite Zlength_cons.
            lia.
          }
          specialize (Hord 0 1 ltac:(lia) ltac:(lia) Hbound).
          exact Hord.
        }
        exact Hhead.
      * apply IHl.
        intros i j Hi Hij Hj.
        assert (Hshift :
          Znth (i + 1) (a :: z :: l) 0 <= Znth (j + 1) (a :: z :: l) 0).
        {
          assert (Hj' : j + 1 <= Zlength (a :: z :: l) - 1).
          {
            rewrite Zlength_cons.
            lia.
          }
          apply Hord.
          - lia.
          - lia.
          - exact Hj'.
        }
        rewrite (@Znth_cons Z 0 (i + 1) a (z :: l)) in Hshift by lia.
        rewrite (@Znth_cons Z 0 (j + 1) a (z :: l)) in Hshift by lia.
        replace (i + 1 - 1) with i in Hshift by lia.
        replace (j + 1 - 1) with j in Hshift by lia.
        exact Hshift.
Qed.
Lemma sorted_range_implies_increasing__quicksort_range :
  forall l,
    sorted_range l 0 (Zlength l - 1) ->
    increasing l.
Proof.
  intros l Hsorted.
  apply ordered_full_implies_increasing__quicksort_range.
  intros i j Hi Hij Hj.
  eapply (sorted_range_ordered__quicksort_range l 0 (Zlength l - 1)).
  - lia.
  - pose proof (Zlength_nonneg l).
    lia.
  - exact Hsorted.
  - exact Hi.
  - exact Hij.
  - exact Hj.
Qed.
Lemma dedup_scan_inv_init__discretize_dedup :
  forall src sorted n,
    permutation src sorted ->
    increasing sorted ->
    Zlength src = n ->
    1 <= n ->
    dedup_scan_inv src sorted sorted 0 1.
Proof.
  intros src sorted n Hperm Hinc Hlen Hn.
  unfold dedup_scan_inv, strict_increasing_prefix, same_values_prefix.
  pose proof (Permutation_length Hperm) as Hperm_len.
  assert (Hsorted_len : Zlength sorted = n) by
    (rewrite !Zlength_correct in *; lia).
  repeat split; auto; try lia.
Qed.
Lemma increasing_aux_tail_increasing__discretize_dedup :
  forall l x,
    increasing_aux l x ->
    increasing l.
Proof.
  intros l x Hinc.
  destruct l; simpl; auto.
  destruct Hinc as [_ Hrest].
  exact Hrest.
Qed.
Lemma increasing_aux_head_le_all__discretize_dedup :
  forall l x k,
    increasing_aux l x ->
    0 <= k < Zlength l ->
    x <= Znth k l 0.
Proof.
  induction l; intros x k Hinc Hk.
  - rewrite Zlength_nil in Hk. lia.
  - simpl in Hinc.
    destruct Hinc as [Hxa Hrest].
    destruct (Z.eq_dec k 0) as [-> | Hneq].
    + exact Hxa.
    + rewrite Znth_cons by lia.
      eapply Z.le_trans.
      * exact Hxa.
      * apply IHl with (x := a); auto.
        rewrite Zlength_cons in Hk. lia.
Qed.
Lemma increasing_order__discretize_dedup :
  forall l i j,
    increasing l ->
    0 <= i <= j ->
    j < Zlength l ->
    Znth i l 0 <= Znth j l 0.
Proof.
  induction l as [| a l IH]; intros i j Hinc Hij Hj.
  - rewrite Zlength_nil in Hj. lia.
  - destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    + subst i.
      destruct (Z.eq_dec j 0) as [Hj0 | Hj0].
      * subst j. reflexivity.
      * rewrite (@Znth_cons Z 0 j a l) by lia.
        apply increasing_aux_head_le_all__discretize_dedup with (x := a).
        -- simpl in Hinc. exact Hinc.
        -- rewrite Zlength_cons in Hj. lia.
    + destruct (Z.eq_dec j 0) as [Hj0 | Hj0].
      * subst j. lia.
      * rewrite !(@Znth_cons Z 0) by lia.
        apply IH.
        -- apply increasing_aux_tail_increasing__discretize_dedup with (x := a).
           simpl in Hinc. exact Hinc.
        -- lia.
        -- rewrite Zlength_cons in Hj. lia.
Qed.
Lemma sublist0_extend_in_iff__discretize_dedup :
  forall (l : list Z) n x,
    0 <= n < Zlength l ->
    In x (sublist 0 (n + 1) l) <->
    In x (sublist 0 n l) \/ x = Znth n l 0.
Proof.
  intros l n x Hn.
  rewrite (sublist_split 0 (n + 1) n l) by lia.
  rewrite (@sublist_single Z 0 n l) by lia.
  rewrite in_app_iff.
  simpl.
  firstorder subst; auto.
Qed.
Lemma sublist0_Znth_In__discretize_dedup :
  forall (l : list Z) n i,
    0 <= i < n ->
    n <= Zlength l ->
    In (Znth i l 0) (sublist 0 n l).
Proof.
  intros l n i Hi Hn.
  rewrite (sublist_split 0 n i l) by lia.
  rewrite in_app_iff.
  right.
  rewrite (sublist_split i n (i + 1) l) by lia.
  rewrite in_app_iff.
  left.
  rewrite (@sublist_single Z 0 i l) by lia.
  simpl; auto.
Qed.
Lemma sublist0_In_Znth_exists__discretize_dedup :
  forall (l : list Z) n x,
    0 <= n <= Zlength l ->
    In x (sublist 0 n l) ->
    exists i, 0 <= i < n /\ Znth i l 0 = x.
Proof.
  intros l n x Hn Hin.
  pose proof (In_nth (sublist 0 n l) x 0 Hin) as [k [Hk Hnth]].
  rewrite sublist_length in Hk by lia.
  exists (Z.of_nat k).
  split.
  - lia.
  - rewrite <- Hnth.
    unfold Znth, sublist.
    rewrite skipn_O.
    replace (Z.to_nat (Z.of_nat k)) with k by lia.
    rewrite nth_firstn by lia.
    reflexivity.
Qed.
Lemma sublist0_replace_prefix__discretize_dedup :
  forall (l : list Z) i v,
    0 <= i <= Zlength l ->
    sublist 0 i (replace_Znth i v l) = sublist 0 i l.
Proof.
  intros l i v Hi.
  destruct (Z.eq_dec i (Zlength l)) as [Hi_end | Hi_inside].
  - subst i.
    rewrite replace_Znth_nothing by lia.
    reflexivity.
  - apply (proj2 (list_eq_ext _ _ 0)).
    split.
    + rewrite !Zlength_sublist0; try rewrite Zlength_replace_Znth; lia.
    + intros k Hk.
      rewrite Zlength_sublist0 in Hk by (rewrite Zlength_replace_Znth; lia).
      rewrite !Znth_sublist0 by (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      reflexivity.
Qed.
Lemma sublist0_replace_next_in_iff__discretize_dedup :
  forall (l : list Z) i v x,
    0 <= i < Zlength l ->
    In x (sublist 0 (i + 1) (replace_Znth i v l)) <->
    In x (sublist 0 i l) \/ x = v.
Proof.
  intros l i v x Hi.
  rewrite sublist0_extend_in_iff__discretize_dedup by
    (rewrite Zlength_replace_Znth; lia).
  rewrite sublist0_replace_prefix__discretize_dedup by lia.
  rewrite Znth_replace_Znth_Same by lia.
  tauto.
Qed.
Lemma dedup_scan_inv_step_duplicate__discretize_dedup :
  forall src sorted cur slow fast,
    dedup_scan_inv src sorted cur slow fast ->
    fast < Zlength sorted ->
    Znth fast cur 0 = Znth slow cur 0 ->
    dedup_scan_inv src sorted cur slow (fast + 1).
Proof.
  intros src sorted cur slow fast Hinv Hfast_lt Heq.
  unfold dedup_scan_inv in *.
  destruct Hinv as
    [Hsrc_len [Hcur_len [Hperm [Hinc [Hfast_bounds [Hslow_bounds
    [Hstrict [Hsame [Htail Hlast]]]]]]]]].
  repeat split; auto; try lia.
  - destruct Hstrict as [_ Hstrict_vals].
    apply Hstrict_vals; lia.
  - intro Hin.
    apply (proj2 (sublist0_extend_in_iff__discretize_dedup sorted fast x
      ltac:(lia))).
    left. apply Hsame. exact Hin.
  - intro Hin.
    pose proof (sublist0_extend_in_iff__discretize_dedup sorted fast x
      ltac:(lia)) as Hext.
    destruct (proj1 Hext Hin) as [Hin_old | Hx].
    + apply Hsame. exact Hin_old.
    + subst x.
      assert (Hcur_fast : Znth fast cur 0 = Znth fast sorted 0) by
        (apply Htail; lia).
      replace (Znth fast sorted 0) with (Znth slow cur 0) by congruence.
      apply sublist0_Znth_In__discretize_dedup; lia.
  - intros k Hk.
    apply Htail; lia.
  - replace (fast + 1 - 1) with fast by lia.
    assert (Hcur_fast : Znth fast cur 0 = Znth fast sorted 0) by
      (apply Htail; lia).
    congruence.
Qed.
Lemma dedup_scan_inv_step_new__discretize_dedup :
  forall src sorted cur slow fast,
    dedup_scan_inv src sorted cur slow fast ->
    fast < Zlength sorted ->
    Znth fast cur 0 <> Znth slow cur 0 ->
    dedup_scan_inv src sorted
      (replace_Znth (slow + 1) (Znth fast cur 0) cur)
      (slow + 1) (fast + 1).
Proof.
  intros src sorted cur slow fast Hinv Hfast_lt Hneq.
  unfold dedup_scan_inv in *.
  destruct Hinv as
    [Hsrc_len [Hcur_len [Hperm [Hinc [Hfast_bounds [Hslow_bounds
    [Hstrict [Hsame [Htail Hlast]]]]]]]]].
  assert (Hcur_fast : Znth fast cur 0 = Znth fast sorted 0) by
    (apply Htail; lia).
  assert (Hslow_fast_lt : Znth slow cur 0 < Znth fast cur 0).
  {
    assert (Hsorted_le :
      Znth (fast - 1) sorted 0 <= Znth fast sorted 0).
    {
      eapply increasing_order__discretize_dedup; eauto; lia.
    }
    assert (Hsorted_neq :
      Znth fast sorted 0 <> Znth (fast - 1) sorted 0).
    {
      intro Heq.
      apply Hneq.
      rewrite Hcur_fast, Hlast.
      exact Heq.
    }
    rewrite Hcur_fast, Hlast.
    lia.
  }
  repeat split; auto; try rewrite Zlength_replace_Znth; try lia.
  - destruct Hstrict as [_ Hstrict_vals].
    intros i j Hij Hj.
    destruct (Z_lt_ge_dec j (slow + 1)) as [Hj_old | Hj_new].
    + rewrite !Znth_replace_Znth_Diff by
        (try rewrite Zlength_replace_Znth; lia).
      apply Hstrict_vals; lia.
    + assert (Hj_eq : j = slow + 1) by lia.
      subst j.
      rewrite Znth_replace_Znth_Same by
        (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec i slow) as [Hi_slow | Hi_slow].
      * subst i.
        rewrite Znth_replace_Znth_Diff by
          (try rewrite Zlength_replace_Znth; lia).
        exact Hslow_fast_lt.
      * assert (Hi_lt_slow : i < slow) by lia.
        rewrite Znth_replace_Znth_Diff by
          (try rewrite Zlength_replace_Znth; lia).
        assert (Hprev_lt : Znth i cur 0 < Znth slow cur 0) by
          (apply Hstrict_vals; lia).
        lia.
  - intro Hin.
    pose proof (sublist0_replace_next_in_iff__discretize_dedup cur
      (slow + 1) (Znth fast cur 0) x ltac:(lia)) as Hrep.
    pose proof (sublist0_extend_in_iff__discretize_dedup sorted fast x
      ltac:(lia)) as Hext.
    destruct (proj1 Hrep Hin) as [Hin_old | Hx].
    + apply (proj2 Hext).
      left. apply Hsame. exact Hin_old.
    + apply (proj2 Hext).
      right. subst x. exact Hcur_fast.
  - intro Hin.
    pose proof (sublist0_replace_next_in_iff__discretize_dedup cur
      (slow + 1) (Znth fast cur 0) x ltac:(lia)) as Hrep.
    pose proof (sublist0_extend_in_iff__discretize_dedup sorted fast x
      ltac:(lia)) as Hext.
    destruct (proj1 Hext Hin) as [Hin_old | Hx].
    + apply (proj2 Hrep).
      left. apply Hsame. exact Hin_old.
    + apply (proj2 Hrep).
      right. subst x. symmetry. exact Hcur_fast.
  - intros k Hk.
    rewrite Znth_replace_Znth_Diff by
      (try rewrite Zlength_replace_Znth; lia).
    apply Htail; lia.
  - rewrite Znth_replace_Znth_Same by
      (try rewrite Zlength_replace_Znth; lia).
    replace (fast + 1 - 1) with fast by lia.
    exact Hcur_fast.
Qed.
Lemma dedup_scan_inv_to_discretize_result__discretize_dedup :
  forall src sorted cur slow n,
    dedup_scan_inv src sorted cur slow n ->
    Zlength src = n ->
    1 <= n ->
    discretize_result src n cur (slow + 1).
Proof.
  intros src sorted cur slow n Hinv Hlen Hn.
  unfold dedup_scan_inv in Hinv.
  destruct Hinv as
    [Hsrc_len [Hcur_len [Hperm [Hinc [Hfast_bounds [Hslow_bounds
    [Hstrict [Hsame [Htail Hlast]]]]]]]]].
  assert (Hsorted_len : Zlength sorted = n) by lia.
  assert (Hcur_len_n : Zlength cur = n) by lia.
  assert (Hsame_src : same_values_prefix cur (slow + 1) src n).
  {
    unfold same_values_prefix in *.
    intro x.
    specialize (Hsame x).
    replace (sublist 0 n sorted) with sorted in Hsame by
      (symmetry; apply sublist_self; lia).
    replace (sublist 0 n src) with src by
      (symmetry; apply sublist_self; lia).
    split; intro Hin.
    - eapply Permutation_in.
      + apply Permutation_sym. exact Hperm.
      + apply Hsame. exact Hin.
    - apply Hsame.
      eapply Permutation_in; eauto.
  }
  unfold discretize_result.
  split; [exact Hlen |].
  split; [exact Hcur_len_n |].
  split; [exact Hn |].
  split; [lia |].
  split; [exact Hstrict |].
  split; [exact Hsame_src |].
  split.
  - intros i Hi.
    assert (Hin_src : In (Znth i src 0) (sublist 0 n src)) by
      (apply sublist0_Znth_In__discretize_dedup; lia).
    assert (Hin_cur : In (Znth i src 0) (sublist 0 (slow + 1) cur)) by
      (apply (proj2 (Hsame_src (Znth i src 0))); exact Hin_src).
    destruct (sublist0_In_Znth_exists__discretize_dedup cur (slow + 1)
      (Znth i src 0) ltac:(lia) Hin_cur) as [r [Hr Hz]].
    exists r. split; auto.
  - split.
    + intros r Hr.
      assert (Hin_cur : In (Znth r cur 0) (sublist 0 (slow + 1) cur)) by
        (apply sublist0_Znth_In__discretize_dedup; lia).
      assert (Hin_src : In (Znth r cur 0) (sublist 0 n src)) by
        (apply (proj1 (Hsame_src (Znth r cur 0))); exact Hin_cur).
      destruct (sublist0_In_Znth_exists__discretize_dedup src n
        (Znth r cur 0) ltac:(lia) Hin_src) as [i [Hi Hz]].
      exists i. split; auto.
    + intros i j ri rj Hi Hj Hri Hrj Hri_eq Hrj_eq.
      destruct Hstrict as [_ Hstrict_vals].
      split.
      * intro Hsrc_eq.
        destruct (Z_lt_ge_dec ri rj) as [Hlt | Hge].
        -- pose proof (Hstrict_vals ri rj ltac:(lia) ltac:(lia)) as Hord.
           rewrite Hri_eq, Hrj_eq, Hsrc_eq in Hord. lia.
        -- destruct (Z_lt_ge_dec rj ri) as [Hlt | Hge'].
           ++ pose proof (Hstrict_vals rj ri ltac:(lia) ltac:(lia)) as Hord.
              rewrite Hri_eq, Hrj_eq, Hsrc_eq in Hord. lia.
           ++ lia.
      * intro Hsrc_lt.
        destruct (Z_lt_ge_dec ri rj) as [Hlt | Hge].
        -- exact Hlt.
        -- destruct (Z.eq_dec ri rj) as [Heq | Hneq].
           ++ subst rj. rewrite <- Hri_eq, <- Hrj_eq in Hsrc_lt. lia.
           ++ assert (Hrj_lt_ri : rj < ri) by lia.
              pose proof (Hstrict_vals rj ri ltac:(lia) ltac:(lia)) as Hord.
              rewrite Hri_eq, Hrj_eq in Hord. lia.
Qed.
Lemma midpoint_between_bounds__query_forward_search :
  forall low high,
    low <= high ->
    low <= low + (high - low) ÷ 2 <= high.
Proof.
  intros low high Hle.
  assert (Hnonneg : 0 <= (high - low) ÷ 2) by
    (apply Z.quot_pos; lia).
  assert (Hupper : (high - low) ÷ 2 <= high - low) by
    (apply Z.quot_le_upper_bound; lia).
  lia.
Qed.
Lemma strict_increasing_Znth_lt__query_forward_search :
  forall l i j,
    strict_increasing l ->
    0 <= i < j ->
    j < Zlength l ->
    Znth i l 0 < Znth j l 0.
Proof.
  intros l i j Hinc Hij Hj.
  unfold strict_increasing, strict_increasing_prefix in Hinc.
  destruct Hinc as [_ Hinc].
  apply Hinc; lia.
Qed.
Lemma query_forward_search_inv_init__query_forward_search :
  forall map map_size target,
    0 <= map_size ->
    query_forward_search_inv map map_size target 0 (map_size - 1).
Proof.
  intros map map_size target Hsize.
  unfold query_forward_search_inv.
  repeat split; intros; lia.
Qed.
Lemma query_forward_search_inv_step_right__query_forward_search :
  forall map map_size target low mid high,
    Zlength map = map_size ->
    strict_increasing map ->
    query_forward_search_inv map map_size target low high ->
    low <= mid ->
    mid <= high ->
    Znth mid map 0 < target ->
    query_forward_search_inv map map_size target (mid + 1) high.
Proof.
  intros map map_size target low mid high Hlen Hinc Hinv Hlow_mid Hmid_high Hmid_val.
  unfold query_forward_search_inv in *.
  destruct Hinv as [Hlow0 [Hhigh_size [Hlow_high [Hleft Hright]]]].
  repeat split.
  - lia.
  - lia.
  - lia.
  - intros i Hi.
    destruct (Z_lt_ge_dec i low) as [Hilow | Hlowi].
    + apply Hleft; lia.
    + assert (i <= mid) by lia.
      destruct (Z.eq_dec i mid) as [-> | Hneq].
      * exact Hmid_val.
      * assert (Hiltmid : i < mid) by lia.
        pose proof (strict_increasing_Znth_lt__query_forward_search
                      map i mid Hinc ltac:(lia) ltac:(lia)) as Hlt.
        lia.
  - intros i Hi.
    apply Hright; lia.
Qed.
Lemma query_forward_search_inv_step_left__query_forward_search :
  forall map map_size target low mid high,
    Zlength map = map_size ->
    strict_increasing map ->
    query_forward_search_inv map map_size target low high ->
    low <= mid ->
    mid <= high ->
    Znth mid map 0 >= target ->
    Znth mid map 0 <> target ->
    query_forward_search_inv map map_size target low (mid - 1).
Proof.
  intros map map_size target low mid high Hlen Hinc Hinv Hlow_mid Hmid_high Hmid_ge Hmid_neq.
  unfold query_forward_search_inv in *.
  destruct Hinv as [Hlow0 [Hhigh_size [Hlow_high [Hleft Hright]]]].
  assert (Htarget_mid : target < Znth mid map 0) by lia.
  repeat split.
  - lia.
  - lia.
  - lia.
  - intros i Hi.
    apply Hleft; lia.
  - intros i Hi.
    destruct (Z_lt_ge_dec high i) as [Hhi | Hihigh].
    + apply Hright; lia.
    + assert (mid <= i) by lia.
      destruct (Z.eq_dec i mid) as [-> | Hneq].
      * exact Htarget_mid.
      * assert (Hmidlt : mid < i) by lia.
        pose proof (strict_increasing_Znth_lt__query_forward_search
                      map mid i Hinc ltac:(lia) ltac:(lia)) as Hlt.
        lia.
Qed.
Lemma query_forward_result_not_found__query_forward_search :
  forall map map_size target low high,
    query_forward_search_inv map map_size target low high ->
    low > high ->
    low <= high + 1 ->
    query_forward_result map map_size target (-1).
Proof.
  intros map map_size target low high Hinv Hgt Hgap.
  unfold query_forward_result.
  right.
  split; [| reflexivity].
  unfold query_forward_search_inv in Hinv.
  destruct Hinv as [_ [_ [_ [Hleft Hright]]]].
  intros i Hi Heq.
  destruct (Z_lt_ge_dec i low) as [Hilow | Hlowi].
  - pose proof (Hleft i ltac:(lia)).
    lia.
  - pose proof (Hright i ltac:(lia)).
    lia.
Qed.
Lemma query_forward_result_found_unique__query_forward_search :
  forall map map_size target mid,
    Zlength map = map_size ->
    strict_increasing map ->
    0 <= mid < map_size ->
    Znth mid map 0 = target ->
    query_forward_result map map_size target mid.
Proof.
  intros map map_size target mid Hlen Hinc Hmid Hhit.
  unfold query_forward_result.
  left.
  split.
  - exists mid.
    repeat split; try lia; try assumption; reflexivity.
  - intros j Hj Hjh.
    destruct (Z_lt_ge_dec j mid) as [Hlt | Hge].
    + pose proof (strict_increasing_Znth_lt__query_forward_search
                    map j mid Hinc ltac:(lia) ltac:(lia)) as Horder.
      lia.
    + destruct (Z.eq_dec j mid) as [Heq | Hneq].
      * lia.
      * pose proof (strict_increasing_Znth_lt__query_forward_search
                      map mid j Hinc ltac:(lia) ltac:(lia)) as Horder.
        lia.
Qed.
