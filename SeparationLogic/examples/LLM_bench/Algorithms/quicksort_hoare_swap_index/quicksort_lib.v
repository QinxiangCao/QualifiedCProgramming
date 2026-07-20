Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib MonotonicList VMap.
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

Definition same_outside_range (l l1 : list Z) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 0 = Znth k l 0.

Definition partitioned_at (l : list Z) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => x <= Znth p l 0) (sublist low p l) /\
  Forall (fun x => Znth p l 0 <= x) (sublist (p + 1) (high + 1) l).

Definition range_nondecreasing (l : list Z) (left right : Z) : Prop :=
  forall i j,
    left <= i ->
    i <= j ->
    j <= right ->
    Znth i l 0 <= Znth j l 0.

Definition partition_outer_inv
    (l l1 : list Z) (low high pivot i j : Z) : Prop :=
  Permutation l l1 /\
  same_outside_range l l1 low high /\
  Znth low l1 0 = pivot /\
  low <= i <= j /\
  j <= high /\
  Znth i l1 0 <= pivot /\
  (forall k, low < k < i -> Znth k l1 0 <= pivot) /\
  (forall k, j < k <= high -> pivot <= Znth k l1 0).

Definition partition_right_scan_inv
    (l l1 : list Z) (low high pivot i j : Z) : Prop :=
  Permutation l l1 /\
  same_outside_range l l1 low high /\
  Znth low l1 0 = pivot /\
  low <= i <= j /\
  j <= high /\
  Znth i l1 0 <= pivot /\
  (forall k, low < k < i -> Znth k l1 0 <= pivot) /\
  (forall k, j < k <= high -> pivot <= Znth k l1 0).

Definition partition_left_scan_inv
    (l l1 : list Z) (low high pivot i j : Z) : Prop :=
  Permutation l l1 /\
  same_outside_range l l1 low high /\
  Znth low l1 0 = pivot /\
  low <= i <= j /\
  j <= high /\
  (forall k, low < k < i -> Znth k l1 0 <= pivot) /\
  (forall k, j < k <= high -> pivot <= Znth k l1 0) /\
  (i < j -> Znth j l1 0 < pivot) /\
  (i = j -> Znth i l1 0 <= pivot).

Definition partition_hole_outer_inv
    (l l1 : list Z) (low high pivot i j : Z) : Prop :=
  let completed := replace_Znth i pivot l1 in
  Permutation l completed /\
  same_outside_range l completed low high /\
  low <= i <= j /\
  j <= high /\
  (forall k, low <= k < i -> Znth k completed 0 <= pivot) /\
  (forall k, j < k <= high -> pivot <= Znth k completed 0).

Definition partition_hole_left_scan_inv
    (l l1 : list Z) (low high pivot i j : Z) : Prop :=
  let completed := replace_Znth j pivot l1 in
  Permutation l completed /\
  same_outside_range l completed low high /\
  low <= i <= j /\
  j <= high /\
  (forall k, low <= k < i -> Znth k completed 0 <= pivot) /\
  (forall k, j < k <= high -> pivot <= Znth k completed 0).
Lemma same_outside_range_trans_local :
  forall l l1 l2 left right,
    same_outside_range l l1 left right ->
    same_outside_range l1 l2 left right ->
    same_outside_range l l2 left right.
Proof.
  intros l l1 l2 left right [Hlen1 Heq1] [Hlen2 Heq2].
  split.
  - rewrite Hlen1. exact Hlen2.
  - intros k Hk Hout.
    assert (Hk1 : 0 <= k < Zlength l1) by (rewrite <- Hlen1; exact Hk).
    rewrite (Heq2 k Hk1 Hout).
    apply Heq1; assumption.
Qed.

Lemma Forall_Znth_local :
  forall (P : Z -> Prop) (l : list Z) i,
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l 0).
Proof.
  intros P l i HForall Hrange.
  apply Forall_forall with (x := Znth i l 0) in HForall.
  - exact HForall.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrange.
    lia.
Qed.

Lemma Forall_sublist_by_Znth_local :
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
    assert (Hnil : sublist lo lo l = nil).
    { apply sublist_nil. lia. }
    rewrite Hnil.
    constructor.
  - assert (lo < hi) by lia.
    rewrite (sublist_split lo hi (lo + 1) l).
    2: lia.
    2: {
      split.
      - lia.
      - exact Hhilen.
    }
    rewrite (sublist_single 0 lo l) by lia.
    constructor.
    + simpl. apply Hpoint. lia.
    + apply IHn with (lo := lo + 1) (hi := hi).
      * lia.
      * exact Hhilen.
      * intros k Hk. apply Hpoint. lia.
      * assert (Hn' : Z.to_nat (hi - (lo + 1)) = n) by lia.
        symmetry. exact Hn'.
Qed.

Lemma same_outside_range_swap_inside_local :
  forall (l : list Z) low high i j,
    0 <= low ->
    low <= i <= high ->
    low <= j <= high ->
    high < Zlength l ->
    same_outside_range l
      (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l))
      low high.
Proof.
  intros l low high i j Hlow Hi Hj Hhigh.
  split.
  - rewrite !Zlength_replace_Znth. reflexivity.
  - intros k Hk Hout.
    assert (HiRange : 0 <= i < Zlength l) by lia.
    assert (HjRange : 0 <= j < Zlength l) by lia.
    assert (Hkj : k <> j) by (intro Heq; subst; destruct Hout; lia).
    assert (Hki : k <> i) by (intro Heq; subst; destruct Hout; lia).
    rewrite Znth_replace_Znth_Diff.
    2: { rewrite Zlength_replace_Znth. exact HjRange. }
    2: { rewrite Zlength_replace_Znth. exact Hk. }
    2: { intro Heq. apply Hkj. symmetry. exact Heq. }
    rewrite Znth_replace_Znth_Diff.
    2: exact HiRange.
    2: exact Hk.
    2: { intro Heq. apply Hki. symmetry. exact Heq. }
    reflexivity.
Qed.

Lemma list_split_around_two_indices_local :
  forall (d : Z) (l : list Z) i j,
    0 <= i /\ i < j /\ j < Zlength l ->
    l =
      sublist 0 i l ++
      Znth i l d :: sublist (i + 1) j l ++
      Znth j l d :: sublist (j + 1) (Zlength l) l.
Proof.
  intros d l i j Hij.
  replace l with (sublist 0 (Zlength l) l) at 1.
  2:{ exact (sublist_self l (Zlength l) eq_refl). }
  rewrite (sublist_split 0 (Zlength l) i l) by lia.
  rewrite (sublist_split i (Zlength l) (i + 1) l) by lia.
  rewrite (sublist_single d i l) by lia.
  rewrite (sublist_split (i + 1) (Zlength l) j l) by lia.
  rewrite (sublist_split j (Zlength l) (j + 1) l) by lia.
  rewrite (sublist_single d j l) by lia.
  reflexivity.
Qed.

Lemma sublist_suffix_full_local :
  forall (l : list Z) lo,
    0 <= lo <= Zlength l ->
    sublist lo (Zlength l) l = skipn (Z.to_nat lo) l.
Proof.
  intros l lo Hlo.
  unfold sublist.
  rewrite Zlength_correct.
  rewrite firstn_all2 by lia.
  reflexivity.
Qed.

Lemma replace_Znth_decomp_local :
  forall (d v : Z) (l : list Z) i,
    0 <= i < Zlength l ->
    replace_Znth i v l =
      sublist 0 i l ++ v :: sublist (i + 1) (Zlength l) l.
Proof.
  intros d v l i Hi.
  assert (Hdecomp :
    l = sublist 0 i l ++ Znth i l d :: sublist (i + 1) (Zlength l) l).
  {
    replace l with (sublist 0 (Zlength l) l) at 1.
    2:{
      apply sublist_self.
      lia.
    }
    rewrite (sublist_split 0 (Zlength l) (i + 1) l) by lia.
    rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite (sublist_single d i l) by lia.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hdecomp at 1.
  rewrite replace_Znth_app_r by (rewrite Zlength_sublist by lia; lia).
  rewrite replace_Znth_nothing by (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  replace (i - (i - 0)) with 0 by lia.
  unfold replace_Znth.
  simpl.
  reflexivity.
Qed.

Lemma swap_Znth_perm_local :
  forall (l : list Z) i j,
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)).
Proof.
  intros l i j (Hi0 & Hijlt & Hjlen).
  set (a := Znth i l 0).
  set (b := Znth j l 0).
  set (p := sublist 0 i l).
  set (m := sublist (i + 1) j l).
  set (s := sublist (j + 1) (Zlength l) l).
  assert (Hl : l = p ++ a :: m ++ b :: s).
  {
    subst a b p m s.
    apply list_split_around_two_indices_local.
    repeat split; lia.
  }
  assert (Htail :
    sublist (i + 1) (Zlength l) l = m ++ b :: s).
  {
    subst b m s.
    rewrite (sublist_split (i + 1) (Zlength l) j l) by lia.
    rewrite (sublist_split j (Zlength l) (j + 1) l) by lia.
    rewrite (sublist_single 0 j l) by lia.
    reflexivity.
  }
  assert (Hreplace_i :
    replace_Znth i b l = p ++ b :: m ++ b :: s).
  {
    rewrite (replace_Znth_decomp_local 0 b l i) by lia.
    rewrite Htail.
    reflexivity.
  }
  assert (Hlen_p : Zlength p = i).
  {
    subst p.
    rewrite Zlength_sublist by lia.
    lia.
  }
  assert (Hlen_bm : Zlength (b :: m) = j - i).
  {
    subst m.
    rewrite Zlength_cons.
    rewrite Zlength_sublist by lia.
    lia.
  }
  assert (Hswap :
    replace_Znth j a (replace_Znth i b l) = p ++ b :: m ++ a :: s).
  {
    rewrite Hreplace_i.
    change (p ++ b :: m ++ b :: s) with (p ++ ((b :: m) ++ b :: s)).
    rewrite replace_Znth_app_r by (rewrite Hlen_p; lia).
    rewrite replace_Znth_nothing by (rewrite Hlen_p; lia).
    rewrite Hlen_p.
    rewrite replace_Znth_app_r by (rewrite Hlen_bm; lia).
    rewrite replace_Znth_nothing by (rewrite Hlen_bm; lia).
    rewrite Hlen_bm.
    replace (j - i - (j - i)) with 0 by lia.
    unfold replace_Znth.
    simpl.
    reflexivity.
  }
  rewrite Hswap, Hl.
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.

Lemma partition_swap_left_scan_to_outer_inv :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l ->
    partition_left_scan_inv l l1 low high pivot i j ->
    i < j ->
    Znth i l1 0 > pivot ->
    partition_outer_inv l
      (replace_Znth j (Znth i l1 0) (replace_Znth i (Znth j l1 0) l1))
      low high pivot i j.
Proof.
  intros l l1 low high pivot i j Hlow Hhigh
    (Hperm & (Hlen & Hsame) & Hpivot & Hbounds & Hjhigh & Hmid & Hright & Hjlt & _)
    Hij Higt.
  assert (HiRange : 0 <= i < Zlength l1).
  { rewrite <- Hlen. lia. }
  assert (HjRange : 0 <= j < Zlength l1).
  { rewrite <- Hlen. lia. }
  assert (Hlow_lt_i : low < i).
  {
    destruct (Z.eq_dec low i) as [-> | Hneq].
    - rewrite Hpivot in Higt. lia.
    - lia.
  }
  repeat split.
  - eapply Permutation_trans.
    + exact Hperm.
    + apply swap_Znth_perm_local. lia.
  - rewrite !Zlength_replace_Znth.
    exact Hlen.
  - intros k Hk Hout.
    assert (Hk1 : 0 <= k < Zlength l1).
    { rewrite <- Hlen. exact Hk. }
    assert (Hki : k <> i).
    { intro Heq. subst. destruct Hout; lia. }
    assert (Hkj : k <> j).
    { intro Heq. subst. destruct Hout; lia. }
    rewrite Znth_replace_Znth_Diff.
    2:{ rewrite Zlength_replace_Znth. exact HjRange. }
    2:{ rewrite Zlength_replace_Znth. exact Hk1. }
    2:{ intro Heq. apply Hkj. symmetry. exact Heq. }
    rewrite Znth_replace_Znth_Diff.
    2:{ exact HiRange. }
    2:{ exact Hk1. }
    2:{ intro Heq. apply Hki. symmetry. exact Heq. }
    apply Hsame; assumption.
  - remember (replace_Znth i (Znth j l1 0) l1) as l2 eqn:Hl2.
    assert (HlowRange : 0 <= low < Zlength l1).
    { rewrite <- Hlen. lia. }
    assert (Hlow_outer :
      Znth low (replace_Znth j (Znth i l1 0) l2) 0 = Znth low l2 0).
    {
      apply Znth_replace_Znth_Diff.
      - rewrite Hl2. rewrite Zlength_replace_Znth. exact HjRange.
      - rewrite Hl2. rewrite Zlength_replace_Znth. exact HlowRange.
      - intro Heq. subst. lia.
    }
    transitivity (Znth low l2 0).
    { exact Hlow_outer. }
    rewrite Hl2.
    assert (Hlow_inner :
      Znth low (replace_Znth i (Znth j l1 0) l1) 0 = Znth low l1 0).
    {
      apply Znth_replace_Znth_Diff.
      - exact HiRange.
      - rewrite <- Hlen. lia.
      - intro Heq. subst. lia.
    }
    transitivity (Znth low l1 0).
    { exact Hlow_inner. }
    exact Hpivot.
  - lia.
  - lia.
  - exact Hjhigh.
  - rewrite Znth_replace_Znth_Diff.
    2:{ rewrite Zlength_replace_Znth. exact HjRange. }
    2:{ rewrite Zlength_replace_Znth. exact HiRange. }
    2:{ intro Heq. subst. lia. }
    rewrite Znth_replace_Znth_Same by exact HiRange.
    specialize (Hjlt Hij).
    lia.
  - intros k Hk.
    assert (Hk1 : 0 <= k < Zlength l1) by lia.
    rewrite Znth_replace_Znth_Diff.
    2:{ rewrite Zlength_replace_Znth. exact HjRange. }
    2:{ rewrite Zlength_replace_Znth. exact Hk1. }
    2:{ intro Heq. subst. lia. }
    rewrite Znth_replace_Znth_Diff.
    2:{ exact HiRange. }
    2:{ exact Hk1. }
    2:{ intro Heq. subst. lia. }
    apply Hmid. exact Hk.
  - intros k Hk.
    assert (Hk1 : 0 <= k < Zlength l1).
    { rewrite <- Hlen. lia. }
    rewrite Znth_replace_Znth_Diff.
    2:{ rewrite Zlength_replace_Znth. exact HjRange. }
    2:{ rewrite Zlength_replace_Znth. exact Hk1. }
    2:{ intro Heq. subst. lia. }
    rewrite Znth_replace_Znth_Diff.
    2:{ exact HiRange. }
    2:{ exact Hk1. }
    2:{ intro Heq. subst. lia. }
    apply Hright. exact Hk.
Qed.

Lemma partition_outer_exit_swap_yields_partitioned_at :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l ->
    partition_outer_inv l l1 low high pivot i j ->
    i >= j ->
    partitioned_at
      (replace_Znth i (Znth low l1 0) (replace_Znth low (Znth i l1 0) l1))
      low high i.
Proof.
  intros l l1 low high pivot i j Hlow Hhigh
    (Hperm & Hsame & Hpivot & [Hloi Hij] & Hjhigh & Hile & Hmid & Hright)
    Hexit.
  assert (Hij_eq : i = j) by lia.
  subst j.
  assert (HiRange : 0 <= i < Zlength l1).
  { destruct Hsame as [Hlen _]. rewrite <- Hlen. lia. }
  set (l2 := replace_Znth i (Znth low l1 0) (replace_Znth low (Znth i l1 0) l1)).
  assert (Hpiv_new : Znth i l2 0 = pivot).
  {
    subst l2.
    destruct (Z.eq_dec low i) as [Heq | Hneq].
    - subst i.
      rewrite replace_Znth_Znth by exact HiRange.
      rewrite replace_Znth_Znth by exact HiRange.
      exact Hpivot.
    - rewrite Znth_replace_Znth_Same.
      2:{ rewrite Zlength_replace_Znth. exact HiRange. }
      exact Hpivot.
  }
  split.
  - lia.
  - split.
	    + apply Forall_sublist_by_Znth_local.
	      * lia.
	      * subst l2.
	        rewrite !Zlength_replace_Znth.
	        destruct Hsame as [Hlen _].
	        rewrite <- Hlen.
	        lia.
      * intros k Hk.
        rewrite Hpiv_new.
        destruct (Z.eq_dec k low) as [-> | Hneq_low].
	        -- subst l2.
	           destruct (Z.eq_dec low i) as [Heq | Hneq].
	           ++ subst i. lia.
	           ++ rewrite Znth_replace_Znth_Diff.
	              2:{ rewrite Zlength_replace_Znth. exact HiRange. }
	              2:{ rewrite Zlength_replace_Znth. lia. }
	              2:{ intro Heq; apply Hneq; symmetry; exact Heq. }
	              rewrite Znth_replace_Znth_Same by lia.
	              exact Hile.
	        -- assert (Hki : k <> i) by lia.
	           subst l2.
	           rewrite Znth_replace_Znth_Diff.
	           2:{ rewrite Zlength_replace_Znth. exact HiRange. }
	           2:{ rewrite Zlength_replace_Znth. lia. }
	           2:{ intro Heq; apply Hki; symmetry; exact Heq. }
	           rewrite Znth_replace_Znth_Diff.
	           2:{ lia. }
	           2:{ lia. }
	           2:{ intro Heq; apply Hneq_low; symmetry; exact Heq. }
	           apply Hmid. lia.
	    + apply Forall_sublist_by_Znth_local.
	      * lia.
	      * subst l2.
	        rewrite !Zlength_replace_Znth.
	        destruct Hsame as [Hlen _].
	        rewrite <- Hlen.
	        lia.
      * intros k Hk.
        rewrite Hpiv_new.
	        assert (Hki : k <> i) by lia.
	        assert (Hklow : k <> low) by lia.
	        subst l2.
	        rewrite Znth_replace_Znth_Diff.
	        2:{ rewrite Zlength_replace_Znth. exact HiRange. }
	        2:{ rewrite Zlength_replace_Znth. destruct Hsame as [Hlen _]. rewrite <- Hlen. lia. }
	        2:{ intro Heq; apply Hki; symmetry; exact Heq. }
	        rewrite Znth_replace_Znth_Diff.
	        2:{ destruct Hsame as [Hlen _]. rewrite <- Hlen. lia. }
	        2:{ destruct Hsame as [Hlen _]. rewrite <- Hlen. lia. }
        2:{ intro Heq; apply Hklow; symmetry; exact Heq. }
        apply Hright. lia.
Qed.

Lemma range_nondecreasing_full_to_increasing :
  forall l,
    range_nondecreasing l 0 (Zlength l - 1) ->
    increasing l.
Proof.
  intros l Hrange.
  apply (proj1 (mono_nondec_iff_increasing l)).
  unfold mono_nondec.
  intros i j Hi Hij Hj.
  apply Hrange; lia.
Qed.

Lemma same_outside_range_weaken_local :
  forall l l1 left1 right1 left2 right2,
    left2 <= left1 ->
    right1 <= right2 ->
    same_outside_range l l1 left1 right1 ->
    same_outside_range l l1 left2 right2.
Proof.
  intros l l1 left1 right1 left2 right2 Hleft Hright [Hlen Heq].
  split.
  - exact Hlen.
  - intros k Hk Hout.
    apply Heq; try assumption.
    destruct Hout as [Hout | Hout].
    + left. lia.
    + right. lia.
Qed.

Lemma Forall_permutation_local :
  forall (P : Z -> Prop) l1 l2,
    Permutation l1 l2 ->
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

Lemma sublist_eq_from_Znth_local :
  forall l1 l2 lo hi,
    Zlength l1 = Zlength l2 ->
    0 <= lo <= hi ->
    hi <= Zlength l1 ->
    (forall k, lo <= k < hi -> Znth k l1 0 = Znth k l2 0) ->
    sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros l1 l2 lo hi Hlen Hlohi Hhilen Hpoint.
  apply (proj2 (list_eq_ext (sublist lo hi l1) (sublist lo hi l2) 0)).
  split.
  - rewrite !Zlength_sublist by lia.
    lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    {
      rewrite Zlength_sublist in Hi by lia.
      exact Hi.
    }
    rewrite (@Znth_sublist_lt Z 0 lo hi l1 i).
    2: exact Hlohi.
    2: exact Hhilen.
    2: exact Hi'.
    rewrite (@Znth_sublist_lt Z 0 lo hi l2 i).
    2: exact Hlohi.
    2: { rewrite <- Hlen. exact Hhilen. }
    2: exact Hi'.
    apply Hpoint.
    lia.
Qed.

Lemma list_decompose_sublist_local :
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

Lemma same_outside_range_prefix_local :
  forall l l1 left right,
    same_outside_range l l1 left right ->
    0 <= left <= Zlength l ->
    sublist 0 left l1 = sublist 0 left l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  apply sublist_eq_from_Znth_local.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + lia.
    + left. lia.
Qed.

Lemma same_outside_range_suffix_local :
  forall l l1 left right,
    same_outside_range l l1 left right ->
    0 <= right + 1 <= Zlength l ->
    sublist (right + 1) (Zlength l1) l1 = sublist (right + 1) (Zlength l) l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  rewrite <- Hlen.
  apply sublist_eq_from_Znth_local.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + rewrite Hlen. lia.
    + right. lia.
Qed.

Lemma middle_permutation_of_same_outside_local :
  forall l l1 left right,
    Permutation l l1 ->
    same_outside_range l l1 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength l ->
    Permutation (sublist left (right + 1) l) (sublist left (right + 1) l1).
Proof.
  intros l l1 left right Hperm Hsame Hlr Hlenr.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen _].
  pose proof (same_outside_range_prefix_local _ _ _ _ Hsame0) as Hpre.
  pose proof (same_outside_range_suffix_local _ _ _ _ Hsame0) as Hsuf.
  rewrite (list_decompose_sublist_local l left (right + 1)) in Hperm by lia.
  assert (Hlenr1 : right + 1 <= Zlength l1) by (rewrite <- Hlen; exact Hlenr).
  rewrite (list_decompose_sublist_local l1 left (right + 1)) in Hperm by lia.
  specialize (Hpre ltac:(lia)).
  specialize (Hsuf ltac:(lia)).
  rewrite Hpre, Hsuf in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.

Lemma partitioned_at_preserved_by_left_local :
  forall l l1 left right p,
    Permutation l l1 ->
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
      eapply Forall_permutation_local.
      * assert (Hmid :
            Permutation (sublist left (p - 1 + 1) l)
                        (sublist left (p - 1 + 1) l1)).
        {
          eapply middle_permutation_of_same_outside_local
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
      apply Forall_sublist_by_Znth_local; try lia.
      intros k Hk.
      rewrite Heq by (try lia; right; lia).
      assert (Hk' : 0 <= k - (p + 1) < Zlength (sublist (p + 1) (right + 1) l)).
      {
        rewrite Zlength_sublist by lia.
        lia.
      }
      pose proof (Forall_Znth_local
                    (fun x => Znth p l 0 <= x)
                    (sublist (p + 1) (right + 1) l)
                    (k - (p + 1))
                    Hright Hk') as Hz.
      rewrite (@Znth_sublist_lt Z 0 (p + 1) (right + 1) l (k - (p + 1))) in Hz.
      2: lia.
      2: lia.
      2: {
        rewrite Zlength_sublist in Hk' by lia.
        exact Hk'.
      }
      replace (p + 1 + (k - (p + 1))) with k in Hz by lia.
      exact Hz.
Qed.

Lemma partitioned_at_preserved_by_right_local :
  forall l l1 left right p,
    Permutation l l1 ->
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
        apply sublist_eq_from_Znth_local.
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
      eapply Forall_permutation_local.
      * assert (Hmid :
            Permutation (sublist (p + 1) (right + 1) l)
                        (sublist (p + 1) (right + 1) l1)).
        {
          eapply middle_permutation_of_same_outside_local
            with (left := p + 1) (right := right).
          - exact Hperm.
          - exact (conj Hlen' Heq).
          - lia.
          - lia.
        }
        exact Hmid.
      * exact Hright.
Qed.

Lemma partitioned_at_left_Znth_le_local :
  forall l left right p k,
    0 <= left ->
    p <= Zlength l ->
    partitioned_at l left right p ->
    left <= k < p ->
    Znth k l 0 <= Znth p l 0.
Proof.
  intros l left right p k Hleft0 Hp Hpart Hk.
  destruct Hpart as [_ [Hleft _]].
  pose proof (Forall_Znth_local
                (fun x => x <= Znth p l 0)
                (sublist left p l)
                (k - left)
                Hleft) as Hz.
  assert (Hk' : 0 <= k - left < Zlength (sublist left p l)).
  {
    rewrite Zlength_sublist by lia.
    lia.
  }
  specialize (Hz Hk').
  rewrite (@Znth_sublist_lt Z 0 left p l (k - left)) in Hz.
  2: lia.
  2: exact Hp.
  2: {
    rewrite Zlength_sublist in Hk' by lia.
    exact Hk'.
  }
  replace (left + (k - left)) with k in Hz by lia.
  exact Hz.
Qed.

Lemma partitioned_at_right_Znth_ge_local :
  forall l left right p k,
    0 <= left ->
    right < Zlength l ->
    partitioned_at l left right p ->
    p < k <= right ->
    Znth p l 0 <= Znth k l 0.
Proof.
  intros l left right p k Hleft0 Hrightlen Hpart Hk.
  destruct Hpart as [Hrange [_ Hright]].
  pose proof (Forall_Znth_local
                (fun x => Znth p l 0 <= x)
                (sublist (p + 1) (right + 1) l)
                (k - (p + 1))
                Hright) as Hz.
  assert (Hk' : 0 <= k - (p + 1) < Zlength (sublist (p + 1) (right + 1) l)).
  {
    rewrite Zlength_sublist by lia.
    lia.
  }
  specialize (Hz Hk').
  rewrite (@Znth_sublist_lt Z 0 (p + 1) (right + 1) l (k - (p + 1))) in Hz.
  2: lia.
  2: lia.
  2: {
    rewrite Zlength_sublist in Hk' by lia.
    exact Hk'.
  }
  replace (p + 1 + (k - (p + 1))) with k in Hz by lia.
  exact Hz.
Qed.

Lemma range_nondecreasing_ext_local :
  forall l l1 left right,
    Zlength l = Zlength l1 ->
    (forall k, left <= k <= right -> Znth k l1 0 = Znth k l 0) ->
    range_nondecreasing l left right ->
    range_nondecreasing l1 left right.
Proof.
  intros l l1 left right Hlen Heq Hrange i j Hi Hij Hj.
  rewrite (Heq i) by lia.
  rewrite (Heq j) by lia.
  apply Hrange; assumption.
Qed.

Lemma quicksort_partition_combine_right_only_local :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    p = left ->
    partitioned_at l left right p ->
    range_nondecreasing l (p + 1) right ->
    range_nondecreasing l left right.
Proof.
  intros l left right p Hleft0 Hrightlen Hp Hpart Hright_sorted i j Hi Hij Hj.
  subst p.
  destruct (Z.eq_dec i left) as [-> | Hi_neq].
  - destruct (Z.eq_dec j left) as [-> | Hj_neq].
    + apply Z.le_refl.
    + eapply (partitioned_at_right_Znth_ge_local l left right left j).
      * exact Hleft0.
      * exact Hrightlen.
      * exact Hpart.
      * lia.
  - assert (left < i) by lia.
    assert (left < j) by lia.
    apply Hright_sorted; lia.
Qed.

Lemma quicksort_partition_combine_left_only_local :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    p = right ->
    partitioned_at l left right p ->
    range_nondecreasing l left (p - 1) ->
    range_nondecreasing l left right.
Proof.
  intros l left right p Hleft0 Hrightlen Hp Hpart Hleft_sorted i j Hi Hij Hj.
  subst p.
  destruct (Z.eq_dec j right) as [-> | Hj_neq].
  - destruct (Z.eq_dec i right) as [-> | Hi_neq].
    + apply Z.le_refl.
    + eapply (partitioned_at_left_Znth_le_local l left right right i).
      * exact Hleft0.
      * lia.
      * exact Hpart.
      * lia.
  - assert (j < right) by lia.
    apply Hleft_sorted; lia.
Qed.

Lemma quicksort_partition_combine_both_sides_local :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    left <= p <= right ->
    partitioned_at l left right p ->
    range_nondecreasing l left (p - 1) ->
    range_nondecreasing l (p + 1) right ->
    range_nondecreasing l left right.
Proof.
  intros l left right p Hleft0 Hrightlen HpRange Hpart Hleft_sorted Hright_sorted
         i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j p) as [Hjp | Hjp].
  - apply Hleft_sorted; lia.
  - destruct (Z.eq_dec j p) as [-> | Hjp_neq].
    + destruct (Z.eq_dec i p) as [-> | Hip_neq].
      * apply Z.le_refl.
      * eapply (partitioned_at_left_Znth_le_local l left right p i).
        -- exact Hleft0.
        -- lia.
        -- exact Hpart.
        -- lia.
    + assert (p < j) by lia.
      destruct (Z.eq_dec i p) as [-> | Hip_neq].
      * eapply (partitioned_at_right_Znth_ge_local l left right p j).
        -- exact Hleft0.
        -- exact Hrightlen.
        -- exact Hpart.
        -- lia.
      * destruct (Z_lt_ge_dec i p) as [Hip_lt | Hip_ge].
        -- eapply Z.le_trans.
           ++ eapply (partitioned_at_left_Znth_le_local l left right p i).
              ** exact Hleft0.
              ** lia.
              ** exact Hpart.
              ** lia.
           ++ eapply (partitioned_at_right_Znth_ge_local l left right p j).
              ** exact Hleft0.
              ** exact Hrightlen.
              ** exact Hpart.
              ** lia.
        -- assert (p < i) by lia.
           apply Hright_sorted; lia.
Qed.

Lemma replace_nth_comm_Z_local :
  forall ni nj (l: list Z) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros ni nj l a b Hneq.
  revert nj l Hneq.
  induction ni; intros nj l Hneq; destruct l as [|x xs]; simpl.
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

Lemma replace_Znth_comm_local :
  forall (l: list Z) i j (a b: Z),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm_Z_local.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma replace_nth_twice_Z_local :
  forall n (l: list Z) a b,
    replace_nth n (replace_nth n l a) b =
    replace_nth n l b.
Proof.
  induction n; intros l a b; destruct l as [|x xs]; simpl; auto.
  f_equal.
  apply IHn.
Qed.

Lemma replace_Znth_twice_local :
  forall (l: list Z) i a b,
    replace_Znth i b (replace_Znth i a l) =
    replace_Znth i b l.
Proof.
  intros l i a b.
  unfold replace_Znth.
  apply replace_nth_twice_Z_local.
Qed.

Lemma partition_hole_outer_scan_decrease_j :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l ->
    partition_hole_outer_inv l l1 low high pivot i j ->
    i < j ->
    Znth j l1 0 > pivot ->
    partition_hole_outer_inv l l1 low high pivot i (j - 1).
Proof.
  intros l l1 low high pivot i j Hlow Hhigh Hinv Hij Hjgt.
  unfold partition_hole_outer_inv in *.
  destruct Hinv as [Hperm [Hsame [[Hloi Hijle] [Hjhi [Hleft Hright]]]]].
  destruct Hsame as [Hlen Hsame].
  assert (Hlen_l1 : Zlength l = Zlength l1).
  { rewrite Hlen. rewrite Zlength_replace_Znth. reflexivity. }
  assert (HjRange : 0 <= j < Zlength l1) by (rewrite <- Hlen_l1; lia).
  split; [exact Hperm|].
  split; [exact (conj Hlen Hsame)|].
  split; [lia|].
  split; [lia|].
  split; [exact Hleft|].
  intros k Hk.
  destruct (Z.eq_dec k j) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Diff by lia.
    lia.
  - apply Hright. lia.
Qed.

Lemma partition_hole_left_scan_increase_i :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l ->
    partition_hole_left_scan_inv l l1 low high pivot i j ->
    i < j ->
    Znth i l1 0 <= pivot ->
    partition_hole_left_scan_inv l l1 low high pivot (i + 1) j.
Proof.
  intros l l1 low high pivot i j Hlow Hhigh Hinv Hij Hile.
  unfold partition_hole_left_scan_inv in *.
  destruct Hinv as [Hperm [Hsame [[Hloi Hijle] [Hjhi [Hleft Hright]]]]].
  destruct Hsame as [Hlen Hsame].
  assert (Hlen_l1 : Zlength l = Zlength l1).
  { rewrite Hlen. rewrite Zlength_replace_Znth. reflexivity. }
  assert (HiRange : 0 <= i < Zlength l1) by (rewrite <- Hlen_l1; lia).
  split; [exact Hperm|].
  split; [exact (conj Hlen Hsame)|].
  split; [lia|].
  split; [lia|].
  split.
  - intros k Hk.
    destruct (Z.eq_dec k i) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Diff by lia.
      exact Hile.
    + apply Hleft. lia.
  - exact Hright.
Qed.

Lemma partition_hole_outer_fill_left_to_left_scan :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l ->
    partition_hole_outer_inv l l1 low high pivot i j ->
    i < j ->
    Znth j l1 0 <= pivot ->
    partition_hole_left_scan_inv l
      (replace_Znth i (Znth j l1 0) l1) low high pivot (i + 1) j.
Proof.
  intros l l1 low high pivot i j Hlow Hhigh Hinv Hij Hjle.
  unfold partition_hole_outer_inv in Hinv.
  unfold partition_hole_left_scan_inv.
  destruct Hinv as [Hperm [Hsame [[Hloi Hijle] [Hjhi [Hleft Hright]]]]].
  destruct Hsame as [Hlen Hsame].
  set (old := replace_Znth i pivot l1).
  set (new := replace_Znth j pivot (replace_Znth i (Znth j l1 0) l1)).
  assert (Hlen_l1 : Zlength l = Zlength l1).
  { rewrite Hlen. subst old. rewrite Zlength_replace_Znth. reflexivity. }
  assert (HiRange : 0 <= i < Zlength l1) by (rewrite <- Hlen_l1; lia).
  assert (HjRange : 0 <= j < Zlength l1) by (rewrite <- Hlen_l1; lia).
  assert (HoldLen : Zlength old = Zlength l1).
  { subst old. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hold_i : Znth i old 0 = pivot).
  { subst old. rewrite Znth_replace_Znth_Same by exact HiRange. reflexivity. }
  assert (Hold_j : Znth j old 0 = Znth j l1 0).
  { subst old. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  assert (Hnew_swap :
    new =
      replace_Znth j (Znth i old 0)
        (replace_Znth i (Znth j old 0) old)).
  {
    subst new old.
    rewrite Hold_i, Hold_j.
    rewrite replace_Znth_twice_local.
    reflexivity.
  }
  split.
  - rewrite Hnew_swap.
    eapply Permutation_trans.
    + exact Hperm.
    + apply swap_Znth_perm_local. rewrite HoldLen. lia.
  - split.
    + eapply same_outside_range_trans_local.
      * exact (conj Hlen Hsame).
      * rewrite Hnew_swap.
        apply same_outside_range_swap_inside_local; try lia.
    + split; [lia|].
      split; [lia|].
      split.
      * intros k Hk.
        destruct (Z.eq_dec k i) as [-> | Hneq].
        -- subst new.
           rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           rewrite Znth_replace_Znth_Same by exact HiRange.
           exact Hjle.
        -- subst new.
           rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           assert (Hkold : Znth k old 0 = Znth k l1 0).
           { subst old. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
           rewrite <- Hkold.
           apply Hleft. lia.
      * intros k Hk.
        subst new.
        rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
        rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
        assert (Hkold : Znth k old 0 = Znth k l1 0).
        { subst old. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
        rewrite <- Hkold.
        apply Hright. lia.
Qed.

Lemma partition_hole_left_fill_right_to_outer :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l ->
    partition_hole_left_scan_inv l l1 low high pivot i j ->
    i < j ->
    Znth i l1 0 > pivot ->
    partition_hole_outer_inv l
      (replace_Znth j (Znth i l1 0) l1) low high pivot i (j - 1).
Proof.
  intros l l1 low high pivot i j Hlow Hhigh Hinv Hij Higt.
  unfold partition_hole_left_scan_inv in Hinv.
  unfold partition_hole_outer_inv.
  destruct Hinv as [Hperm [Hsame [[Hloi Hijle] [Hjhi [Hleft Hright]]]]].
  destruct Hsame as [Hlen Hsame].
  set (old := replace_Znth j pivot l1).
  set (new := replace_Znth i pivot (replace_Znth j (Znth i l1 0) l1)).
  assert (Hlen_l1 : Zlength l = Zlength l1).
  { rewrite Hlen. subst old. rewrite Zlength_replace_Znth. reflexivity. }
  assert (HiRange : 0 <= i < Zlength l1) by (rewrite <- Hlen_l1; lia).
  assert (HjRange : 0 <= j < Zlength l1) by (rewrite <- Hlen_l1; lia).
  assert (HoldLen : Zlength old = Zlength l1).
  { subst old. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hold_i : Znth i old 0 = Znth i l1 0).
  { subst old. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  assert (Hold_j : Znth j old 0 = pivot).
  { subst old. rewrite Znth_replace_Znth_Same by exact HjRange. reflexivity. }
  assert (Hnew_swap :
    new =
      replace_Znth j (Znth i old 0)
        (replace_Znth i (Znth j old 0) old)).
  {
    subst new old.
    rewrite Hold_i, Hold_j.
    rewrite (replace_Znth_comm_local
      (replace_Znth j pivot l1) i j pivot (Znth i l1 0)) by lia.
    rewrite replace_Znth_twice_local.
    reflexivity.
  }
  split.
  - rewrite Hnew_swap.
    eapply Permutation_trans.
    + exact Hperm.
    + apply swap_Znth_perm_local. rewrite HoldLen. lia.
  - split.
    + eapply same_outside_range_trans_local.
      * exact (conj Hlen Hsame).
      * rewrite Hnew_swap.
        apply same_outside_range_swap_inside_local; try lia.
    + split; [lia|].
      split; [lia|].
      split.
      * intros k Hk.
        subst new.
        rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
        rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
        assert (Hkold : Znth k old 0 = Znth k l1 0).
        { subst old. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
        rewrite <- Hkold.
        apply Hleft. lia.
      * intros k Hk.
        destruct (Z.eq_dec k j) as [-> | Hneq].
        -- subst new.
           rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           rewrite Znth_replace_Znth_Same by exact HjRange.
           lia.
        -- subst new.
           rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           assert (Hkold : Znth k old 0 = Znth k l1 0).
           { subst old. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
           rewrite <- Hkold.
           apply Hright. lia.
Qed.

Lemma partition_hole_outer_exit_yields_partitioned_at :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l ->
    partition_hole_outer_inv l l1 low high pivot i j ->
    i >= j ->
    partitioned_at (replace_Znth i pivot l1) low high i.
Proof.
  intros l l1 low high pivot i j Hlow Hhigh Hinv Hexit.
  unfold partition_hole_outer_inv in Hinv.
  destruct Hinv as [Hperm [Hsame [[Hloi Hij] [Hjhi [Hleft Hright]]]]].
  assert (Hij_eq : i = j) by lia.
  subst j.
  destruct Hsame as [Hlen Hsame].
  assert (HcompLen : Zlength (replace_Znth i pivot l1) = Zlength l).
  { symmetry. exact Hlen. }
  assert (HiRange : 0 <= i < Zlength (replace_Znth i pivot l1)).
  { rewrite <- Hlen. lia. }
  assert (Hpivot : Znth i (replace_Znth i pivot l1) 0 = pivot).
  { rewrite Znth_replace_Znth_Same; try lia.
    rewrite Zlength_replace_Znth in HiRange. exact HiRange. }
  split; [lia|split].
  - apply Forall_sublist_by_Znth_local.
    + lia.
    + rewrite HcompLen. lia.
    + intros k Hk. rewrite Hpivot. apply Hleft. lia.
  - apply Forall_sublist_by_Znth_local.
    + lia.
    + rewrite HcompLen. lia.
    + intros k Hk. rewrite Hpivot. apply Hright. lia.
Qed.

Lemma partition_hole_left_exit_yields_partitioned_at :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l ->
    partition_hole_left_scan_inv l l1 low high pivot i j ->
    i >= j ->
    partitioned_at (replace_Znth i pivot l1) low high i.
Proof.
  intros l l1 low high pivot i j Hlow Hhigh Hinv Hexit.
  unfold partition_hole_left_scan_inv in Hinv.
  destruct Hinv as [Hperm [Hsame [[Hloi Hij] [Hjhi [Hleft Hright]]]]].
  assert (Hij_eq : i = j) by lia.
  subst j.
  destruct Hsame as [Hlen Hsame].
  assert (HcompLen : Zlength (replace_Znth i pivot l1) = Zlength l).
  { symmetry. exact Hlen. }
  assert (HiRange : 0 <= i < Zlength (replace_Znth i pivot l1)).
  { rewrite <- Hlen. lia. }
  assert (Hpivot : Znth i (replace_Znth i pivot l1) 0 = pivot).
  { rewrite Znth_replace_Znth_Same; try lia.
    rewrite Zlength_replace_Znth in HiRange. exact HiRange. }
  split; [lia|split].
  - apply Forall_sublist_by_Znth_local.
    + lia.
    + rewrite HcompLen. lia.
    + intros k Hk. rewrite Hpivot. apply Hleft. lia.
  - apply Forall_sublist_by_Znth_local.
    + lia.
    + rewrite HcompLen. lia.
    + intros k Hk. rewrite Hpivot. apply Hright. lia.
Qed.

Lemma quicksort_partition_combine_right_guard_local :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    left <= p <= right ->
    p <= left + 1 ->
    partitioned_at l left right p ->
    range_nondecreasing l (p + 1) right ->
    range_nondecreasing l left right.
Proof.
  intros l left right p Hleft0 Hrightlen HpRange HpShort Hpart Hright_sorted
         i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j p) as [Hjp | Hjp].
  - assert (i = j) by lia.
    subst; lia.
  - destruct (Z.eq_dec j p) as [-> | Hjne].
    + destruct (Z.eq_dec i p) as [-> | Hip].
      * lia.
      * eapply partitioned_at_left_Znth_le_local; eauto; lia.
    + assert (Hp_j : p < j) by lia.
      destruct (Z_lt_ge_dec i p) as [Hip_lt | Hip_ge].
      * eapply Z.le_trans.
        -- eapply partitioned_at_left_Znth_le_local; eauto; lia.
        -- eapply partitioned_at_right_Znth_ge_local; eauto; lia.
      * destruct (Z.eq_dec i p) as [-> | Hip_ne].
        -- eapply partitioned_at_right_Znth_ge_local; eauto; lia.
        -- assert (p < i) by lia.
           apply Hright_sorted; lia.
Qed.

Lemma quicksort_partition_combine_left_guard_local :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    left <= p <= right ->
    right - 1 <= p ->
    partitioned_at l left right p ->
    range_nondecreasing l left (p - 1) ->
    range_nondecreasing l left right.
Proof.
  intros l left right p Hleft0 Hrightlen HpRange HpShort Hpart Hleft_sorted
         i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j p) as [Hjp | Hjp].
  - apply Hleft_sorted; lia.
  - destruct (Z.eq_dec j p) as [-> | Hjne].
    + destruct (Z.eq_dec i p) as [-> | Hip].
      * lia.
      * eapply partitioned_at_left_Znth_le_local; eauto; lia.
    + assert (Hp_j : p < j) by lia.
      destruct (Z_lt_ge_dec i p) as [Hip_lt | Hip_ge].
      * eapply Z.le_trans.
        -- eapply partitioned_at_left_Znth_le_local; eauto; lia.
        -- eapply partitioned_at_right_Znth_ge_local; eauto; lia.
      * destruct (Z.eq_dec i p) as [-> | Hip_ne].
        -- eapply partitioned_at_right_Znth_ge_local; eauto; lia.
        -- assert (i = j) by lia.
           subst; lia.
Qed.

Lemma quicksort_partition_combine_short_local :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    left <= p <= right ->
    p <= left + 1 ->
    right - 1 <= p ->
    partitioned_at l left right p ->
    range_nondecreasing l left right.
Proof.
  intros l left right p Hleft0 Hrightlen HpRange Hpleft Hrightp Hpart
         i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j p) as [Hjp | Hjp].
  - assert (i = j) by lia.
    subst; lia.
  - destruct (Z.eq_dec j p) as [-> | Hjne].
    + destruct (Z.eq_dec i p) as [-> | Hip].
      * lia.
      * eapply partitioned_at_left_Znth_le_local; eauto; lia.
    + assert (Hp_j : p < j) by lia.
      destruct (Z_lt_ge_dec i p) as [Hip_lt | Hip_ge].
      * eapply Z.le_trans.
        -- eapply partitioned_at_left_Znth_le_local; eauto; lia.
        -- eapply partitioned_at_right_Znth_ge_local; eauto; lia.
      * destruct (Z.eq_dec i p) as [-> | Hip_ne].
        -- eapply partitioned_at_right_Znth_ge_local; eauto; lia.
        -- assert (i = j) by lia.
           subst; lia.
Qed.

Lemma int_array_full_merge_three_local :
  forall x n m k (l1 l2 l3 : list Z),
    0 <= n ->
    0 <= m ->
    0 <= k ->
    IntArray.full x n l1
    ** IntArray.full (x + n * sizeof(INT)) m l2
    ** IntArray.full (x + (n + m) * sizeof(INT)) k l3
    |-- IntArray.full x (n + m + k) (l1 ++ l2 ++ l3).
Proof.
  intros.
  replace (x + (n + m) * sizeof(INT))
    with (x + n * sizeof(INT) + m * sizeof(INT)) by lia.
  replace k with (m + k - m) by lia.
  sep_apply (IntArray.full_merge_to_full
    (x + n * sizeof(INT)) m (m + k) l2 l3); try lia.
  replace (n + (m + k) - n) with (m + k) by lia.
  sepcon_lift (IntArray.full x n l1).
  replace (m + k) with (n + (m + k) - n) by lia.
  sep_apply (IntArray.full_merge_to_full
    x n (n + (m + k)) l1 (l2 ++ l3)); try lia.
  replace (n + (m + k)) with (n + m + k) by lia.
  replace (n + m + (n + m + k - n - m)) with (n + m + k) by lia.
  rewrite app_assoc.
  entailer!.
Qed.

Lemma quicksort_permuted_partition_combine_local :
  forall n p base left right,
    Zlength base = n ->
    0 <= p < n ->
    partitioned_at base 0 (n - 1) p ->
    Permutation (sublist 0 p base) left ->
    range_nondecreasing left 0 (p - 1) ->
    Permutation (sublist (p + 1) n base) right ->
    range_nondecreasing right 0 (n - p - 1 - 1) ->
    range_nondecreasing
      (left ++ sublist p (p + 1) base ++ right) 0 (n - 1).
Proof.
  intros n p base left right Hlen Hp Hpart HpermL HsortedL HpermR HsortedR.
  destruct Hpart as [_ [HleftBound HrightBound]].
  assert (HlenL : Zlength left = p).
  {
    pose proof (Permutation_length HpermL) as Hperm_len.
    assert (HZlen : Zlength (sublist 0 p base) = Zlength left).
    { rewrite !Zlength_correct. rewrite Hperm_len. reflexivity. }
    rewrite Zlength_sublist in HZlen by lia.
    lia.
  }
  assert (HlenR : Zlength right = n - p - 1).
  {
    pose proof (Permutation_length HpermR) as Hperm_len.
    assert (HZlen : Zlength (sublist (p + 1) n base) = Zlength right).
    { rewrite !Zlength_correct. rewrite Hperm_len. reflexivity. }
    rewrite Zlength_sublist in HZlen by lia.
    lia.
  }
  assert (HleftBound' : forall k, 0 <= k < p -> Znth k left 0 <= Znth p base 0).
  {
    intros k Hk.
    eapply (Forall_Znth_local (fun x => x <= Znth p base 0) left k).
    - eapply (Forall_permutation_local
        (fun x => x <= Znth p base 0) (sublist 0 p base) left).
      + exact HpermL.
      + exact HleftBound.
    - rewrite HlenL. exact Hk.
  }
  assert (HrightBound' : forall k, 0 <= k < n - p - 1 -> Znth p base 0 <= Znth k right 0).
  {
    intros k Hk.
    eapply (Forall_Znth_local (fun x => Znth p base 0 <= x) right k).
    - eapply (Forall_permutation_local
        (fun x => Znth p base 0 <= x) (sublist (p + 1) n base) right).
      + exact HpermR.
      + replace n with (n - 1 + 1) by lia.
        exact HrightBound.
    - rewrite HlenR. exact Hk.
  }
  set (combined := left ++ sublist p (p + 1) base ++ right).
  assert (Hznth_left : forall k, 0 <= k < p ->
      Znth k combined 0 = Znth k left 0).
  {
    intros k Hk.
    subst combined.
    rewrite app_Znth1 by (rewrite HlenL; lia).
    reflexivity.
  }
  assert (Hznth_pivot : Znth p combined 0 = Znth p base 0).
  {
    subst combined.
    rewrite app_Znth2 by (rewrite HlenL; lia).
    rewrite HlenL.
    replace (p - p) with 0 by lia.
    rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia).
    rewrite (@Znth_sublist_lt Z 0 p (p + 1) base 0) by (try lia; rewrite Hlen; lia).
    replace (p + 0) with p by lia.
    reflexivity.
  }
  assert (Hznth_right : forall k, p < k < n ->
      Znth k combined 0 = Znth (k - (p + 1)) right 0).
  {
    intros k Hk.
    subst combined.
    rewrite app_Znth2 by (rewrite HlenL; lia).
    rewrite HlenL.
    rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
    replace (k - p - Zlength (sublist p (p + 1) base)) with (k - (p + 1)).
    - reflexivity.
    - rewrite Zlength_sublist by lia. lia.
  }
  intros i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j p) as [Hjp | Hjp].
  - rewrite Hznth_left by lia.
    rewrite Hznth_left by lia.
    apply HsortedL; lia.
  - destruct (Z.eq_dec j p) as [Hj_eq | Hj_neq].
    + subst j.
      destruct (Z.eq_dec i p) as [Hi_eq | Hi_neq].
      * subst i. lia.
      * rewrite Hznth_left by lia.
        rewrite Hznth_pivot.
        apply HleftBound'; lia.
    + assert (Hpj : p < j) by lia.
      destruct (Z_lt_ge_dec i p) as [Hip | Hip].
      * rewrite Hznth_left by lia.
        rewrite Hznth_right by lia.
        eapply Z.le_trans.
        -- apply HleftBound'; lia.
        -- apply HrightBound'; lia.
      * destruct (Z.eq_dec i p) as [Hi_eq | Hi_neq].
        -- subst i.
           rewrite Hznth_pivot.
           rewrite Hznth_right by lia.
           apply HrightBound'; lia.
        -- assert (p < i) by lia.
           rewrite Hznth_right by lia.
           rewrite Hznth_right by lia.
           apply HsortedR; lia.
Qed.
