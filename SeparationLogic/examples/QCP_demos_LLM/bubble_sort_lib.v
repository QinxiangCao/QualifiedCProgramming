Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib MonotonicList VMap.
Require Import SetsClass.SetsClass.
Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.

Import naive_C_Rules.
Local Open Scope sac.

Lemma increasing_sublist_elim :
  forall l lo hi i j,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    increasing (sublist lo hi l) ->
    lo <= i /\ i <= j /\ j < hi ->
    Znth i l 0 <= Znth j l 0.
Proof.
  intros l lo hi i j Hlohi Hhi Hinc Hij.
  pose proof (proj2 (mono_nondec_iff_increasing _) Hinc) as Hmono.
  unfold mono_nondec in Hmono.
  pose proof (Hmono (i - lo) (j - lo)) as Hle.
  rewrite !Znth_sublist in Hle by lia.
  replace (i - lo + lo) with i in Hle by lia.
  replace (j - lo + lo) with j in Hle by lia.
  apply Hle; try lia.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma increasing_sublist_intro :
  forall l lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall i j, lo <= i /\ i <= j /\ j < hi -> Znth i l 0 <= Znth j l 0) ->
    increasing (sublist lo hi l).
Proof.
  intros l lo hi Hlohi Hhi Hrange.
  apply (proj1 (mono_nondec_iff_increasing _)).
  unfold mono_nondec.
  intros i j Hi Hij Hj.
  assert (Hij' : 0 <= i /\ i <= j /\ j < hi - lo).
  {
    rewrite Zlength_sublist in Hj by lia.
    lia.
  }
  rewrite !Znth_sublist by lia.
  apply Hrange.
  lia.
Qed.

Lemma increasing_sublist_iff :
  forall l lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    increasing (sublist lo hi l) <->
    (forall i j, lo <= i /\ i <= j /\ j < hi -> Znth i l 0 <= Znth j l 0).
Proof.
  intros l lo hi Hlohi Hhi.
  split.
  - intros Hinc i j Hij.
    eapply increasing_sublist_elim; eauto.
  - apply increasing_sublist_intro; auto.
Qed.

Lemma increasing_sublist_strict_indices :
  forall l lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    increasing (sublist lo hi l) ->
    forall i j,
      lo <= i /\ i < j /\ j < hi ->
      Znth i l 0 <= Znth j l 0.
Proof.
  intros l lo hi Hlohi Hhi Hinc i j Hij.
  eapply increasing_sublist_elim; eauto; lia.
Qed.

Lemma replace_nth_length_Z :
  forall m (a: Z) (l0: list Z),
    length (replace_nth m l0 a) = length l0.
Proof.
  intros m a l0.
  revert l0.
  induction m; intros l0; destruct l0; simpl; try reflexivity.
  rewrite IHm.
  reflexivity.
Qed.

Lemma Zlength_replace_Znth :
  forall n (a: Z) l,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros n a l.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite replace_nth_length_Z.
  reflexivity.
Qed.

Lemma increasing_length_le_1 :
  forall l,
    Zlength l <= 1 ->
    increasing l.
Proof.
  intros l Hlen.
  apply (proj1 (mono_nondec_iff_increasing _)).
  unfold mono_nondec.
  intros i j Hi Hij Hj.
  assert (i = j) by lia.
  subst j.
  lia.
Qed.

Lemma increasing_sublist_same :
  forall l n,
    increasing (sublist n n l).
Proof.
  intros.
  apply increasing_length_le_1.
  rewrite Zlength_sublist'.
  lia.
Qed.

Lemma increasing_suffix_at_length :
  forall l n,
    Zlength l = n ->
    increasing (sublist n n l).
Proof.
  intros.
  apply increasing_sublist_same.
Qed.

Definition adjacent_swap (l: list Z) (j: Z): list Z :=
  replace_Znth (j + 1) (Znth j l 0)
    (replace_Znth j (Znth (j + 1) l 0) l).

Lemma replace_Znth_swap_form :
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

Lemma permutation_swap_Znth_lt :
  forall (l: list Z) i j (d: Z),
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hrange.
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
    2:{ rewrite Zlength_correct in Hj; lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr: (nj < length lr)%nat).
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
  rewrite replace_Znth_swap_form.
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

Lemma replace_nth_comm_Z :
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

Lemma replace_Znth_comm :
  forall (l: list Z) i j (a b: Z),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm_Z.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma permutation_swap_Znth :
  forall (l: list Z) i j (d: Z),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_Znth_lt.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm by lia.
      apply permutation_swap_Znth_lt.
      lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma Zlength_adjacent_swap :
  forall l j,
    Zlength (adjacent_swap l j) = Zlength l.
Proof.
  intros; unfold adjacent_swap; repeat rewrite Zlength_replace_Znth; reflexivity.
Qed.

Lemma Znth_adjacent_swap :
  forall l j k,
    0 <= j ->
    j + 1 < Zlength l ->
    0 <= k < Zlength l ->
    Znth k (adjacent_swap l j) 0 =
      if Z.eq_dec k j then Znth (j + 1) l 0
      else if Z.eq_dec k (j + 1) then Znth j l 0
      else Znth k l 0.
Proof.
  intros l j k Hj Hj1 Hk.
  unfold adjacent_swap.
  destruct (Z.eq_dec k j) as [-> | Hkj].
  - rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    destruct (Z.eq_dec j j); [reflexivity | lia].
  - destruct (Z.eq_dec k (j + 1)) as [-> | Hkj1].
    + rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec (j + 1) j); [lia |].
      destruct (Z.eq_dec (j + 1) (j + 1)); [reflexivity | lia].
    + rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      destruct (Z.eq_dec k j); [lia |].
      destruct (Z.eq_dec k (j + 1)); [lia | reflexivity].
Qed.

Lemma sublist_eq_from_Znth :
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

Lemma sublist_after_adjacent_swap :
  forall l j lo hi,
    0 <= j ->
    j + 1 < lo ->
    0 <= lo <= hi ->
    hi <= Zlength l ->
    sublist lo hi (adjacent_swap l j) = sublist lo hi l.
Proof.
  intros l j lo hi Hj Hjlo Hlohi Hhi.
  apply sublist_eq_from_Znth.
  - rewrite Zlength_adjacent_swap; reflexivity.
  - exact Hlohi.
  - rewrite Zlength_adjacent_swap; exact Hhi.
  - intros k Hk.
    rewrite Znth_adjacent_swap by lia.
    destruct (Z.eq_dec k j); [lia |].
    destruct (Z.eq_dec k (j + 1)); [lia | reflexivity].
Qed.

Lemma increasing_sublist_extend_left :
  forall l lo hi,
    0 <= lo < hi ->
    hi <= Zlength l ->
    increasing (sublist (lo + 1) hi l) ->
    (forall q, lo + 1 <= q < hi -> Znth lo l 0 <= Znth q l 0) ->
    increasing (sublist lo hi l).
Proof.
  intros l lo hi Hlohi Hhi Hinc Hbound.
  apply increasing_sublist_intro; try lia.
  intros p q Hpq.
  destruct (Z.eq_dec p lo) as [Hp | Hp].
  - subst p.
    destruct (Z.eq_dec q lo) as [-> | Hq].
    + lia.
    + apply Hbound; lia.
  - eapply increasing_sublist_elim with (lo := lo + 1) (hi := hi); eauto; lia.
Qed.
