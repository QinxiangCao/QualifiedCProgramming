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

Definition same_outside_range (l l1: list Z) (left right: Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 0 = Znth k l 0.

Definition partitioned_at (l: list Z) (low high p: Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => x <= Znth p l 0) (sublist low p l) /\
  Forall (fun x => Znth p l 0 < x) (sublist (p + 1) (high + 1) l).

Definition partition_scan_inv (l l1: list Z) (low high pivot i j: Z) : Prop :=
  permutation l l1 /\
  same_outside_range l l1 low high /\
  Znth high l1 0 = pivot /\
  (forall k, low <= k <= i -> Znth k l1 0 <= pivot) /\
  (forall k, i < k < j -> pivot < Znth k l1 0).

Inductive sorted_range (l: list Z) (left right: Z) : Prop :=
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

Definition incr (l: list Z) : Prop :=
  increasing l.

Definition ordered_range (l: list Z) (left right: Z) : Prop :=
  forall i j, left <= i -> i <= j -> j <= right -> Znth i l 0 <= Znth j l 0.

Lemma Forall_Znth_range :
  forall (P: Z -> Prop) (l: list Z) i (d: Z),
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
Lemma Forall_sublist_by_Znth_range :
  forall (P: Z -> Prop) (l: list Z) lo hi,
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

Lemma increasing_aux_tail_increasing :
  forall l x,
    increasing_aux l x ->
    increasing l.
Proof.
  intros l x Hinc.
  destruct l; simpl; auto.
  destruct Hinc as [_ Hrest].
  exact Hrest.
Qed.

Lemma increasing_aux_head_le_all :
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

Lemma increasing_implies_ordered_full :
  forall l,
    increasing l ->
    ordered_range l 0 (Zlength l - 1).
Proof.
  induction l; intros Hinc i j Hi Hij Hj.
  - rewrite Zlength_nil in Hj. lia.
  - rewrite Zlength_cons in Hj.
    destruct (Z.eq_dec i 0) as [-> | Hineq].
    + destruct (Z.eq_dec j 0) as [-> | Hjneq].
      * reflexivity.
      * rewrite (@Znth_cons Z 0 j a l) by lia.
        apply increasing_aux_head_le_all with (x := a); auto.
        split; lia.
    + assert (0 < i) by lia.
      assert (0 < j) by lia.
      rewrite !Znth_cons by lia.
      apply IHl.
      * apply increasing_aux_tail_increasing with (x := a). exact Hinc.
      * lia.
      * lia.
      * lia.
Qed.

Lemma ordered_range_full_implies_increasing :
  forall l,
    ordered_range l 0 (Zlength l - 1) ->
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

Lemma partitioned_at_left_Znth_le :
  forall l left right p k,
    0 <= left ->
    p <= Zlength l ->
    partitioned_at l left right p ->
    left <= k < p ->
    Znth k l 0 <= Znth p l 0.
Proof.
  intros l left right p k Hleft0 Hp Hpart Hk.
  destruct Hpart as [_ [Hleft _]].
  pose proof (Forall_Znth_range
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

Lemma partitioned_at_right_Znth_lt :
  forall l left right p k,
    0 <= left ->
    right < Zlength l ->
    partitioned_at l left right p ->
    p < k <= right ->
    Znth p l 0 < Znth k l 0.
Proof.
  intros l left right p k Hleft0 Hrightlen Hpart Hk.
  destruct Hpart as [Hprange [_ Hright]].
  pose proof (Forall_Znth_range
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

Lemma sorted_range_implies_ordered_range :
  forall l left right,
    0 <= left ->
    right < Zlength l ->
    sorted_range l left right ->
    ordered_range l left right.
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
      * eapply partitioned_at_left_Znth_le.
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
        eapply partitioned_at_right_Znth_lt.
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
            eapply partitioned_at_right_Znth_lt.
            + exact Hleft0.
            + exact Hrightlen.
            + exact Hpart.
            + lia.
        }
        {
          destruct Hj_cases as [-> | Hpj'].
          - eapply partitioned_at_left_Znth_le.
            + exact Hleft0.
            + eapply Z.le_trans.
              * exact Hp_right.
              * apply Z.lt_le_incl. exact Hrightlen.
            + exact Hpart.
            + lia.
          - eapply Z.le_trans.
            + eapply partitioned_at_left_Znth_le.
              * exact Hleft0.
              * eapply Z.le_trans.
                { exact Hp_right. }
                { apply Z.lt_le_incl. exact Hrightlen. }
              * exact Hpart.
              * lia.
            + apply Z.lt_le_incl.
              eapply partitioned_at_right_Znth_lt.
              * exact Hleft0.
              * exact Hrightlen.
              * exact Hpart.
              * lia.
        }
Qed.

Lemma ordered_range_implies_sorted_range :
  forall l left right,
    0 <= left ->
    right < Zlength l ->
    ordered_range l left right ->
    sorted_range l left right.
Proof.
  intros l.
  assert (Hind :
    forall n left right,
      Z.to_nat (right - left + 1) = n ->
      0 <= left ->
      right < Zlength l ->
      ordered_range l left right ->
      sorted_range l left right).
  {
    induction n; intros left right Hn Hleft Hright Hord.
    - apply sorted_range_base.
      destruct (Z_ge_dec left right) as [Hge | Hlt].
      + exact Hge.
      + assert (Hz : Z.of_nat (Z.to_nat (right - left + 1)) = right - left + 1).
        { rewrite Z2Nat.id by lia. reflexivity. }
        rewrite Hn in Hz. simpl in Hz. lia.
    - destruct (Z_ge_dec left right) as [Hge | Hlt].
      + apply sorted_range_base. exact Hge.
      + apply sorted_range_from_left with (p := right).
        * lia.
        * split.
          -- lia.
          -- split.
             ++ apply Forall_sublist_by_Znth_range.
                ** lia.
                ** lia.
                ** intros k Hk.
                   apply Hord; lia.
             ++ rewrite Zsublist_nil by lia.
                constructor.
        * apply IHn with (left := left) (right := right - 1).
          -- replace ((right - 1) - left + 1) with (right - left) by lia.
             replace (right - left + 1) with ((right - left) + 1) in Hn by lia.
             rewrite Z2Nat.inj_add in Hn by lia.
             simpl in Hn.
             lia.
          -- exact Hleft.
          -- lia.
          -- intros i j Hi Hij Hj.
             apply Hord; lia.
  }
  intros left right Hleft Hright Hord.
  apply (Hind (Z.to_nat (right - left + 1)) left right); auto.
Qed.

Lemma sorted_range_implies_increasing :
  forall l,
    sorted_range l 0 (Zlength l - 1) ->
    increasing l.
Proof.
  intros l Hsorted.
  apply ordered_range_full_implies_increasing.
  eapply sorted_range_implies_ordered_range.
  - lia.
  - pose proof (Zlength_nonneg l).
    lia.
  - exact Hsorted.
Qed.

Lemma increasing_implies_sorted_range :
  forall l,
    increasing l ->
    sorted_range l 0 (Zlength l - 1).
Proof.
  intros l Hinc.
  apply ordered_range_implies_sorted_range.
  - lia.
  - destruct l; rewrite ?Zlength_nil, ?Zlength_cons; lia.
  - apply increasing_implies_ordered_full.
    exact Hinc.
Qed.

Lemma increasing_iff_sorted_range :
  forall l,
    increasing l <-> sorted_range l 0 (Zlength l - 1).
Proof.
  intros l.
  split.
  - apply increasing_implies_sorted_range.
  - apply sorted_range_implies_increasing.
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
  unfold increasing.
  destruct l as [ | a l' ]; simpl; auto.
  destruct l' as [ | b l'' ]; simpl.
  - auto.
  - rewrite Zlength_correct in Hlen.
    simpl in Hlen.
    lia.
Qed.

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
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hrange.
  unfold permutation.
  destruct Hrange as [ Hi [ Hij Hj ] ].
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
	      rewrite <- Hnat.
	      replace (S (Z.to_nat i) + Z.to_nat (j - i - 1))%nat
	        with (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat by lia.
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
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [ Hij | Hge ].
  - apply permutation_swap_Znth_lt.
    lia.
  - destruct (Z_lt_ge_dec j i) as [ Hji | Heq ].
    + eapply Permutation_trans.
      2:{
        apply Permutation_refl.
      }
      rewrite replace_Znth_comm by lia.
      apply permutation_swap_Znth_lt.
      lia.
    + assert (i = j) by lia.
      subst j.
      unfold permutation.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma permutation_swap_Znth_by_result_length :
  forall (l: list Z) i j n (d: Z),
    0 <= i < n ->
    0 <= j < n ->
    Zlength (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) = n ->
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j n d Hi Hj Hlen.
  assert (Zlength l = n).
  {
    rewrite <- Zlength_replace_Znth with (n := i) (a := Znth j l d).
    rewrite <- Zlength_replace_Znth with (n := j) (a := Znth i l d).
    exact Hlen.
  }
  apply permutation_swap_Znth; lia.
Qed.

(* Helper lemmas migrated from quicksort_proof_manual.v. *)
Lemma same_outside_range_refl :
  forall (l: list Z) left right,
    same_outside_range l l left right.
Proof.
  intros l left right.
  unfold same_outside_range.
  split.
  - reflexivity.
  - intros k Hk _.
    reflexivity.
Qed.

Lemma same_outside_range_trans :
  forall (l l1 l2: list Z) left right,
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

Lemma same_outside_range_weaken :
  forall (l l1: list Z) left1 right1 left2 right2,
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

Lemma Forall_permutation :
  forall (P: Z -> Prop) l1 l2,
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

Lemma Forall_Znth :
  forall (P: Z -> Prop) (l: list Z) i (d: Z),
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

Lemma Znth_replace_eq :
  forall (l: list Z) n (a d: Z),
    0 <= n < Zlength l ->
    Znth n (replace_Znth n a l) d = a.
Proof.
  intros l n a d Hn.
  unfold Znth, replace_Znth.
  rewrite Zlength_correct in Hn.
  remember (Z.to_nat n) as m eqn:Hm.
  assert (HmLen : (m < length l)%nat) by lia.
  clear Hn Hm n.
  revert l HmLen.
  induction m; intros l HmLen.
  - destruct l; simpl in *.
    + lia.
    + reflexivity.
  - destruct l; simpl in *.
    + lia.
    + apply IHm. lia.
Qed.

Lemma Znth_replace_neq :
  forall (l: list Z) i j (a d: Z),
    0 <= i < Zlength l ->
    0 <= j ->
    i <> j ->
    Znth i (replace_Znth j a l) d = Znth i l d.
Proof.
  intros l i j a d Hi Hj Hneq.
  unfold Znth, replace_Znth.
  rewrite Zlength_correct in Hi.
  remember (Z.to_nat i) as ni eqn:HiNat.
  remember (Z.to_nat j) as nj eqn:HjNat.
  assert (HiEq : i = Z.of_nat ni) by (subst; symmetry; apply Z2Nat.id; lia).
  assert (HjEq : j = Z.of_nat nj) by (subst; symmetry; apply Z2Nat.id; lia).
  assert (HiLen : (ni < length l)%nat) by lia.
  assert (HneqNat : ni <> nj).
  {
    intro Heq.
    apply Hneq.
    rewrite HiEq, HjEq.
    now rewrite Heq.
  }
  clear Hi Hj Hneq HiNat HjNat HiEq HjEq i j.
  revert nj l HiLen HneqNat.
  induction ni; intros nj l HiLen HneqNat.
  - destruct l; simpl in *; try lia.
    destruct nj; [contradiction HneqNat; reflexivity | reflexivity].
  - destruct l; simpl in *; try lia.
    destruct nj; simpl.
    + reflexivity.
    + apply IHni.
      * lia.
      * intro Heq.
        apply HneqNat.
        now f_equal.
Qed.

Lemma sublist_eq_from_Znth :
  forall (l1 l2: list Z) lo hi,
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

Lemma list_decompose_sublist :
  forall (l: list Z) lo hi,
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

Lemma same_outside_range_prefix :
  forall (l l1: list Z) left right,
    same_outside_range l l1 left right ->
    0 <= left <= Zlength l ->
    sublist 0 left l1 = sublist 0 left l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  apply sublist_eq_from_Znth.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + lia.
    + left. lia.
Qed.

Lemma same_outside_range_suffix :
  forall (l l1: list Z) left right,
    same_outside_range l l1 left right ->
    0 <= right + 1 <= Zlength l ->
    sublist (right + 1) (Zlength l1) l1 = sublist (right + 1) (Zlength l) l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  rewrite <- Hlen.
  apply sublist_eq_from_Znth.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + rewrite Hlen. lia.
    + right. lia.
Qed.

Lemma middle_permutation_of_same_outside :
  forall (l l1: list Z) left right,
    permutation l l1 ->
    same_outside_range l l1 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength l ->
    permutation (sublist left (right + 1) l) (sublist left (right + 1) l1).
Proof.
  intros l l1 left right Hperm Hsame Hlr Hlenr.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen _].
  pose proof (same_outside_range_prefix _ _ _ _ Hsame0) as Hpre.
  pose proof (same_outside_range_suffix _ _ _ _ Hsame0) as Hsuf.
  rewrite (list_decompose_sublist l left (right + 1)) in Hperm by lia.
  assert (Hlenr1 : right + 1 <= Zlength l1) by (rewrite <- Hlen; exact Hlenr).
  rewrite (list_decompose_sublist l1 left (right + 1)) in Hperm by lia.
  specialize (Hpre ltac:(lia)).
  specialize (Hsuf ltac:(lia)).
  rewrite Hpre, Hsuf in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.

Lemma Forall_sublist_by_Znth :
  forall (P: Z -> Prop) (l: list Z) lo hi,
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

Lemma same_outside_range_swap_inside :
  forall (l: list Z) low high i j,
    0 <= low ->
    low <= i <= high ->
    low <= j <= high ->
    high < Zlength l ->
    same_outside_range l
      (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l))
      low high.
Proof.
  intros l low high i j Hlow Hi Hj Hhigh.
  unfold same_outside_range.
  split.
  - rewrite !Zlength_replace_Znth. reflexivity.
  - intros k Hk Hout.
    assert (Hkj : k <> j).
    { intro Heq. subst k. destruct Hout as [Hout | Hout]; lia. }
    assert (Hki : k <> i).
    { intro Heq. subst k. destruct Hout as [Hout | Hout]; lia. }
    rewrite (Znth_replace_neq (replace_Znth i (Znth j l 0) l) k j (Znth i l 0) 0).
    2: { rewrite Zlength_replace_Znth. exact Hk. }
    2: lia.
    2: exact Hkj.
    rewrite (Znth_replace_neq l k i (Znth j l 0) 0).
    2: exact Hk.
    2: lia.
    2: exact Hki.
    reflexivity.
Qed.

Lemma partitioned_at_preserved_by_left :
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
  assert (Hpiv: Znth p l1 0 = Znth p l 0).
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
      eapply (Forall_permutation
                (fun x => x <= Znth p l 0)
                (sublist left p l)
                (sublist left p l1)).
      * assert (Hmid :
            permutation (sublist left (p - 1 + 1) l)
                        (sublist left (p - 1 + 1) l1)).
        {
          eapply middle_permutation_of_same_outside
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
      apply Forall_sublist_by_Znth; try lia.
      intros k Hk.
      rewrite Heq by (try lia; right; lia).
      assert (Hk' : 0 <= k - (p + 1) < Zlength (sublist (p + 1) (right + 1) l)) by
        (rewrite Zlength_sublist by lia; lia).
      pose proof (Forall_Znth _ _ (k - (p + 1)) 0 Hright Hk') as Hz.
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

Lemma partitioned_at_preserved_by_right :
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
  assert (Hpiv: Znth p l1 0 = Znth p l 0).
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
        apply sublist_eq_from_Znth.
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
      eapply (Forall_permutation
                (fun x => Znth p l 0 < x)
                (sublist (p + 1) (right + 1) l)
                (sublist (p + 1) (right + 1) l1)).
      * assert (Hmid :
            permutation (sublist (p + 1) (right + 1) l)
                        (sublist (p + 1) (right + 1) l1)).
        {
          eapply middle_permutation_of_same_outside
            with (left := p + 1) (right := right).
          - exact Hperm.
          - exact (conj Hlen' Heq).
          - lia.
          - lia.
        }
        exact Hmid.
      * exact Hright.
Qed.

Lemma partitioned_at_ext :
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
        apply sublist_eq_from_Znth.
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
        apply sublist_eq_from_Znth.
        - symmetry. exact Hlen.
        - lia.
        - rewrite <- Hlen. lia.
        - intros k Hk. apply Heq. lia.
      }
      rewrite Hpiv.
      rewrite Hsub.
      exact Hright.
Qed.

Lemma sorted_range_ext :
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
    + eapply partitioned_at_ext.
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
    + eapply partitioned_at_ext.
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
    + eapply partitioned_at_ext.
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

Lemma partition_scan_inv_swap :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l1 ->
    j < high ->
    low - 1 <= i ->
    i < j ->
    partition_scan_inv l l1 low high pivot i j ->
    Znth j l1 0 <= pivot ->
    partition_scan_inv l
      (replace_Znth j (Znth (i + 1) l1 0)
         (replace_Znth (i + 1) (Znth j l1 0) l1))
      low high pivot (i + 1) (j + 1).
Proof.
  intros l l1 low high pivot i j Hlow Hhigh Hjh Hile Hij
         [Hperm [Hsame [Hpivot [Hle Hgt]]]] Hjle.
  set (l2 :=
    replace_Znth j (Znth (i + 1) l1 0)
      (replace_Znth (i + 1) (Znth j l1 0) l1)).
  assert (Hi1 : 0 <= i + 1 < Zlength l1) by lia.
  assert (Hjrange : 0 <= j < Zlength l1) by lia.
  split.
  - subst l2.
    eapply Permutation_trans.
    + exact Hperm.
    + apply permutation_swap_Znth; lia.
  - split.
    + eapply same_outside_range_trans.
      * exact Hsame.
      * subst l2.
        apply same_outside_range_swap_inside; lia.
    + split.
      * subst l2.
        assert (Hhighj : high <> j) by lia.
        assert (Hhighi1 : high <> i + 1) by lia.
        rewrite (Znth_replace_neq
                   (replace_Znth (i + 1) (Znth j l1 0) l1)
                   high j (Znth (i + 1) l1 0) 0).
        2: { rewrite Zlength_replace_Znth. lia. }
        2: lia.
        2: exact Hhighj.
        rewrite (Znth_replace_neq l1 high (i + 1) (Znth j l1 0) 0).
        2: lia.
        2: lia.
        2: exact Hhighi1.
        exact Hpivot.
      * split.
        -- intros k Hk.
           assert (Hklen : 0 <= k < Zlength l1) by lia.
           destruct (Z.eq_dec k (i + 1)) as [Hki1 | Hki1].
           ++ subst k.
              destruct (Z.eq_dec j (i + 1)) as [Hij1eq | Hij1neq].
              ** subst j.
                 subst l2.
                 rewrite replace_Znth_Znth by lia.
                 rewrite replace_Znth_Znth by lia.
                 exact Hjle.
              ** subst l2.
                 rewrite (Znth_replace_neq
                            (replace_Znth (i + 1) (Znth j l1 0) l1)
                            (i + 1) j (Znth (i + 1) l1 0) 0).
                 2: { rewrite Zlength_replace_Znth. lia. }
                 2: lia.
                 2: { intro HC. apply Hij1neq. symmetry. exact HC. }
                 rewrite (Znth_replace_eq l1 (i + 1) (Znth j l1 0) 0) by lia.
                 exact Hjle.
           ++ assert (Hkj : k <> j) by lia.
              subst l2.
              rewrite (Znth_replace_neq
                         (replace_Znth (i + 1) (Znth j l1 0) l1)
                         k j (Znth (i + 1) l1 0) 0).
              2: { rewrite Zlength_replace_Znth. exact Hklen. }
              2: lia.
              2: exact Hkj.
              rewrite (Znth_replace_neq l1 k (i + 1) (Znth j l1 0) 0).
              2: exact Hklen.
              2: lia.
              2: exact Hki1.
              apply Hle.
              lia.
        -- intros k Hk.
           assert (Hklen : 0 <= k < Zlength l1) by lia.
           subst l2.
           destruct (Z.eq_dec k j) as [Hkj | Hkj].
           ++ subst k.
              rewrite (Znth_replace_eq
                         (replace_Znth (i + 1) (Znth j l1 0) l1)
                         j (Znth (i + 1) l1 0) 0).
              2: { rewrite Zlength_replace_Znth. lia. }
              apply Hgt.
              lia.
           ++ assert (Hki1 : k <> i + 1) by lia.
              rewrite (Znth_replace_neq
                         (replace_Znth (i + 1) (Znth j l1 0) l1)
                         k j (Znth (i + 1) l1 0) 0).
              2: { rewrite Zlength_replace_Znth. exact Hklen. }
              2: lia.
              2: exact Hkj.
              rewrite (Znth_replace_neq l1 k (i + 1) (Znth j l1 0) 0).
              2: exact Hklen.
              2: lia.
              2: exact Hki1.
              apply Hgt.
              lia.
Qed.

Lemma partitioned_at_after_final_swap :
  forall l l1 low high pivot i,
    0 <= low ->
    high < Zlength l1 ->
    low - 1 <= i ->
    i < high ->
    partition_scan_inv l l1 low high pivot i high ->
    partitioned_at
      (replace_Znth high (Znth (i + 1) l1 0)
         (replace_Znth (i + 1) (Znth high l1 0) l1))
      low high (i + 1).
Proof.
  intros l l1 low high pivot i Hlow Hhigh Hile Hihigh
         [_ [_ [Hpivot [Hle Hgt]]]].
  set (l2 :=
    replace_Znth high (Znth (i + 1) l1 0)
      (replace_Znth (i + 1) (Znth high l1 0) l1)).
  assert (Hi1 : 0 <= i + 1 < Zlength l1) by lia.
  assert (Hhighrange : 0 <= high < Zlength l1) by lia.
  assert (Hpiv : Znth (i + 1) l2 0 = pivot).
  {
    subst l2.
    destruct (Z.eq_dec high (i + 1)) as [Heq | Hneq].
    - subst high.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      exact Hpivot.
    - rewrite (Znth_replace_neq
                 (replace_Znth (i + 1) (Znth high l1 0) l1)
                 (i + 1) high (Znth (i + 1) l1 0) 0).
      2: { rewrite Zlength_replace_Znth. lia. }
      2: lia.
      2: { intro HC. apply Hneq. symmetry. exact HC. }
      rewrite (Znth_replace_eq l1 (i + 1) (Znth high l1 0) 0) by lia.
      exact Hpivot.
  }
  split.
  - lia.
  - split.
    + apply Forall_sublist_by_Znth.
      * lia.
      * subst l2. rewrite !Zlength_replace_Znth. lia.
      * intros k Hk.
        rewrite Hpiv.
        assert (Hklen : 0 <= k < Zlength l1) by lia.
        assert (Hkhigh : k <> high) by lia.
        assert (Hki1 : k <> i + 1) by lia.
        subst l2.
        rewrite (Znth_replace_neq
                   (replace_Znth (i + 1) (Znth high l1 0) l1)
                   k high (Znth (i + 1) l1 0) 0).
        2: { rewrite Zlength_replace_Znth. exact Hklen. }
        2: lia.
        2: exact Hkhigh.
        rewrite (Znth_replace_neq l1 k (i + 1) (Znth high l1 0) 0).
        2: exact Hklen.
        2: lia.
        2: exact Hki1.
        apply Hle.
        lia.
    + apply Forall_sublist_by_Znth.
      * lia.
      * subst l2. rewrite !Zlength_replace_Znth. lia.
      * intros k Hk.
        rewrite Hpiv.
        assert (Hklen : 0 <= k < Zlength l1) by lia.
        destruct (Z.eq_dec k high) as [Hkhigh | Hkhigh].
        -- subst k.
           subst l2.
           rewrite (Znth_replace_eq
                      (replace_Znth (i + 1) (Znth high l1 0) l1)
                      high (Znth (i + 1) l1 0) 0).
           2: { rewrite Zlength_replace_Znth. lia. }
           apply Hgt.
           lia.
        -- assert (Hki1 : k <> i + 1) by lia.
           subst l2.
           rewrite (Znth_replace_neq
                      (replace_Znth (i + 1) (Znth high l1 0) l1)
                      k high (Znth (i + 1) l1 0) 0).
           2: { rewrite Zlength_replace_Znth. exact Hklen. }
           2: lia.
           2: exact Hkhigh.
           rewrite (Znth_replace_neq l1 k (i + 1) (Znth high l1 0) 0).
           2: exact Hklen.
           2: lia.
           2: exact Hki1.
           apply Hgt.
           lia.
Qed.
