Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope sac.

Definition max_Z (a b : Z) : Z := Z.max a b.

Fixpoint kadane_loop (cur res : Z) (l : list Z) : Z * Z :=
  match l with
  | [] => (cur, res)
  | x :: xs =>
      let cur' := max_Z x (cur + x) in
      let res' := max_Z res cur' in
      kadane_loop cur' res' xs
  end.

Definition max_suffix_sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fst (kadane_loop x x xs)
  end.

Definition max_subarray_sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => snd (kadane_loop x x xs)
  end.

Definition kadane_safe (l : list Z) : Prop :=
  forall i,
    1 <= i < Zlength l ->
    INT_MIN <= max_suffix_sum (sublist 0 i l) + Znth i l 0 <= INT_MAX.

Definition MaxSubArraySum (l : list Z) (r : Z) : Prop :=
  r = max_subarray_sum l.

Definition subarray_sum (l : list Z) (lo hi : Z) : Z :=
  sum (sublist lo hi l).

Definition suffix_sum (l : list Z) (lo : Z) : Z :=
  subarray_sum l lo (Zlength l).

Definition IntuitiveMaxSuffixSum (l : list Z) (r : Z) : Prop :=
  exists lo,
    0 <= lo < Zlength l /\
    r = suffix_sum l lo /\
    forall lo',
      0 <= lo' < Zlength l ->
      suffix_sum l lo' <= r.

Definition IntuitiveMaxSubArraySum (l : list Z) (r : Z) : Prop :=
  exists lo hi,
    0 <= lo /\ lo < hi /\ hi <= Zlength l /\
    r = subarray_sum l lo hi /\
    forall lo' hi',
      0 <= lo' /\ lo' < hi' /\ hi' <= Zlength l ->
      subarray_sum l lo' hi' <= r.

Lemma kadane_loop_snoc :
  forall cur res l x,
    kadane_loop cur res (l ++ x :: nil) =
    let st := kadane_loop cur res l in
    let cur' := fst st in
    let res' := snd st in
    (max_Z x (cur' + x), max_Z res' (max_Z x (cur' + x))).
Proof.
  intros cur res l.
  revert cur res.
  induction l.
  - intros cur res x; simpl.
    reflexivity.
  - intros cur res x; simpl.
    rewrite (IHl (max_Z a (cur + a))
                 (max_Z res (max_Z a (cur + a)))
                 x).
    remember (kadane_loop (max_Z a (cur + a))
                          (max_Z res (max_Z a (cur + a))) l) as st eqn:Hst.
    destruct st.
    reflexivity.
Qed.

Lemma max_suffix_sum_snoc :
  forall prefix x,
    prefix <> nil ->
    max_suffix_sum (prefix ++ x :: nil) =
    max_Z x (max_suffix_sum prefix + x).
Proof.
  intros prefix x Hnonempty.
  destruct prefix.
  - contradiction.
  - simpl.
    rewrite kadane_loop_snoc.
    simpl.
    reflexivity.
Qed.

Lemma max_subarray_sum_snoc :
  forall prefix x,
    prefix <> nil ->
    max_subarray_sum (prefix ++ x :: nil) =
    max_Z (max_subarray_sum prefix) (max_suffix_sum (prefix ++ x :: nil)).
Proof.
  intros prefix x Hnonempty.
  destruct prefix.
  - contradiction.
  - simpl.
    destruct (kadane_loop z z prefix) eqn:Hst.
    rewrite kadane_loop_snoc.
    simpl.
    rewrite Hst.
    reflexivity.
Qed.

Lemma subarray_sum_left_snoc :
  forall prefix x lo hi,
    0 <= lo <= hi ->
    hi <= Zlength prefix ->
    subarray_sum (prefix ++ x :: nil) lo hi = subarray_sum prefix lo hi.
Proof.
  intros prefix x lo hi Hrange Hhi.
  unfold subarray_sum.
  pose proof Zlength_correct prefix as Hzlen.
  rewrite sublist_split_app_l by lia.
  reflexivity.
Qed.

Lemma suffix_sum_last :
  forall prefix x,
    suffix_sum (prefix ++ x :: nil) (Zlength prefix) = x.
Proof.
  intros prefix x.
  unfold suffix_sum, subarray_sum.
  rewrite Zlength_app_cons.
  rewrite (sublist_split_app_r (Zlength prefix) (Zlength prefix + 1)
            (Zlength prefix) prefix (x :: nil)).
  2: reflexivity.
  2: pose proof Zlength_nonneg prefix; lia.
  replace (Zlength prefix - Zlength prefix) with 0 by lia.
  replace (Zlength prefix + 1 - Zlength prefix) with 1 by lia.
  simpl.
  lia.
Qed.

Lemma suffix_sum_snoc :
  forall prefix x lo,
    0 <= lo < Zlength prefix ->
    suffix_sum (prefix ++ x :: nil) lo = suffix_sum prefix lo + x.
Proof.
  intros prefix x lo Hlo.
  unfold suffix_sum, subarray_sum.
  pose proof Zlength_correct prefix as Hzlen.
  rewrite Zlength_app_cons.
  rewrite (sublist_split lo (Zlength prefix + 1) (Zlength prefix) (prefix ++ x :: nil)).
  2: lia.
  2: pose proof (Zlength_correct (prefix ++ x :: nil)) as Hwhole; rewrite Zlength_app_cons in Hwhole; lia.
  rewrite sum_app.
  rewrite (sublist_split_app_l lo (Zlength prefix) prefix (x :: nil)).
  2: lia.
  2: lia.
  rewrite (sublist_split_app_r (Zlength prefix) (Zlength prefix + 1)
            (Zlength prefix) prefix (x :: nil)).
  2: reflexivity.
  2: pose proof Zlength_nonneg prefix; lia.
  replace (Zlength prefix - Zlength prefix) with 0 by lia.
  replace (Zlength prefix + 1 - Zlength prefix) with 1 by lia.
  simpl.
  lia.
Qed.

Lemma max_suffix_sum_intuitive :
  forall l,
    l <> nil ->
    IntuitiveMaxSuffixSum l (max_suffix_sum l).
Proof.
  intros l Hnonempty.
  induction l using rev_ind.
  - contradiction.
  - destruct l.
    + rewrite app_nil_l.
      unfold IntuitiveMaxSuffixSum, suffix_sum, subarray_sum, max_suffix_sum.
      exists 0.
      split.
      * rewrite Zlength_cons, Zlength_nil. lia.
      * split.
        -- simpl. destruct x; reflexivity.
        -- intros lo Hlo.
           rewrite Zlength_cons, Zlength_nil in Hlo.
           assert (lo = 0) by lia.
           subst lo.
           simpl.
           destruct x;
           lia.
    + assert (Hprefix_nonempty : z :: l <> nil) by discriminate.
      specialize (IHl Hprefix_nonempty).
      destruct IHl as [lo [Hlo [Hsum Hbound]]].
      rewrite max_suffix_sum_snoc by exact Hprefix_nonempty.
      unfold IntuitiveMaxSuffixSum.
      destruct (Z_le_gt_dec x (max_suffix_sum (z :: l) + x)) as [Hcase | Hcase].
      * exists lo.
        split.
        -- rewrite Zlength_app_cons. lia.
        -- split.
           ++ rewrite suffix_sum_snoc by exact Hlo.
              rewrite Hsum.
              unfold max_Z.
              rewrite Z.max_r by lia.
              reflexivity.
           ++ intros lo' Hlo'.
              destruct (Z_lt_ge_dec lo' (Zlength (z :: l))) as [Hlt | Hge].
              ** rewrite suffix_sum_snoc by lia.
                 unfold max_Z.
                 rewrite Z.max_r by lia.
                 rewrite Hsum.
                 specialize (Hbound lo' ltac:(lia)).
                 lia.
              ** assert (lo' = Zlength (z :: l)) by (rewrite Zlength_app_cons in Hlo'; lia).
                 subst lo'.
                 rewrite suffix_sum_last.
                 unfold max_Z.
                 apply Z.le_max_l.
      * exists (Zlength (z :: l)).
        split.
        -- rewrite Zlength_app_cons. lia.
        -- split.
           ++ rewrite suffix_sum_last.
              unfold max_Z.
              rewrite Z.max_l by lia.
              reflexivity.
           ++ intros lo' Hlo'.
              destruct (Z_lt_ge_dec lo' (Zlength (z :: l))) as [Hlt | Hge].
              ** rewrite suffix_sum_snoc by lia.
                 rewrite Hsum.
                 unfold max_Z.
                 rewrite Z.max_l by lia.
                 specialize (Hbound lo' ltac:(lia)).
                 lia.
              ** assert (lo' = Zlength (z :: l)) by (rewrite Zlength_app_cons in Hlo'; lia).
                 subst lo'.
                 rewrite suffix_sum_last.
                 unfold max_Z.
                 rewrite Z.max_l by lia.
                 lia.
Qed.

Lemma max_subarray_sum_intuitive :
  forall l,
    l <> nil ->
    IntuitiveMaxSubArraySum l (max_subarray_sum l).
Proof.
  intros l Hnonempty.
  induction l using rev_ind.
  - contradiction.
  - destruct l.
    + rewrite app_nil_l.
      unfold IntuitiveMaxSubArraySum, subarray_sum, max_subarray_sum.
      exists 0, 1.
      split.
      * lia.
      * repeat split.
        -- rewrite Zlength_cons, Zlength_nil. lia.
        -- simpl. destruct x; reflexivity.
        -- intros lo hi Hrange.
           rewrite Zlength_cons, Zlength_nil in Hrange.
           assert (lo = 0 /\ hi = 1) by lia.
           destruct H as [-> ->].
           simpl.
           destruct x;
           lia.
    + assert (Hprefix_nonempty : z :: l <> nil) by discriminate.
      specialize (IHl Hprefix_nonempty).
      pose proof (max_suffix_sum_intuitive ((z :: l) ++ x :: nil)) as Hsuffix.
      assert ((z :: l) ++ x :: nil <> nil) by discriminate.
      specialize (Hsuffix H).
      destruct IHl as [best_lo [best_hi [Hbest_lo [Hbest_lt [Hbest_hi [Hbest_sum Hbest_bound]]]]]].
      destruct Hsuffix as [suf_lo [Hsuf_lo [Hsuf_sum Hsuf_bound]]].
      rewrite max_subarray_sum_snoc by exact Hprefix_nonempty.
      unfold IntuitiveMaxSubArraySum.
      destruct (Z_le_gt_dec (max_subarray_sum (z :: l))
                            (max_suffix_sum ((z :: l) ++ x :: nil))) as [Hcase | Hcase].
      * exists suf_lo, (Zlength ((z :: l) ++ x :: nil)).
        repeat split.
        -- lia.
        -- lia.
        -- lia.
        -- rewrite Hsuf_sum.
           unfold max_Z.
           rewrite Z.max_r by lia.
           reflexivity.
        -- intros lo hi Hrange.
           destruct Hrange as [Hlo0 [Hlt Hhi]].
           rewrite Zlength_app_cons in Hhi.
           assert (Hend : hi <= Zlength (z :: l) \/ hi = Zlength (z :: l) + 1) by lia.
           destruct Hend as [Hleft | Hright].
           ++ rewrite subarray_sum_left_snoc by lia.
              specialize (Hbest_bound lo hi ltac:(lia)).
              unfold max_Z.
              rewrite Z.max_r by lia.
              lia.
           ++ replace (Zlength (z :: l) + 1)
                with (Zlength ((z :: l) ++ x :: nil)) in Hright
                by apply Zlength_app_cons.
              subst hi.
              change
                (suffix_sum ((z :: l) ++ x :: nil) lo <=
                 max_Z (max_subarray_sum (z :: l))
                   (max_suffix_sum ((z :: l) ++ x :: nil))).
              specialize (Hsuf_bound lo ltac:(lia)).
              unfold max_Z.
              rewrite Z.max_r by lia.
              lia.
      * exists best_lo, best_hi.
        repeat split.
        -- lia.
        -- lia.
        -- pose proof (Zlength_app_cons (z :: l) x) as Hlen. lia.
        -- rewrite subarray_sum_left_snoc by lia.
           rewrite <- Hbest_sum.
           unfold max_Z.
           rewrite Z.max_l by lia.
           reflexivity.
        -- intros lo hi Hrange.
           destruct Hrange as [Hlo0 [Hlt Hhi]].
           rewrite Zlength_app_cons in Hhi.
           assert (Hend : hi <= Zlength (z :: l) \/ hi = Zlength (z :: l) + 1) by lia.
           destruct Hend as [Hleft | Hright].
           ++ rewrite subarray_sum_left_snoc by lia.
              specialize (Hbest_bound lo hi ltac:(lia)).
              unfold max_Z.
              rewrite Z.max_l by lia.
              lia.
           ++ replace (Zlength (z :: l) + 1)
                with (Zlength ((z :: l) ++ x :: nil)) in Hright
                by apply Zlength_app_cons.
              subst hi.
              change
                (suffix_sum ((z :: l) ++ x :: nil) lo <=
                 max_Z (max_subarray_sum (z :: l))
                   (max_suffix_sum ((z :: l) ++ x :: nil))).
              specialize (Hsuf_bound lo ltac:(lia)).
              unfold max_Z.
              rewrite Z.max_l by lia.
              lia.
Qed.

Lemma MaxSubArraySum_refines_intuitive :
  forall l r,
    l <> nil ->
    MaxSubArraySum l r ->
    IntuitiveMaxSubArraySum l r.
Proof.
  intros l r Hnonempty Hmax.
  unfold MaxSubArraySum in Hmax.
  subst r.
  apply max_subarray_sum_intuitive.
  exact Hnonempty.
Qed.
