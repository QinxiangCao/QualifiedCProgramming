Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition DivisionValue (a cuts : list Z) (value : Z) : Prop :=
  2 <= Zlength cuts /\ Znth 0 cuts 0 = 0 /\
  Znth (Zlength cuts - 1) cuts 0 = Zlength a /\
  mono_inc cuts /\
  value = fold_right Z.add 0
    (Zmap_range (fun i => (i + 1) * fold_right Z.add 0
      (sublist (Znth i cuts 0) (Znth (i + 1) cuts 0) a))
      (Zlength cuts - 1)).

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 100000 /\ Forall (fun x => -100000000 <= x <= 100000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      DivisionValue a (fst candidate) (snd candidate))
    snd out.

Definition SuffixSum (a : list Z) (lo : Z) : Z :=
  fold_right Z.add 0 (sublist lo (Zlength a) a).

Definition SuffixContribution (a : list Z) (i : Z) : Z :=
  if Z.eq_dec i 0 then SuffixSum a 0 else Z.max 0 (SuffixSum a i).

Definition SuffixContributionSum (a : list Z) (lo value : Z) : Prop :=
  0 <= lo <= Zlength a /\
  value = fold_right Z.add 0
    (map (SuffixContribution a) (Zrange lo (Zlength a))).

Require Import Coq.micromega.Lia.
Lemma suffix_sum_at_length__suffix_initialization :
  forall a, SuffixSum a (Zlength a) = 0.
Proof.
  intros a.
  unfold SuffixSum.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.
Lemma suffix_contribution_sum_at_length__suffix_initialization :
  forall a, SuffixContributionSum a (Zlength a) 0.
Proof.
  intros a.
  unfold SuffixContributionSum.
  split.
  - pose proof (Zlength_nonneg a).
    lia.
  - unfold Zrange.
    replace (Zlength a - Zlength a) with 0 by lia.
    reflexivity.
Qed.
Lemma zrange_cons_step__suffix_transitions : forall lo hi,
  lo < hi ->
  Zrange lo hi = lo :: Zrange (lo + 1) hi.
Proof.
  intros lo hi Hlt.
  unfold Zrange.
  replace (Z.to_nat (hi - lo))
    with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  reflexivity.
Qed.
Lemma suffix_sum_step__suffix_transitions : forall (a : list Z) i,
  0 <= i < Zlength a ->
  SuffixSum a i = Znth i a 0 + SuffixSum a (i + 1).
Proof.
  intros a i Hi.
  unfold SuffixSum.
  rewrite (sublist_split i (Zlength a) (i + 1) a) by lia.
  rewrite (sublist_single 0) by lia.
  simpl.
  lia.
Qed.
Lemma suffix_contribution_sum_positive_step__suffix_transitions :
  forall (a : list Z) i answer,
  0 < i < Zlength a ->
  0 < SuffixSum a i ->
  SuffixContributionSum a (i + 1) answer ->
  SuffixContributionSum a i (answer + SuffixSum a i).
Proof.
  intros a i answer Hi Hpositive [Hrange Hanswer].
  unfold SuffixContributionSum.
  split; [lia |].
  rewrite zrange_cons_step__suffix_transitions by lia.
  simpl.
  unfold SuffixContribution at 1.
  destruct (Z.eq_dec i 0); [lia |].
  rewrite Z.max_r by lia.
  rewrite Hanswer.
  lia.
Qed.
Lemma suffix_contribution_sum_nonpositive_step__suffix_transitions :
  forall (a : list Z) i answer,
  0 < i < Zlength a ->
  SuffixSum a i <= 0 ->
  SuffixContributionSum a (i + 1) answer ->
  SuffixContributionSum a i answer.
Proof.
  intros a i answer Hi Hnonpositive [Hrange Hanswer].
  unfold SuffixContributionSum.
  split; [lia |].
  rewrite zrange_cons_step__suffix_transitions by lia.
  simpl.
  unfold SuffixContribution at 1.
  destruct (Z.eq_dec i 0); [lia |].
  rewrite Z.max_l by lia.
  exact Hanswer.
Qed.
Lemma zmap_range_sum_as_Z_range_sum__final_optimality :
  forall (f : Z -> Z) n,
    fold_right Z.add 0 (Zmap_range f n) =
    sum (fun i => 0 <= i < n) f.
Proof.
  intros f n.
  unfold Zmap_range.
  rewrite sum_range_unfold.
  induction (Zrange 0 n) as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Lemma suffix_sum_split__final_optimality :
  forall a lo hi,
    0 <= lo <= hi -> hi <= Zlength a ->
    SuffixSum a lo =
      fold_right Z.add 0 (sublist lo hi a) + SuffixSum a hi.
Proof.
  intros a lo hi Hlo Hhi.
  unfold SuffixSum.
  change (ListLib.sum (sublist lo (Zlength a) a) =
          ListLib.sum (sublist lo hi a) +
          ListLib.sum (sublist hi (Zlength a) a)).
  rewrite (list_sum_sublist_as_Z_range_sum a lo (Zlength a)) by lia.
  rewrite (list_sum_sublist_as_Z_range_sum a lo hi) by lia.
  rewrite (list_sum_sublist_as_Z_range_sum a hi (Zlength a)) by lia.
  apply sum_Z_range_split. lia.
Qed.
Lemma suffix_sum_end__final_optimality :
  forall a, SuffixSum a (Zlength a) = 0.
Proof.
  intros a. unfold SuffixSum.
  change (ListLib.sum (sublist (Zlength a) (Zlength a) a) = 0).
  rewrite (list_sum_sublist_as_Z_range_sum a (Zlength a) (Zlength a)) by
    (pose proof (Zlength_nonneg a); lia).
  apply sum_Z_range_empty. lia.
Qed.
Lemma weighted_suffix_telescope_nat__final_optimality :
  forall (n : nat) (s : Z -> Z),
    sum (fun i => 0 <= i < Z.of_nat n)
      (fun i => (i + 1) * (s i - s (i + 1))) =
    sum (fun i => 0 <= i < Z.of_nat n) s -
      Z.of_nat n * s (Z.of_nat n).
Proof.
  induction n as [|n IH]; intros s.
  - simpl. rewrite !sum_Z_range_empty by lia. ring.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite (sum_Z_range_extend_right 0 (Z.of_nat n)
      (fun i => (i + 1) * (s i - s (i + 1)))) by lia.
    rewrite (sum_Z_range_extend_right 0 (Z.of_nat n) s) by lia.
    rewrite IH. ring.
Qed.
Lemma weighted_suffix_telescope__final_optimality :
  forall m (s : Z -> Z), 0 <= m ->
    sum (fun i => 0 <= i < m)
      (fun i => (i + 1) * (s i - s (i + 1))) =
    sum (fun i => 0 <= i < m) s - m * s m.
Proof.
  intros m s Hm.
  rewrite !sum_range_unfold.
  assert (Hnat : m = Z.of_nat (Z.to_nat m)) by lia.
  rewrite Hnat.
  pose proof (weighted_suffix_telescope_nat__final_optimality
    (Z.to_nat m) s) as H.
  rewrite !sum_range_unfold in H.
  exact H.
Qed.
Lemma cuts_bounds__final_optimality :
  forall cuts n,
    2 <= Zlength cuts ->
    Znth 0 cuts 0 = 0 ->
    Znth (Zlength cuts - 1) cuts 0 = n ->
    mono_inc cuts ->
    forall j, 0 <= j < Zlength cuts ->
      0 <= Znth j cuts 0 <= n.
Proof.
  intros cuts n Hlen Hfirst Hlast Hmono j Hj.
  assert (Hn : 0 < n).
  { pose proof (Hmono 0 (Zlength cuts - 1)
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hends. lia. }
  destruct (Z.eq_dec j 0) as [-> | Hj0].
  - rewrite Hfirst. split; lia.
  - destruct (Z.eq_dec j (Zlength cuts - 1)) as [-> | Hjlast].
    + rewrite Hlast. split.
      * lia.
      * lia.
    + split.
      * pose proof (Hmono 0 j ltac:(lia) ltac:(lia) ltac:(lia)) as Hlo.
        lia.
      * pose proof (Hmono j (Zlength cuts - 1)
          ltac:(lia) ltac:(lia) ltac:(lia)) as Hhi.
        lia.
Qed.
Lemma division_value_score_identity__final_optimality :
  forall a cuts value,
    DivisionValue a cuts value ->
    value = sum
      (fun j => 0 <= j < Zlength cuts - 1)
      (fun j => SuffixSum a (Znth j cuts 0)).
Proof.
  intros a cuts value Hdiv.
  unfold DivisionValue in Hdiv.
  destruct Hdiv as (Hlen & Hfirst & Hlast & Hmono & Hvalue).
  subst value.
  rewrite zmap_range_sum_as_Z_range_sum__final_optimality.
  rewrite (sum_Z_range_ext 0 (Zlength cuts - 1)
    (fun i => (i + 1) *
      fold_right Z.add 0
        (sublist (Znth i cuts 0) (Znth (i + 1) cuts 0) a))
    (fun i => (i + 1) *
      (SuffixSum a (Znth i cuts 0) -
       SuffixSum a (Znth (i + 1) cuts 0)))).
  2: {
    intros i Hi.
    f_equal.
    pose proof (cuts_bounds__final_optimality cuts (Zlength a)
      Hlen Hfirst Hlast Hmono i) as Hbi.
    pose proof (cuts_bounds__final_optimality cuts (Zlength a)
      Hlen Hfirst Hlast Hmono (i + 1)) as Hbj.
    specialize (Hbi ltac:(lia)).
    specialize (Hbj ltac:(lia)).
    assert (Hinc : Znth i cuts 0 < Znth (i + 1) cuts 0).
    { apply Hmono; lia. }
    pose proof (suffix_sum_split__final_optimality a
      (Znth i cuts 0) (Znth (i + 1) cuts 0)) as Hsplit.
    specialize (Hsplit ltac:(lia) ltac:(lia)). lia.
  }
  rewrite weighted_suffix_telescope__final_optimality by lia.
  rewrite Hlast.
  rewrite suffix_sum_end__final_optimality.
  ring.
Qed.
Lemma mono_inc_sublist__final_optimality :
  forall l lo hi,
    0 <= lo <= hi -> hi <= Zlength l ->
    mono_inc l -> mono_inc (sublist lo hi l).
Proof.
  intros l lo hi Hlo Hhi Hmono i j Hi Hij Hj.
  rewrite Zlength_sublist in Hj by lia.
  rewrite !Znth_sublist by lia.
  apply Hmono; lia.
Qed.
Lemma sum_map_max_nonneg__final_optimality :
  forall (f : Z -> Z) xs,
    0 <= ListLib.sum (map (fun x => Z.max 0 (f x)) xs).
Proof.
  intros f xs. induction xs as [|x xs IH]; simpl; [lia|].
  pose proof (Z.le_max_l 0 (f x)). lia.
Qed.
Lemma fold_right_add_map__final_optimality :
  forall (f : Z -> Z) xs,
    fold_right Z.add 0 (map f xs) =
    fold_right (fun x acc => f x + acc) 0 xs.
Proof.
  intros f xs. induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Lemma mono_inc_bounded_sum_le_range_max_aux__final_optimality :
  forall (n : nat) low xs (f : Z -> Z),
    mono_inc xs ->
    Forall (fun x => low <= x < low + Z.of_nat n) xs ->
    ListLib.sum (map f xs) <=
      ListLib.sum
        (map (fun x => Z.max 0 (f x)) (Zrange_aux low n)).
Proof.
  induction n as [|n IH]; intros low xs f Hmono Hbounds.
  - destruct xs as [|x xs].
    + simpl. lia.
    + inversion Hbounds. simpl in *. lia.
  - destruct xs as [|x xs].
    + simpl.
      pose proof (sum_map_max_nonneg__final_optimality f
        (Zrange_aux (low + 1) n)) as Htail.
      pose proof (Z.le_max_l 0 (f low)). lia.
    + inversion Hbounds as [|? ? Hx Hxs]; subst.
      pose proof (proj1 (mono_inc_cons x xs) Hmono) as [Hxall Hxmono].
      simpl Zrange_aux. simpl map. simpl ListLib.sum.
      destruct (Z.eq_dec x low) as [-> | Hxne].
      * specialize (IH (low + 1) xs f Hxmono).
        assert (Hshift : Forall
          (fun y => low + 1 <= y < low + 1 + Z.of_nat n) xs).
        { apply Forall_forall. intros y Hyin.
          apply Forall_forall with (x := y) in Hxs; [|exact Hyin].
          apply Forall_forall with (x := y) in Hxall; [|exact Hyin].
          rewrite Nat2Z.inj_succ in Hx. lia. }
        specialize (IH Hshift).
        pose proof (Z.le_max_r 0 (f low)). lia.
      * specialize (IH (low + 1) (x :: xs) f Hmono).
        assert (Hshift : Forall
          (fun y => low + 1 <= y < low + 1 + Z.of_nat n) (x :: xs)).
        { constructor.
          - rewrite Nat2Z.inj_succ in Hx. lia.
          - apply Forall_forall. intros y Hyin.
            apply Forall_forall with (x := y) in Hxs; [|exact Hyin].
            apply Forall_forall with (x := y) in Hxall; [|exact Hyin].
            rewrite Nat2Z.inj_succ in Hx. lia. }
        specialize (IH Hshift).
        eapply Z.le_trans; [exact IH|].
        pose proof (Z.le_max_l 0 (f low)). lia.
Qed.
Lemma mono_inc_bounded_sum_le_range_max__final_optimality :
  forall low high xs (f : Z -> Z),
    low <= high ->
    mono_inc xs ->
    Forall (fun x => low <= x < high) xs ->
    ListLib.sum (map f xs) <=
      ListLib.sum (map (fun x => Z.max 0 (f x)) (Zrange low high)).
Proof.
  intros low high xs f Hrange Hmono Hbounds.
  unfold Zrange.
  apply mono_inc_bounded_sum_le_range_max_aux__final_optimality;
    try assumption.
  apply Forall_forall. intros x Hxin.
  apply Forall_forall with (x := x) in Hbounds; [|exact Hxin].
  assert (Hconv : Z.of_nat (Z.to_nat (high - low)) = high - low) by lia.
  rewrite Hconv. lia.
Qed.
Lemma indexed_sublist_map_sum__final_optimality :
  forall cuts lo hi (f : Z -> Z),
    0 <= lo <= hi -> hi <= Zlength cuts ->
    ListLib.sum (map f (sublist lo hi cuts)) =
      sum (fun j => lo <= j < hi) (fun j => f (Znth j cuts 0)).
Proof.
  intros cuts lo hi f Hlo Hhi.
  rewrite (list_sum_map_as_Z_range_sum 0 f (sublist lo hi cuts)).
  rewrite Zlength_sublist by lia.
  rewrite (sum_Z_range_ext 0 (hi - lo)
    (fun j => f (Znth j (sublist lo hi cuts) 0))
    (fun j => f (Znth (j + lo) cuts 0))).
  2: { intros j Hj. rewrite Znth_sublist by lia. reflexivity. }
  rewrite <- (sum_Z_range_shift 0 (hi - lo) lo
    (fun j => f (Znth j cuts 0))).
  replace (0 + lo) with lo by lia.
  replace (hi - lo + lo) with hi by lia.
  reflexivity.
Qed.
Lemma division_value_upper_bound__final_optimality :
  forall a cuts value,
    1 <= Zlength a ->
    DivisionValue a cuts value ->
    value <= fold_right Z.add 0
      (map (SuffixContribution a) (Zrange 0 (Zlength a))).
Proof.
  intros a cuts value Ha Hdiv.
  pose proof Hdiv as Hstruct.
  unfold DivisionValue in Hstruct.
  destruct Hstruct as (Hlen & Hfirst & Hlast & Hmono & Hvalue).
  rewrite (division_value_score_identity__final_optimality a cuts value Hdiv).
  rewrite (sum_Z_range_cons 0 (Zlength cuts - 1)) by lia.
  rewrite Hfirst.
  assert (Hint_mono : mono_inc (sublist 1 (Zlength cuts - 1) cuts)).
  { apply mono_inc_sublist__final_optimality; [lia|lia|exact Hmono]. }
  assert (Hint_bounds : Forall
    (fun x => 1 <= x < Zlength a)
    (sublist 1 (Zlength cuts - 1) cuts)).
  { apply (proj2 (Forall_Znth (fun x => 1 <= x < Zlength a) 0 _)).
    intros j Hj.
    rewrite Zlength_sublist in Hj by lia.
    rewrite Znth_sublist by lia.
    pose proof (cuts_bounds__final_optimality cuts (Zlength a)
      Hlen Hfirst Hlast Hmono (j + 1) ltac:(lia)) as Hb.
    pose proof (Hmono 0 (j + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as Hlo.
    pose proof (Hmono (j + 1) (Zlength cuts - 1)
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hhi.
    lia. }
  pose proof (mono_inc_bounded_sum_le_range_max__final_optimality
    1 (Zlength a) (sublist 1 (Zlength cuts - 1) cuts)
    (SuffixSum a) ltac:(lia) Hint_mono Hint_bounds) as Hbound.
  rewrite indexed_sublist_map_sum__final_optimality in Hbound by lia.
  change (SuffixSum a 0 +
    sum (fun j => 1 <= j < Zlength cuts - 1)
      (fun j => SuffixSum a (Znth j cuts 0)) <=
    fold_right Z.add 0
      (Zmap_range (SuffixContribution a) (Zlength a))).
  rewrite zmap_range_sum_as_Z_range_sum__final_optimality.
  unfold SuffixContribution.
  rewrite (sum_Z_range_cons 0 (Zlength a)) by lia.
  destruct (Z.eq_dec 0 0); [|contradiction].
  rewrite (sum_Z_range_ext (0 + 1) (Zlength a)
    (fun i => if Z.eq_dec i 0 then SuffixSum a 0
              else Z.max 0 (SuffixSum a i))
    (fun i => Z.max 0 (SuffixSum a i))).
  2: { intros i Hi. destruct (Z.eq_dec i 0); [lia|reflexivity]. }
  change (sum (fun j => 1 <= j < Zlength cuts - 1)
      (fun j => SuffixSum a (Znth j cuts 0)) <=
    fold_right Z.add 0
      (map (fun x => Z.max 0 (SuffixSum a x))
        (Zrange 1 (Zlength a)))) in Hbound.
  rewrite fold_right_add_map__final_optimality in Hbound.
  rewrite <- sum_range_unfold in Hbound.
  apply Z.add_le_mono_l. exact Hbound.
Qed.
Lemma mono_inc_Zrange_aux__final_optimality :
  forall n low, mono_inc (Zrange_aux low n).
Proof.
  induction n as [|n IH]; intros low.
  - apply mono_inc_nil.
  - simpl Zrange_aux.
    apply (proj2 (mono_inc_cons low (Zrange_aux (low + 1) n))).
    split.
    + apply Forall_forall. intros x Hx.
      apply In_Zrange_aux_lb in Hx. lia.
    + apply IH.
Qed.
Lemma mono_inc_Zrange__final_optimality :
  forall low high, mono_inc (Zrange low high).
Proof.
  intros low high. unfold Zrange. apply mono_inc_Zrange_aux__final_optimality.
Qed.
Lemma mono_inc_filter__final_optimality :
  forall (p : Z -> bool) xs,
    mono_inc xs -> mono_inc (filter p xs).
Proof.
  intros p xs. induction xs as [|x xs IH]; intros Hmono.
  - simpl. apply mono_inc_nil.
  - pose proof (proj1 (mono_inc_cons x xs) Hmono) as [Hx Htail].
    simpl. destruct (p x) eqn:Hp.
    + apply (proj2 (mono_inc_cons x (filter p xs))). split.
      * apply Forall_forall. intros y Hy.
        apply filter_In in Hy as [Hy _].
        apply Forall_forall with (x := y) in Hx; assumption.
      * apply IH. exact Htail.
    + apply IH. exact Htail.
Qed.
Lemma mono_inc_snoc__final_optimality :
  forall xs last,
    mono_inc xs ->
    Forall (fun x => x < last) xs ->
    mono_inc (xs ++ last :: nil).
Proof.
  intros xs last Hmono Hlast.
  apply (proj2 (mono_inc_iff_ind (xs ++ last :: nil))).
  apply (proj2 (mono_inc_ind_app xs (last :: nil))).
  split.
  - apply (proj1 (mono_inc_iff_ind xs)). exact Hmono.
  - split.
    + apply (proj1 (mono_inc_iff_ind (last :: nil))).
      apply mono_inc_single.
    + intros x y Hx Hy. simpl in Hy. destruct Hy as [-> | []].
      apply Forall_forall with (x := x) in Hlast; assumption.
Qed.
Lemma Znth_app_single_last__final_optimality :
  forall xs x,
    Znth (Zlength (xs ++ x :: nil) - 1) (xs ++ x :: nil) 0 = x.
Proof.
  intros xs x.
  unfold Znth.
  rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length xs) + Z.succ 0 - 1))
    with (length xs) by lia.
  rewrite app_nth2 by lia.
  replace (length xs - length xs)%nat with O by lia.
  reflexivity.
Qed.
Lemma positive_filter_sum__final_optimality :
  forall (f : Z -> Z) xs,
    ListLib.sum (map f (filter (fun x => 0 <? f x) xs)) =
    ListLib.sum (map (fun x => Z.max 0 (f x)) xs).
Proof.
  intros f xs. induction xs as [|x xs IH]; simpl; [reflexivity|].
  destruct (0 <? f x) eqn:Hx; simpl.
  - apply Z.ltb_lt in Hx. rewrite IH.
    rewrite Z.max_r by lia. reflexivity.
  - apply Z.ltb_ge in Hx. rewrite IH.
    rewrite Z.max_l by lia. lia.
Qed.
Lemma suffix_contribution_total_form__final_optimality :
  forall a,
    1 <= Zlength a ->
    fold_right Z.add 0
      (map (SuffixContribution a) (Zrange 0 (Zlength a))) =
    SuffixSum a 0 +
      ListLib.sum
        (map (fun i => Z.max 0 (SuffixSum a i))
          (Zrange 1 (Zlength a))).
Proof.
  intros a Ha.
  change (fold_right Z.add 0
    (Zmap_range (SuffixContribution a) (Zlength a)) =
    SuffixSum a 0 +
      ListLib.sum
        (map (fun i => Z.max 0 (SuffixSum a i))
          (Zrange 1 (Zlength a)))).
  rewrite zmap_range_sum_as_Z_range_sum__final_optimality.
  rewrite (sum_Z_range_cons 0 (Zlength a)) by lia.
  unfold SuffixContribution at 1.
  destruct (Z.eq_dec 0 0); [|contradiction].
  rewrite (sum_Z_range_ext (0 + 1) (Zlength a)
    (SuffixContribution a)
    (fun i => Z.max 0 (SuffixSum a i))).
  2: { intros i Hi. unfold SuffixContribution.
       destruct (Z.eq_dec i 0); [lia|reflexivity]. }
  rewrite fold_right_add_map__final_optimality.
  rewrite <- sum_range_unfold. reflexivity.
Qed.
Lemma optimal_division_exists__final_optimality :
  forall a,
    1 <= Zlength a ->
    exists cuts,
      DivisionValue a cuts
        (fold_right Z.add 0
          (map (SuffixContribution a) (Zrange 0 (Zlength a)))).
Proof.
  intros a Ha.
  set (positive :=
    filter (fun i => 0 <? SuffixSum a i) (Zrange 1 (Zlength a))).
  set (prefix := 0 :: positive).
  set (cuts := prefix ++ Zlength a :: nil).
  assert (Hpositive_bounds : Forall
    (fun x => 1 <= x < Zlength a) positive).
  { unfold positive. apply Forall_forall. intros x Hx.
    apply filter_In in Hx as [Hx _].
    apply (proj2 (In_Zrange 1 (Zlength a) x)) in Hx. exact Hx. }
  assert (Hpositive_mono : mono_inc positive).
  { unfold positive. apply mono_inc_filter__final_optimality.
    apply mono_inc_Zrange__final_optimality. }
  assert (Hprefix_mono : mono_inc prefix).
  { unfold prefix. apply (proj2 (mono_inc_cons 0 positive)). split.
    - apply Forall_forall. intros x Hxin.
      apply Forall_forall with (x := x) in Hpositive_bounds;
        [lia|exact Hxin].
    - exact Hpositive_mono. }
  assert (Hprefix_last : Forall (fun x => x < Zlength a) prefix).
  { unfold prefix. constructor; [lia|].
    apply Forall_forall. intros x Hxin.
    apply Forall_forall with (x := x) in Hpositive_bounds;
      [lia|exact Hxin]. }
  assert (Hcuts_mono : mono_inc cuts).
  { unfold cuts. apply mono_inc_snoc__final_optimality;
    assumption. }
  assert (Hlen : 2 <= Zlength cuts).
  { unfold cuts, prefix. rewrite Zlength_app, !Zlength_cons, Zlength_nil.
    pose proof (Zlength_nonneg positive). lia. }
  assert (Hfirst : Znth 0 cuts 0 = 0).
  { unfold cuts, prefix. simpl. reflexivity. }
  assert (Hlast : Znth (Zlength cuts - 1) cuts 0 = Zlength a).
  { unfold cuts. apply Znth_app_single_last__final_optimality. }
  exists cuts.
  unfold DivisionValue.
  repeat split; try assumption.
  set (score := fold_right Z.add 0
    (Zmap_range
      (fun i => (i + 1) * fold_right Z.add 0
        (sublist (Znth i cuts 0) (Znth (i + 1) cuts 0) a))
      (Zlength cuts - 1))).
  assert (Hscore_div : DivisionValue a cuts score).
  { unfold DivisionValue, score. repeat split; try assumption. }
  pose proof (division_value_score_identity__final_optimality
    a cuts score Hscore_div) as Hscore.
  unfold score in Hscore.
  rewrite <- (indexed_sublist_map_sum__final_optimality
    cuts 0 (Zlength cuts - 1) (SuffixSum a)) in Hscore by lia.
  assert (Hstarts : sublist 0 (Zlength cuts - 1) cuts = prefix).
  { unfold cuts.
    replace (Zlength (prefix ++ Zlength a :: nil) - 1)
      with (Zlength prefix) by
      (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    apply sublist_app_exact1. }
  rewrite Hstarts in Hscore.
  unfold prefix in Hscore. simpl in Hscore.
  unfold positive in Hscore.
  rewrite positive_filter_sum__final_optimality in Hscore.
  rewrite suffix_contribution_total_form__final_optimality by exact Ha.
  symmetry. exact Hscore.
Qed.
Lemma suffix_contribution_sum_spec__final_optimality :
  forall a out,
    Pre a -> SuffixContributionSum a 0 out -> Spec a out.
Proof.
  intros a out Hpre Hsum.
  unfold Pre in Hpre. destruct Hpre as [Hlen HForall].
  unfold SuffixContributionSum in Hsum.
  destruct Hsum as [_ Hout]. subst out.
  unfold Spec, max_value_of_subset, max_object_of_subset.
  destruct (optimal_division_exists__final_optimality a (proj1 Hlen))
    as [cuts Hcuts].
  exists (cuts,
    fold_right Z.add 0
      (map (SuffixContribution a) (Zrange 0 (Zlength a)))).
  split.
  - split.
    + exact Hcuts.
    + intros [otherCuts otherValue] Hother.
      simpl. simpl in Hother.
      exact (division_value_upper_bound__final_optimality
        a otherCuts otherValue (proj1 Hlen) Hother).
  - reflexivity.
Qed.
Lemma pre_from_pointwise_bounds__final_optimality :
  forall a,
    1 <= Zlength a <= 100000 ->
    (forall j, 0 <= j < Zlength a ->
      -100000000 <= Znth j a 0 <= 100000000) ->
    Pre a.
Proof.
  intros a Hlen Hpoint.
  unfold Pre. split; [exact Hlen|].
  apply (proj2 (Forall_Znth
    (fun x => -100000000 <= x <= 100000000) 0 a)).
  exact Hpoint.
Qed.
