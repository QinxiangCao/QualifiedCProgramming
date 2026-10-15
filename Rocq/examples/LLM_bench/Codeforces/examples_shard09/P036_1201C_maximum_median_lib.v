Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition MedianOf (a : list Z) (m : Z) : Prop :=
  exists s,
    Permutation s a /\ mono_nondec s /\ m = Znth (Zlength a / 2) s 0.

Definition ReachMedian (a : list Z) (k m : Z) : Prop :=
  exists b,
    Zlength b = Zlength a /\
    (forall i, 0 <= i < Zlength a -> Znth i a 0 <= Znth i b 0) /\
    (fold_right Z.add 0) b - (fold_right Z.add 0) a <= k /\
    MedianOf b m.

Definition Pre (k : Z) (a : list Z) : Prop :=
  (* Stated explicitly in the P036 solver Require, so dropped here:
       1 <= Zlength a <= 200000 /\
       Forall (fun x => 1 <= x <= 1000000000) a /\
       1 <= k <= 1000000000   *)
  Z.even (Zlength a) = false.

Definition Spec (k : Z) (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le (ReachMedian a k) (fun x => x) out.

Definition MedianRaiseCost (sorted : list Z) (m : Z) : Z :=
  fold_right Z.add 0
    (map (fun x => Z.max 0 (m - x))
         (sublist (Zlength sorted / 2) (Zlength sorted) sorted)).

Definition MedianCostPrefix
    (sorted : list Z) (m i need : Z) : Prop :=
  need = fold_right Z.add 0
    (map (fun x => Z.max 0 (m - x))
         (sublist (Zlength sorted / 2) i sorted)).

Definition MedianSearchBounds
    (values : list Z) (k lo hi : Z) : Prop :=
  ReachMedian values k lo /\
  forall candidate, hi < candidate -> ~ ReachMedian values k candidate.

Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zquot.
Lemma quot_div_pos__cost_prefix :
  forall a b, 0 <= a -> 0 <= b -> a ÷ b = a / b.
Proof.
  intros a b Ha Hb.
  apply Zquot_Zdiv_pos; assumption.
Qed.
Lemma median_cost_prefix_init__cost_prefix :
  forall sorted m,
    MedianCostPrefix sorted m (Zlength sorted / 2) 0.
Proof.
  intros sorted m.
  unfold MedianCostPrefix.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.
Lemma median_cost_prefix_step_lt__cost_prefix :
  forall sorted m i need,
    Zlength sorted / 2 <= i < Zlength sorted ->
    Znth i sorted 0 < m ->
    MedianCostPrefix sorted m i need ->
    MedianCostPrefix sorted m (i + 1) (need + (m - Znth i sorted 0)).
Proof.
  intros sorted m i need Hi Hlt Hprefix.
  assert (Hhalf : 0 <= Zlength sorted / 2).
  { apply Z.div_pos; pose proof (Zlength_nonneg sorted); lia. }
  unfold MedianCostPrefix in *.
  rewrite (sublist_split (Zlength sorted / 2) (i + 1) i sorted) by
      lia.
  rewrite (sublist_single 0) by lia.
  rewrite map_app, fold_right_app.
  simpl.
  rewrite Z.max_r by lia.
  assert (Hfold : forall (xs : list Z) z,
      fold_right Z.add z xs = fold_right Z.add 0 xs + z).
  {
    induction xs as [|x xs IH]; intros z; simpl.
    - lia.
    - rewrite IH. lia.
  }
  rewrite Hfold.
  lia.
Qed.
Lemma median_cost_prefix_at_end__cost_prefix :
  forall sorted m i need,
    i = Zlength sorted ->
    MedianCostPrefix sorted m i need ->
    need = MedianRaiseCost sorted m.
Proof.
  intros sorted m i need Hi Hprefix.
  subst i.
  exact Hprefix.
Qed.
Lemma median_cost_prefix_zero_tail__cost_prefix :
  forall sorted m i need,
    mono_nondec sorted ->
    Zlength sorted / 2 <= i < Zlength sorted ->
    m <= Znth i sorted 0 ->
    MedianCostPrefix sorted m i need ->
    need = MedianRaiseCost sorted m.
Proof.
  intros sorted m i need Hmono Hi Hmi Hprefix.
  pose proof (Zlength_nonneg sorted) as Hlen.
  assert (Hhalf : 0 <= Zlength sorted / 2).
  { apply Z.div_pos; lia. }
  assert (Htail : Forall (fun x => m <= x)
                    (sublist i (Zlength sorted) sorted)).
  {
    apply (proj2 (Forall_Znth (fun x => m <= x) 0
                    (sublist i (Zlength sorted) sorted))).
    intros j Hj.
    assert (Htail_len :
      Zlength (sublist i (Zlength sorted) sorted) = Zlength sorted - i).
    { apply Zlength_sublist; lia. }
    rewrite Htail_len in Hj.
    rewrite (Znth_sublist 0) by lia.
    eapply Z.le_trans; [exact Hmi |].
    apply Hmono; lia.
  }
  assert (Hzero :
    fold_right Z.add 0
      (map (fun x => Z.max 0 (m - x))
        (sublist i (Zlength sorted) sorted)) = 0).
  {
    induction Htail as [|x xs Hmx Hxs IH]; simpl.
    - reflexivity.
    - rewrite Z.max_l by lia.
      exact IH.
  }
  unfold MedianCostPrefix in Hprefix.
  unfold MedianRaiseCost.
  rewrite (sublist_split (Zlength sorted / 2) (Zlength sorted) i sorted)
    by lia.
  rewrite map_app, fold_right_app, Hzero.
  simpl.
  lia.
Qed.
Lemma permutation_preserves_zindexed_bounds__solver_sort :
  forall (values sorted : list Z) n lo hi,
    Permutation values sorted ->
    n = Zlength values ->
    (forall i, 0 <= i < n -> lo <= Znth i values 0 <= hi) ->
    Zlength sorted = n /\
    forall i, 0 <= i < n -> lo <= Znth i sorted 0 <= hi.
Proof.
  intros values sorted n lo hi Hperm Hn Hbounds.
  assert (Hlen : Zlength sorted = Zlength values).
  {
    rewrite !Zlength_correct.
    rewrite (Permutation_length Hperm).
    reflexivity.
  }
  split.
  - lia.
  - intros i Hi.
    apply (proj1 (Forall_Znth (fun x => lo <= x <= hi) 0 sorted)).
    + eapply Permutation_Forall.
      * exact Hperm.
      * apply (proj2 (Forall_Znth (fun x => lo <= x <= hi) 0 values)).
        intros j Hj.
        apply Hbounds.
        lia.
    + lia.
Qed.
Lemma fold_add_perm__search_semantics :
  forall l1 l2 : list Z,
    Permutation l1 l2 ->
    fold_right Z.add 0 l1 = fold_right Z.add 0 l2.
Proof.
  intros l1 l2 Hperm.
  induction Hperm; simpl; lia.
Qed.
Lemma fold_add_nonnegative__search_semantics :
  forall l : list Z,
    Forall (fun x => 0 <= x) l ->
    0 <= fold_right Z.add 0 l.
Proof.
  intros l H.
  induction H; simpl; lia.
Qed.
Lemma fold_add_acc__search_semantics :
  forall l acc,
    fold_right Z.add acc l = fold_right Z.add 0 l + acc.
Proof.
  induction l as [|x l IH]; intros acc; simpl; [lia |].
  rewrite IH. lia.
Qed.
Lemma fold_add_Forall2_le__search_semantics :
  forall l1 l2 : list Z,
    Forall2 Z.le l1 l2 ->
    fold_right Z.add 0 l1 <= fold_right Z.add 0 l2.
Proof.
  intros l1 l2 H.
  induction H; simpl; lia.
Qed.
Lemma Forall2_le_Znth__search_semantics :
  forall l1 l2 : list Z,
    Forall2 Z.le l1 l2 ->
    forall i, 0 <= i < Zlength l1 -> Znth i l1 0 <= Znth i l2 0.
Proof.
  intros l1 l2 H.
  induction H; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite !Znth0_cons. exact H.
    + rewrite !Znth_cons by lia.
      apply IHForall2. lia.
Qed.
Lemma Forall2_le_of_Znth__search_semantics :
  forall l1 l2 : list Z,
    Zlength l1 = Zlength l2 ->
    (forall i, 0 <= i < Zlength l1 -> Znth i l1 0 <= Znth i l2 0) ->
    Forall2 Z.le l1 l2.
Proof.
  induction l1 as [|a l1 IH]; intros l2 Hlen Hpoint.
  - destruct l2; [constructor |].
    rewrite Zlength_nil, Zlength_cons in Hlen. pose proof (Zlength_nonneg l2). lia.
  - destruct l2 as [|b l2].
    + rewrite Zlength_cons, Zlength_nil in Hlen. pose proof (Zlength_nonneg l1). lia.
    + constructor.
      * specialize (Hpoint 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l1); lia)).
        rewrite !Znth0_cons in Hpoint. exact Hpoint.
      * apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- intros i Hi.
           specialize (Hpoint (i + 1) ltac:(rewrite Zlength_cons; lia)).
           rewrite !Znth_cons in Hpoint by lia.
           replace (i + 1 - 1) with i in Hpoint by lia.
           exact Hpoint.
Qed.
Lemma count_lt_perm__search_semantics :
  forall (z : Z) (l1 l2 : list Z),
    Permutation l1 l2 ->
    length (filter (fun x => Z.ltb x z) l1) =
    length (filter (fun x => Z.ltb x z) l2).
Proof.
  intros z l1 l2 Hperm.
  induction Hperm; simpl; auto.
  - destruct (Z.ltb x z); simpl; lia.
  - destruct (Z.ltb x z), (Z.ltb y z); simpl; lia.
  - lia.
Qed.
Lemma count_lt_Forall2_le__search_semantics :
  forall (z : Z) (l1 l2 : list Z),
    Forall2 Z.le l1 l2 ->
    (length (filter (fun x => Z.ltb x z) l2) <=
     length (filter (fun x => Z.ltb x z) l1))%nat.
Proof.
  intros z l1 l2 H.
  induction H; simpl; [lia |].
  simpl.
  destruct (Z.ltb x z) eqn:Hx; destruct (Z.ltb y z) eqn:Hy; simpl; try lia.
Qed.
Lemma mono_nondec_tail__search_semantics :
  forall a l,
    mono_nondec (a :: l) -> mono_nondec l.
Proof.
  intros a l H i j Hi Hij Hj.
  specialize (H (i + 1) (j + 1) ltac:(lia) ltac:(lia)
    ltac:(rewrite Zlength_cons; lia)).
  rewrite !Znth_cons in H by lia.
  replace (i + 1 - 1) with i in H by lia.
  replace (j + 1 - 1) with j in H by lia.
  exact H.
Qed.
Lemma mono_nondec_head_all__search_semantics :
  forall a l x,
    mono_nondec (a :: l) ->
    In x l -> a <= x.
Proof.
  intros a l. revert a.
  induction l as [|b l IH]; intros a x Hmono Hin; simpl in Hin; [contradiction |].
  assert (Hab : a <= b).
  { specialize (Hmono 0 1 ltac:(lia) ltac:(lia)).
    rewrite Zlength_cons, Zlength_cons in Hmono.
    specialize (Hmono ltac:(pose proof (Zlength_nonneg l); lia)).
    rewrite Znth0_cons, Znth_cons, Znth0_cons in Hmono by lia.
    exact Hmono. }
  destruct Hin as [-> | Hin]; [exact Hab |].
  assert (Htail : mono_nondec (b :: l)).
  { eapply mono_nondec_tail__search_semantics. exact Hmono. }
  specialize (IH b x Htail Hin). lia.
Qed.
Lemma filter_ltb_empty__search_semantics :
  forall z l,
    (forall x, In x l -> z <= x) ->
    filter (fun x => Z.ltb x z) l = [].
Proof.
  intros z l H.
  induction l as [|a l IH]; simpl; auto.
  assert (Ha : Z.ltb a z = false).
  { apply Z.ltb_ge. apply H. left. reflexivity. }
  rewrite Ha. apply IH.
  intros x Hx. apply H. right. exact Hx.
Qed.
Lemma mono_nondec_count_lt_at_most__search_semantics :
  forall l i,
    mono_nondec l ->
    0 <= i < Zlength l ->
    Z.of_nat (length (filter (fun x => Z.ltb x (Znth i l 0)) l)) <= i.
Proof.
  induction l as [|a l IH]; intros i Hmono Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Znth0_cons. simpl.
    assert (filter (fun x => Z.ltb x a) l = []).
    { apply filter_ltb_empty__search_semantics. intros x Hx.
      eapply mono_nondec_head_all__search_semantics; eauto. }
    rewrite Z.ltb_irrefl, H. simpl. lia.
    + rewrite Znth_cons by lia. simpl.
    assert (Htail : mono_nondec l).
    { eapply mono_nondec_tail__search_semantics. exact Hmono. }
    specialize (IH (i - 1) Htail ltac:(lia)).
    destruct (Z.ltb a (Znth (i - 1) l 0)); simpl; lia.
Qed.
Lemma mono_nondec_count_lt_above_at_least__search_semantics :
  forall l i z,
    mono_nondec l ->
    0 <= i < Zlength l ->
    Znth i l 0 < z ->
    i + 1 <= Z.of_nat (length (filter (fun x => Z.ltb x z) l)).
Proof.
  induction l as [|a l IH]; intros i z Hmono Hi Hlt.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Znth0_cons in Hlt. simpl.
      assert (Z.ltb a z = true) by (apply Z.ltb_lt; lia).
      rewrite H.
      change (1 <= Z.of_nat (S (length (filter (fun x => Z.ltb x z) l)))).
      rewrite Nat2Z.inj_succ.
      pose proof (Nat2Z.is_nonneg (length (filter (fun x => Z.ltb x z) l))).
      lia.
    + rewrite Znth_cons in Hlt by lia. simpl.
    assert (Htail : mono_nondec l).
    { eapply mono_nondec_tail__search_semantics. exact Hmono. }
    assert (Ha : a <= Znth (i - 1) l 0).
    { assert (Hi0 : 0 <= i) by lia.
      assert (Hib : i < Zlength (a :: l)) by (rewrite Zlength_cons; lia).
      specialize (Hmono 0 i ltac:(lia) Hi0 Hib).
      rewrite Znth0_cons, Znth_cons in Hmono by lia. exact Hmono. }
    specialize (IH (i - 1) z Htail ltac:(lia) Hlt).
    assert (Z.ltb a z = true) by (apply Z.ltb_lt; lia).
    rewrite H.
    change (i + 1 <= Z.of_nat (S (length (filter (fun x => Z.ltb x z) l)))).
    rewrite Nat2Z.inj_succ.
    pose proof (Nat2Z.is_nonneg (length (filter (fun x => Z.ltb x z) l))).
    lia.
Qed.
Lemma sorted_matching_Znth_le__search_semantics :
  forall a b sa sb,
    Forall2 Z.le a b ->
    Permutation a sa ->
    Permutation b sb ->
    mono_nondec sa ->
    mono_nondec sb ->
    forall i, 0 <= i < Zlength sa -> Znth i sa 0 <= Znth i sb 0.
Proof.
  intros a b sa sb Hmatch Hpa Hpb Hsa Hsb i Hi.
  assert (Hlen : Zlength sa = Zlength sb).
  { rewrite !Zlength_correct.
    rewrite <- (Permutation_length Hpa), <- (Permutation_length Hpb).
    pose proof (Forall2_length Hmatch) as Hmatch_len. now rewrite Hmatch_len. }
  destruct (Z_le_gt_dec (Znth i sa 0) (Znth i sb 0)); auto.
  pose proof (mono_nondec_count_lt_at_most__search_semantics sa i Hsa Hi) as Hupper.
  pose proof (mono_nondec_count_lt_above_at_least__search_semantics
    sb i (Znth i sa 0) Hsb ltac:(lia) ltac:(lia)) as Hlower.
  pose proof (count_lt_Forall2_le__search_semantics (Znth i sa 0) a b Hmatch) as Hcount_nat.
  apply Nat2Z.inj_le in Hcount_nat.
  rename Hcount_nat into Hcount.
  rewrite (count_lt_perm__search_semantics _ a sa Hpa) in Hcount.
  rewrite (count_lt_perm__search_semantics _ b sb Hpb) in Hcount.
  lia.
Qed.
Lemma max_zero_mono_left__search_semantics :
  forall m1 m2 x,
    m1 <= m2 -> Z.max 0 (m1 - x) <= Z.max 0 (m2 - x).
Proof.
  intros. apply Z.max_le_compat_l. lia.
Qed.
Lemma map_max_fold_mono__search_semantics :
  forall l m1 m2,
    m1 <= m2 ->
    fold_right Z.add 0 (map (fun x => Z.max 0 (m1 - x)) l) <=
    fold_right Z.add 0 (map (fun x => Z.max 0 (m2 - x)) l).
Proof.
  induction l as [|x l IH]; intros m1 m2 Hm; simpl; [lia |].
  pose proof (max_zero_mono_left__search_semantics m1 m2 x Hm).
  specialize (IH m1 m2 Hm). lia.
Qed.
Lemma median_raise_cost_monotone__search_semantics :
  forall sorted m1 m2,
    m1 <= m2 -> MedianRaiseCost sorted m1 <= MedianRaiseCost sorted m2.
Proof.
  intros sorted m1 m2 Hm.
  unfold MedianRaiseCost.
  apply map_max_fold_mono__search_semantics. exact Hm.
Qed.
Lemma Forall_of_Znth__search_semantics :
  forall (P : Z -> Prop) l,
    (forall i, 0 <= i < Zlength l -> P (Znth i l 0)) ->
    Forall P l.
Proof.
  intros P l.
  induction l as [|a l IH]; intros H; constructor.
  - specialize (H 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia)).
    rewrite Znth0_cons in H. exact H.
  - apply IH. intros i Hi.
    specialize (H (i + 1) ltac:(rewrite Zlength_cons; lia)).
    rewrite Znth_cons in H by lia.
    replace (i + 1 - 1) with i in H by lia. exact H.
Qed.
Lemma sum_max_le_difference__search_semantics :
  forall a b m,
    Forall2 Z.le a b ->
    Forall (fun x => m <= x) b ->
    fold_right Z.add 0 (map (fun x => Z.max 0 (m - x)) a) <=
    fold_right Z.add 0 b - fold_right Z.add 0 a.
Proof.
  intros a b m Hab.
  induction Hab; intros Hm; inversion Hm; subst; simpl; [lia |].
  specialize (IHHab H3).
  destruct (Z_le_gt_dec 0 (m - x)).
  - rewrite Z.max_r by lia. lia.
  - rewrite Z.max_l by lia. lia.
Qed.
Lemma median_raise_cost_le_of_reach__search_semantics :
  forall values sorted k m,
    Permutation values sorted ->
    mono_nondec sorted ->
    ReachMedian values k m ->
    MedianRaiseCost sorted m <= k.
Proof.
  intros values sorted k m Hperm Hsorted Hreach.
  unfold ReachMedian in Hreach.
  destruct Hreach as [b [Hblen [Hpoint [Hbudget Hmedian]]]].
  unfold MedianOf in Hmedian.
  destruct Hmedian as [sb [Hsbperm [Hsbsorted Hm]]].
  assert (Hmatch : Forall2 Z.le values b).
  { apply Forall2_le_of_Znth__search_semantics.
    - symmetry. exact Hblen.
    - exact Hpoint. }
  assert (Hsorted_len : Zlength sorted = Zlength sb).
  { rewrite !Zlength_correct.
    rewrite <- (Permutation_length Hperm).
    rewrite (Permutation_length Hsbperm).
    rewrite !Zlength_correct in Hblen. symmetry. exact Hblen. }
  assert (Hsorted_point : forall i, 0 <= i < Zlength sorted ->
      Znth i sorted 0 <= Znth i sb 0).
  { intros i Hi.
    eapply sorted_matching_Znth_le__search_semantics
      with (a := values) (b := b); eauto using Permutation_sym. }
  set (h := Zlength sorted / 2).
  assert (Hh0 : 0 <= h).
  { subst h. pose proof (Zlength_nonneg sorted). apply Z.div_pos; lia. }
  assert (Hhle : h <= Zlength sorted).
  { subst h. pose proof (Zlength_nonneg sorted). apply Z.div_le_upper_bound; lia. }
  assert (Hhle_sb : h <= Zlength sb) by lia.
  assert (Hb_sb_len : Zlength b = Zlength sb).
  { rewrite !Zlength_correct.
    rewrite (Permutation_length Hsbperm). reflexivity. }
  assert (Hh_b : h = Zlength b / 2).
  { subst h. rewrite Hsorted_len, <- Hb_sb_len. reflexivity. }
  assert (Hprefix_match : Forall2 Z.le
      (sublist 0 h sorted) (sublist 0 h sb)).
  { apply Forall2_le_of_Znth__search_semantics.
    - rewrite !Zlength_sublist by lia. lia.
    - intros i Hi. rewrite Zlength_sublist in Hi by lia.
      rewrite Znth_sublist by lia. rewrite Znth_sublist by lia.
      apply Hsorted_point. lia. }
  assert (Hsuffix_match : Forall2 Z.le
      (sublist h (Zlength sorted) sorted)
      (sublist h (Zlength sb) sb)).
  { apply Forall2_le_of_Znth__search_semantics.
    - rewrite !Zlength_sublist by lia. lia.
    - intros i Hi. rewrite Zlength_sublist in Hi by lia.
      rewrite Znth_sublist by lia. rewrite Znth_sublist by lia.
      apply Hsorted_point. lia. }
  assert (Hsuffix_m : Forall (fun x => m <= x)
      (sublist h (Zlength sb) sb)).
  { apply Forall_of_Znth__search_semantics. intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    rewrite Hm, <- Hh_b.
    apply Hsbsorted; lia. }
  pose proof (sum_max_le_difference__search_semantics
    _ _ m Hsuffix_match Hsuffix_m) as Hsuffix_cost.
  pose proof (fold_add_Forall2_le__search_semantics _ _ Hprefix_match) as Hprefix_cost.
  unfold MedianRaiseCost.
  assert (Hsplit_sorted : sorted = sublist 0 h sorted ++ sublist h (Zlength sorted) sorted).
  { rewrite <- (sublist_split 0 (Zlength sorted) h sorted) by lia.
    pose proof (sublist_app_exact1 sorted (@nil Z)) as Hfull.
    rewrite app_nil_r in Hfull. rewrite Hfull. reflexivity. }
  assert (Hsplit_sb : sb = sublist 0 h sb ++ sublist h (Zlength sb) sb).
  { rewrite <- (sublist_split 0 (Zlength sb) h sb) by lia.
    pose proof (sublist_app_exact1 sb (@nil Z)) as Hfull.
    rewrite app_nil_r in Hfull. rewrite Hfull. reflexivity. }
  rewrite (fold_add_perm__search_semantics values sorted Hperm) in Hbudget.
  rewrite <- (fold_add_perm__search_semantics sb b Hsbperm) in Hbudget.
  rewrite Hsplit_sorted, Hsplit_sb in Hbudget.
  rewrite !fold_right_app in Hbudget.
  rewrite (fold_add_acc__search_semantics (sublist 0 h sb)
    (fold_right Z.add 0 (sublist h (Zlength sb) sb))) in Hbudget.
  rewrite (fold_add_acc__search_semantics (sublist 0 h sorted)
    (fold_right Z.add 0 (sublist h (Zlength sorted) sorted))) in Hbudget.
  change (fold_right Z.add 0
    (map (fun x => Z.max 0 (m - x)) (sublist h (Zlength sorted) sorted)) <= k).
  eapply Z.le_trans; [exact Hsuffix_cost |].
  lia.
Qed.
Lemma Zlength_map__search_semantics :
  forall (f : Z -> Z) l, Zlength (map f l) = Zlength l.
Proof.
  intros f l. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__search_semantics :
  forall (f : Z -> Z) l i,
    0 <= i < Zlength l ->
    Znth i (map f l) 0 = f (Znth i l 0).
Proof.
  intros f l i Hi.
  rewrite (Znth_indep (map f l) i 0 (f 0)) by
    (rewrite Zlength_map__search_semantics; lia).
  unfold Znth.
  rewrite map_nth.
  reflexivity.
Qed.
Lemma Forall2_le_map_max__search_semantics :
  forall l m,
    Forall2 Z.le l (map (fun x => Z.max m x) l).
Proof.
  induction l as [|x l IH]; simpl; constructor; auto.
  apply Z.le_max_r.
Qed.
Lemma Forall2_le_refl__search_semantics :
  forall l : list Z, Forall2 Z.le l l.
Proof.
  induction l as [|x l IH]; constructor; auto; lia.
Qed.
Lemma mono_nondec_raise_suffix__search_semantics :
  forall sorted h m,
    mono_nondec sorted ->
    0 <= h < Zlength sorted ->
    Znth h sorted 0 <= m ->
    mono_nondec
      (sublist 0 h sorted ++
       map (fun x => Z.max m x) (sublist h (Zlength sorted) sorted)).
Proof.
  intros sorted h m Hmono Hh Hmedian i j Hi Hij Hj.
  rewrite Zlength_app, Zlength_map__search_semantics,
    !Zlength_sublist in Hj by lia.
  destruct (Z_lt_ge_dec j h).
  - rewrite !app_Znth1 by (rewrite Zlength_sublist by lia; lia).
    rewrite !Znth_sublist by lia.
    apply Hmono; lia.
  - destruct (Z_lt_ge_dec i h).
    + rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia).
      rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
      rewrite Zlength_sublist by lia.
      rewrite Znth_sublist by lia.
      rewrite Znth_map__search_semantics by
        (rewrite Zlength_sublist by lia; lia).
      rewrite Znth_sublist by lia.
      eapply Z.le_trans.
      * apply Hmono with (j := h); lia.
      * eapply Z.le_trans; [exact Hmedian | apply Z.le_max_l].
    + rewrite !app_Znth2 by (rewrite Zlength_sublist by lia; lia).
      rewrite !Zlength_sublist by lia.
      rewrite !Znth_map__search_semantics by
        (rewrite Zlength_sublist by lia; lia).
      rewrite !Znth_sublist by lia.
      apply Z.max_le_compat_l.
      apply Hmono; lia.
Qed.
Lemma raise_suffix_median__search_semantics :
  forall sorted h m,
    0 <= h < Zlength sorted ->
    Znth h sorted 0 <= m ->
    Znth h
      (sublist 0 h sorted ++
       map (fun x => Z.max m x) (sublist h (Zlength sorted) sorted)) 0 = m.
Proof.
  intros sorted h m Hh Hmedian.
  rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  replace (h - h) with 0 by lia.
  rewrite Znth_map__search_semantics by
    (rewrite Zlength_sublist by lia; lia).
  rewrite Znth_sublist by lia.
  replace (h - (h - 0) + h) with h by lia.
  apply Z.max_l. exact Hmedian.
Qed.
Lemma fold_raise_difference__search_semantics :
  forall l m,
    fold_right Z.add 0 (map (fun x => Z.max m x) l) -
    fold_right Z.add 0 l =
    fold_right Z.add 0 (map (fun x => Z.max 0 (m - x)) l).
Proof.
  induction l as [|x l IH]; intros m; simpl; [lia |].
  specialize (IH m).
  destruct (Z_le_gt_dec m x) as [Hmx | Hxm].
  - rewrite (Z.max_r m x) by exact Hmx.
    rewrite (Z.max_l 0 (m - x)) by lia. lia.
  - rewrite (Z.max_l m x) by lia.
    rewrite (Z.max_r 0 (m - x)) by lia. lia.
Qed.
Lemma median_raise_cost_reaches__search_semantics :
  forall values sorted k m,
    Permutation values sorted ->
    mono_nondec sorted ->
    0 <= Zlength sorted / 2 < Zlength sorted ->
    Znth (Zlength sorted / 2) sorted 0 <= m ->
    MedianRaiseCost sorted m <= k ->
    ReachMedian values k m.
Proof.
  intros values sorted k m Hperm Hmono Hhalf Hmedian Hcost.
  set (h := Zlength sorted / 2).
  set (target := sublist 0 h sorted ++
    map (fun x => Z.max m x) (sublist h (Zlength sorted) sorted)).
  assert (Hpair : Forall2 Z.le sorted target).
  { subst target.
    assert (Hsplit : sorted = sublist 0 h sorted ++ sublist h (Zlength sorted) sorted).
    { rewrite <- (sublist_split 0 (Zlength sorted) h sorted) by lia.
      pose proof (sublist_app_exact1 sorted (@nil Z)) as Hfull.
      rewrite app_nil_r in Hfull. rewrite Hfull. reflexivity. }
    rewrite Hsplit at 1.
    apply Forall2_app;
      [apply Forall2_le_refl__search_semantics |
       apply Forall2_le_map_max__search_semantics]. }
  destruct (Permutation_Forall2 (P := Z.le) (Permutation_sym Hperm) Hpair)
    as [b [Htarget_b Hvalues_b]].
  exists b.
  assert (Hb_len : Zlength b = Zlength values).
  { rewrite !Zlength_correct.
    rewrite <- (Permutation_length Htarget_b).
    pose proof (Forall2_length Hpair) as Hpair_len.
    rewrite <- Hpair_len. now rewrite <- (Permutation_length Hperm). }
  split; [exact Hb_len |].
  split.
  - eapply Forall2_le_Znth__search_semantics. exact Hvalues_b.
  - split.
    + rewrite <- (fold_add_perm__search_semantics target b Htarget_b).
      rewrite (fold_add_perm__search_semantics values sorted Hperm).
      subst target. rewrite !fold_right_app.
      rewrite (fold_add_acc__search_semantics (sublist 0 h sorted)
        (fold_right Z.add 0
          (map (fun x => Z.max m x) (sublist h (Zlength sorted) sorted)))).
      assert (Hsplit : sorted = sublist 0 h sorted ++ sublist h (Zlength sorted) sorted).
      { rewrite <- (sublist_split 0 (Zlength sorted) h sorted) by lia.
        pose proof (sublist_app_exact1 sorted (@nil Z)) as Hfull.
        rewrite app_nil_r in Hfull. rewrite Hfull. reflexivity. }
      assert (Hfoldsplit :
        fold_right Z.add 0 sorted =
        fold_right Z.add 0 (sublist 0 h sorted) +
        fold_right Z.add 0 (sublist h (Zlength sorted) sorted)).
      { rewrite Hsplit at 1. rewrite fold_right_app.
        apply fold_add_acc__search_semantics. }
      rewrite Hfoldsplit.
      unfold MedianRaiseCost in Hcost.
      subst h.
      rewrite <- fold_raise_difference__search_semantics in Hcost.
      lia.
    + unfold MedianOf.
      exists target. split; [exact Htarget_b |].
      split.
      * subst target. apply mono_nondec_raise_suffix__search_semantics; auto.
      * rewrite Hb_len.
        assert (HlenVS : Zlength values = Zlength sorted).
        { rewrite !Zlength_correct. now rewrite (Permutation_length Hperm). }
        rewrite HlenVS.
        subst target h.
        symmetry. apply raise_suffix_median__search_semantics; auto.
Qed.
Lemma median_raise_cost_characterization__search_semantics :
  forall values sorted k m,
    Permutation values sorted ->
    mono_nondec sorted ->
    0 <= Zlength sorted / 2 < Zlength sorted ->
    Znth (Zlength sorted / 2) sorted 0 <= m ->
    (ReachMedian values k m <-> MedianRaiseCost sorted m <= k).
Proof.
  intros values sorted k m Hperm Hmono Hhalf Hmed.
  split.
  - apply median_raise_cost_le_of_reach__search_semantics; auto.
  - apply median_raise_cost_reaches__search_semantics; auto.
Qed.
Lemma fold_map_max_nonnegative__search_semantics :
  forall l m,
    0 <= fold_right Z.add 0 (map (fun x => Z.max 0 (m - x)) l).
Proof.
  induction l as [|x l IH]; intros m; simpl; [lia |].
  specialize (IH m).
  pose proof (Z.le_max_l 0 (m - x)). lia.
Qed.
Lemma reach_median_ge_original__search_semantics :
  forall values sorted k m,
    Permutation values sorted ->
    mono_nondec sorted ->
    0 <= Zlength sorted / 2 < Zlength sorted ->
    ReachMedian values k m ->
    Znth (Zlength sorted / 2) sorted 0 <= m.
Proof.
  intros values sorted k m Hperm Hmono Hhalf Hreach.
  unfold ReachMedian in Hreach.
  destruct Hreach as [b [Hblen [Hpoint [_ Hmedian]]]].
  unfold MedianOf in Hmedian.
  destruct Hmedian as [sb [Hsbperm [Hsbmono Hm]]].
  assert (Hmatch : Forall2 Z.le values b).
  { apply Forall2_le_of_Znth__search_semantics.
    - symmetry. exact Hblen.
    - exact Hpoint. }
  pose proof (sorted_matching_Znth_le__search_semantics
    values b sorted sb Hmatch Hperm (Permutation_sym Hsbperm)
    Hmono Hsbmono (Zlength sorted / 2) Hhalf) as Hcoord.
  assert (Hindex : Zlength sorted / 2 = Zlength b / 2).
  { assert (Hlen : Zlength sorted = Zlength b).
    { rewrite !Zlength_correct.
      rewrite <- (Permutation_length Hperm).
      rewrite !Zlength_correct in Hblen. exact (eq_sym Hblen). }
    now rewrite Hlen. }
  rewrite Hm, <- Hindex. exact Hcoord.
Qed.
Lemma median_raise_cost_above_upper__search_semantics :
  forall sorted candidate,
    0 <= Zlength sorted / 2 < Zlength sorted ->
    (forall j, 0 <= j < Zlength sorted -> Znth j sorted 0 <= 1000000000) ->
    candidate > 2000000000 ->
    MedianRaiseCost sorted candidate > 1000000000.
Proof.
  intros sorted candidate Hhalf Hupper Hcandidate.
  set (h := Zlength sorted / 2).
  remember (sublist h (Zlength sorted) sorted) as suffix eqn:Hsuffix.
  assert (Hsuffix_len : 0 < Zlength suffix).
  { subst suffix. rewrite Zlength_sublist by lia. lia. }
  destruct suffix as [|x xs]; [rewrite Zlength_nil in Hsuffix_len; lia |].
  assert (Hx : x = Znth h sorted 0).
  { assert (Hz : Znth 0 (x :: xs) 0 = Znth h sorted 0).
    { rewrite Hsuffix. rewrite Znth_sublist by lia. reflexivity. }
    rewrite Znth0_cons in Hz. exact Hz. }
  unfold MedianRaiseCost. fold h. rewrite <- Hsuffix. simpl.
  pose proof (Hupper h Hhalf) as Hxupper.
  pose proof (fold_map_max_nonnegative__search_semantics xs candidate).
  rewrite Z.max_r by (rewrite Hx; lia).
  rewrite Hx. lia.
Qed.
