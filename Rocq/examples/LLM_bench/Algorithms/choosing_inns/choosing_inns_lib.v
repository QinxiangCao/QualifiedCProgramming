Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib MonotonicList.
From SumLib Require Import ZRange.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition InnsAffordable (costs : list Z) (p lo hi : Z) : bool :=
  existsb (fun idx => Z.leb (Znth idx costs 0) p) (Zrange lo (hi + 1)).

Definition same_colorb (colors : list Z) (a b : Z) : bool :=
  Z.eqb (Znth a colors 0) (Znth b colors 0).

Definition InnsPairAllowed (colors costs : list Z) (p : Z) (pair : Z * Z) : bool :=
  let (left, right) := pair in
  same_colorb colors left right && InnsAffordable costs p left right.

Definition InnsPairs (n : Z) : list (Z * Z) :=
  flat_map (fun right => map (fun left => (left, right)) (Zrange 0 right)) (Zrange 0 n).

Definition InnsPairCount (colors costs : list Z) (p n : Z) : Z :=
  Zlength (filter (InnsPairAllowed colors costs p) (InnsPairs n)).

Definition InnsColorCount (colors : list Z) (limit color : Z) : Z :=
  Zlength (filter (fun idx => Z.eqb (Znth idx colors 0) color) (Zrange 0 limit)).

Definition InnsGoodColorCount (colors costs : list Z) (limit p color : Z) : Z :=
  Zlength (filter (fun idx => Z.eqb (Znth idx colors 0) color &&
    InnsAffordable costs p idx (limit - 1)) (Zrange 0 limit)).

Definition InnsCopiedPrefix (src old dst : list Z) (written k : Z) : Prop :=
  Forall2 eq (sublist 0 written dst) (sublist 0 written src) /\
  Forall2 eq (sublist written k dst) (sublist written k old).

(** Functional meaning of a processed prefix, independent of C array shape
    and machine-integer bounds. *)
Definition InnsPrefixCounts (colors costs : list Z) (limit k p answer : Z)
  (seen good : list Z) : Prop :=
  answer = InnsPairCount colors costs p limit /\
  (forall color, 0 <= color < k -> Znth color seen 0 = InnsColorCount colors limit color) /\
  (forall color, 0 <= color < k -> Znth color good 0 = InnsGoodColorCount colors costs limit p color).

Definition InnsPairAnswer (colors costs : list Z) (n p answer : Z) : Prop :=
  answer = InnsPairCount colors costs p n.

Require Import Coq.micromega.Psatz.

Lemma CountsZeroPrefix_nil : (Zlength (@nil Z) = 0 /\ Forall (eq 0) (@nil Z)).
Proof.
  split; [reflexivity | constructor].
Qed.
Lemma CountsZeroPrefix_snoc_zero :
  forall xs i,
    (Zlength xs = i /\ Forall (eq 0) xs) ->
    0 <= i ->
    (Zlength (xs ++ [0]) = (i + 1) /\ Forall (eq 0) (xs ++ [0])).
Proof.
  intros xs i [Hlen Hzero] Hi. split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - apply Forall_app. split; [exact Hzero | repeat constructor].
Qed.
Lemma inns_Forall2_eq : forall (xs ys : list Z), Forall2 eq xs ys <-> xs = ys.
Proof.
  intros xs ys. split.
  - intros H. induction H; subst; f_equal; assumption.
  - intros H. subst ys. induction xs; constructor; auto.
Qed.

Lemma inns_segments_agree : forall (xs ys : list Z) lo hi other_lo other_hi,
  0 <= lo <= hi /\ hi <= Zlength xs ->
  0 <= other_lo <= other_hi /\ other_hi <= Zlength ys ->
  hi - lo = other_hi - other_lo ->
  (Forall2 eq (sublist lo hi xs) (sublist other_lo other_hi ys) <->
   forall k, 0 <= k < hi - lo ->
     Znth (lo + k) xs 0 = Znth (other_lo + k) ys 0).
Proof.
  intros xs ys lo hi other_lo other_hi Hx Hy Hlength.
  rewrite inns_Forall2_eq, (list_eq_ext _ _ 0).
  rewrite !Zlength_sublist by lia. split.
  - intros [_ H] k Hk. specialize (H k Hk).
    rewrite !Znth_sublist in H by lia.
    replace (k + lo) with (lo + k) in H by lia.
    replace (k + other_lo) with (other_lo + k) in H by lia. exact H.
  - intros H. split; [lia |]. intros k Hk.
    rewrite !Znth_sublist by lia.
    replace (k + lo) with (lo + k) by lia.
    replace (k + other_lo) with (other_lo + k) by lia. apply H. exact Hk.
Qed.

Lemma CopyCountsPrefix_zero :
  forall src old k,
    Zlength src = k ->
    Zlength old = k ->
    InnsCopiedPrefix src old old 0 k.
Proof.
  intros src old k Hsrc Hold.
  unfold InnsCopiedPrefix. rewrite !inns_Forall2_eq.
  split; [rewrite !Zsublist_nil by lia |]; reflexivity.
Qed.
Lemma CopyCountsPrefix_step_replace :
  forall src old dst i k,
    Zlength src = k -> Zlength old = k ->
    InnsCopiedPrefix src old dst i k ->
    Zlength dst = k ->
    0 <= i < k ->
    InnsCopiedPrefix src old (replace_Znth i (Znth i src 0) dst) (i + 1) k.
Proof.
  intros src old dst i k Hsrc Hold Hcopy Hdst Hi.
  unfold InnsCopiedPrefix in *.
  rewrite !inns_segments_agree in Hcopy by lia.
  rewrite !inns_segments_agree by (rewrite ?Zlength_replace_Znth; lia).
  destruct Hcopy as [Hdone Hrest].
  split.
  - intros idx Hidx. simpl in *.
    destruct (Z.eq_dec idx i) as [Heq | Hneq].
    + subst idx. rewrite Znth_replace_Znth_Same by lia. reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia. apply Hdone. lia.
  - intros idx Hidx.
    rewrite Znth_replace_Znth_Diff by lia.
    specialize (Hrest (idx + 1) ltac:(lia)).
    replace (i + 1 + idx) with (i + (idx + 1)) by lia. exact Hrest.
Qed.
Lemma CopyCountsPrefix_full_eq :
  forall src old dst i k,
    InnsCopiedPrefix src old dst i k ->
    Zlength src = k ->
    Zlength dst = k ->
    i >= k ->
    i <= k ->
    dst = src.
Proof.
  intros src old dst i k [Hdone _] Hsrc Hdst Hge Hle.
  apply inns_Forall2_eq in Hdone.
  rewrite !sublist_self in Hdone by lia. exact Hdone.
Qed.
Lemma replace_Znth_preserves_bounds :
  forall xs i v k lo hi,
    Zlength xs = k ->
    0 <= i < k ->
    lo <= v <= hi ->
    Forall (fun value : Z => lo <= value <= hi) xs ->
    Forall (fun value : Z => lo <= value <= hi) (replace_Znth i v xs).
Proof.
  intros xs i v k lo hi Hlen Hi Hv Hxs.
  rewrite (Forall_Znth _ 0 xs) in Hxs.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hidx.
  rewrite Zlength_replace_Znth in Hidx.
  destruct (Z.eq_dec idx i) as [Heq | Hneq].
  - subst idx. rewrite Znth_replace_Znth_Same by lia. exact Hv.
  - rewrite Znth_replace_Znth_Diff by lia. apply Hxs. exact Hidx.
Qed.
Lemma CountArraySafe_weaken_limit :
  forall xs k old_limit new_limit,
    (Zlength xs = k /\ Forall (fun value : Z => 0 <= value <= old_limit) xs) ->
    old_limit <= new_limit ->
    (Zlength xs = k /\ Forall (fun value : Z => 0 <= value <= new_limit) xs).
Proof.
  intros xs k old_limit new_limit [Hlen Hbounds] Hle.
  split; [exact Hlen |].
  eapply Forall_impl; [| exact Hbounds]. intros value Hvalue. cbn in Hvalue |- *. lia.
Qed.
Lemma CountArraySafe_increment_at :
  forall xs k limit c,
    (Zlength xs = k /\ Forall (fun value : Z => 0 <= value <= limit) xs) ->
    0 <= c < k ->
    (Zlength (replace_Znth c (Znth c xs 0 + 1) xs) = k /\ Forall (fun value : Z => 0 <= value <= (limit + 1))
      (replace_Znth c (Znth c xs 0 + 1) xs)).
Proof.
  intros xs k limit c [Hlen Hbounds] Hc.
  split; [rewrite Zlength_replace_Znth; exact Hlen |].
  eapply replace_Znth_preserves_bounds with (k := k); try eassumption.
  - pose proof (proj1 (Forall_Znth _ 0 xs) Hbounds c ltac:(lia)) as Hvalue. cbn in Hvalue. lia.
  - eapply Forall_impl; [| exact Hbounds]. intros value Hvalue. cbn in Hvalue |- *. lia.
Qed.
Lemma ChoosingPrefixDataSafe_step_affordable_after_copy :
  forall (colors costs : list Z) i k seen good c,
    (0 <= i <= Zlength colors /\ Zlength costs = Zlength colors /\ (Zlength seen = k /\ Forall (fun value : Z
      => 0 <= value <= i) seen) /\ (Zlength good = k /\ Forall (fun value : Z => 0 <= value <= i) good)) ->
    i < Zlength colors ->
    0 <= c < k ->
    (0 <= (i + 1) <= Zlength colors /\ Zlength costs = Zlength colors /\ (Zlength (replace_Znth c (Znth c seen
      0 + 1) seen) = k /\ Forall (fun value : Z => 0 <= value <= (i + 1)) (replace_Znth c (Znth c seen 0 + 1)
      seen)) /\ (Zlength (replace_Znth c (Znth c seen 0 + 1) seen) = k /\ Forall (fun value : Z => 0 <= value
      <= (i + 1)) (replace_Znth c (Znth c seen 0 + 1) seen))).
Proof.
  intros colors costs i k seen good c
    [Hlimit [Hcosts [Hseen Hgood]]] Hi Hc.
  split; [lia |].
  split; [exact Hcosts |].
  split.
  - now apply CountArraySafe_increment_at.
  - now apply CountArraySafe_increment_at.
Qed.
Lemma ChoosingPrefixDataSafe_step_expensive :
  forall (colors costs : list Z) i k seen good c,
    (0 <= i <= Zlength colors /\ Zlength costs = Zlength colors /\ (Zlength seen = k /\ Forall (fun value : Z
      => 0 <= value <= i) seen) /\ (Zlength good = k /\ Forall (fun value : Z => 0 <= value <= i) good)) ->
    i < Zlength colors ->
    0 <= c < k ->
    (0 <= (i + 1) <= Zlength colors /\ Zlength costs = Zlength colors /\ (Zlength (replace_Znth c (Znth c seen
      0 + 1) seen) = k /\ Forall (fun value : Z => 0 <= value <= (i + 1)) (replace_Znth c (Znth c seen 0 + 1)
      seen)) /\ (Zlength good = k /\ Forall (fun value : Z => 0 <= value <= (i + 1)) good)).
Proof.
  intros colors costs i k seen good c
    [Hlimit [Hcosts [Hseen Hgood]]] Hi Hc.
  split; [lia |].
  split; [exact Hcosts |].
  split.
  - now apply CountArraySafe_increment_at.
  - eapply CountArraySafe_weaken_limit; eauto; lia.
Qed.
Require Import Coq.micromega.Lia.
Lemma choosing_pair_count_zero :
  forall (colors costs : list Z) p,
    InnsPairCount colors costs p 0 = 0.
Proof.
  intros.
  unfold InnsPairCount, InnsPairs, Zrange.
  try rewrite !Zlength_correct;
  simpl.
  reflexivity.
Qed.
Lemma color_count_zero :
  forall colors color,
    InnsColorCount colors 0 color = 0.
Proof.
  intros.
  unfold InnsColorCount, Zrange.
  try rewrite !Zlength_correct;
  simpl.
  reflexivity.
Qed.
Lemma good_color_count_zero :
  forall (colors costs : list Z) p color,
    InnsGoodColorCount colors costs 0 p color = 0.
Proof.
  intros.
  unfold InnsGoodColorCount, Zrange.
  try rewrite !Zlength_correct;
  simpl.
  reflexivity.
Qed.
Lemma CountsZeroFull_to_ChoosingPrefixState_zero :
  forall (colors costs : list Z) k p seen good,
    (Zlength seen = k /\ Forall (eq 0) seen) ->
    (Zlength good = k /\ Forall (eq 0) good) ->
    InnsPrefixCounts colors costs 0 k p 0 seen good.
Proof.
  intros colors costs k p seen good Hseen Hgood.
  destruct Hseen as [Hseen_len Hseen_zero].
  rewrite (Forall_Znth _ 0 seen), Hseen_len in Hseen_zero.
  destruct Hgood as [Hgood_len Hgood_zero].
  rewrite (Forall_Znth _ 0 good), Hgood_len in Hgood_zero.
  unfold InnsPrefixCounts.
  split.
  - rewrite choosing_pair_count_zero; reflexivity.
  - split.
    + intros color Hcolor.
      rewrite <- Hseen_zero by lia.
      rewrite color_count_zero.
      reflexivity.
    + intros color Hcolor.
      rewrite <- Hgood_zero by lia.
      rewrite good_color_count_zero.
      reflexivity.
Qed.
Lemma CountsZeroFull_to_CountArraySafe_zero :
  forall k xs,
    (Zlength xs = k /\ Forall (eq 0) xs) ->
    (Zlength xs = k /\ Forall (fun value : Z => 0 <= value <= 0) xs).
Proof.
  intros k xs [Hlen Hzero]. split; [exact Hlen |].
  eapply Forall_impl; [| exact Hzero]. intros value Hvalue. subst value. lia.
Qed.
Lemma CountsZeroFull_to_ChoosingPrefixDataSafe_zero :
  forall (colors costs : list Z) k seen good,
    (Zlength seen = k /\ Forall (eq 0) seen) ->
    (Zlength good = k /\ Forall (eq 0) good) ->
    Zlength costs = Zlength colors ->
    (0 <= 0 <= Zlength colors /\ Zlength costs = Zlength colors /\ (Zlength seen = k /\ Forall (fun value : Z
      => 0 <= value <= 0) seen) /\ (Zlength good = k /\ Forall (fun value : Z => 0 <= value <= 0) good)).
Proof.
  intros colors costs k seen good Hseen Hgood Hcosts.
  split.
  - pose proof (Zlength_nonneg colors); lia.
  - split; [exact Hcosts |].
    split.
    + now apply CountsZeroFull_to_CountArraySafe_zero.
    + now apply CountsZeroFull_to_CountArraySafe_zero.
Qed.
Lemma CountsZeroFull_bounds_zero :
  forall k xs idx,
    (Zlength xs = k /\ Forall (eq 0) xs) ->
    0 <= idx < k ->
    0 <= Znth idx xs 0 <= 0.
Proof.
  intros k xs idx Hfull Hidx.
  destruct Hfull as [Hlen Hzero].
  rewrite (Forall_Znth _ 0 xs), Hlen in Hzero.
  rewrite <- Hzero by lia.
  lia.
Qed.
Lemma ChoosingPrefixState_to_ChoosingInnsAnswer_full :
  forall (colors costs : list Z) n k p answer seen good,
    Zlength colors = n ->
    InnsPrefixCounts colors costs n k p answer seen good ->
    1 <= k ->
    (InnsPairAnswer colors costs n p answer).
Proof.
  intros colors costs n k p answer seen good Hcolors Hstate Hk.
  unfold InnsPrefixCounts in Hstate.
  unfold InnsPairAnswer.
  exact (proj1 Hstate).
Qed.
Lemma zrange_length_nonneg :
  forall n,
    0 <= n ->
    Zlength ((Zrange 0 n)) = n.
Proof.
  intros n Hn. unfold Zrange.
  replace (n - 0) with n by lia.
  remember (Z.to_nat n) as count eqn:Hcount.
  assert (Hlen : forall lo, Zlength (Zrange_aux lo count) = Z.of_nat count).
  { clear Hcount. induction count; intros lo; simpl; rewrite ?Zlength_nil, ?Zlength_cons; try rewrite IHcount; lia. }
  rewrite Hlen. subst count. lia.
Qed.
Lemma zrange_between_snoc :
  forall lo hi,
    lo <= hi ->
    (Zrange lo (hi + 1)) = (Zrange lo ((hi - 1) + 1)) ++ [hi].
Proof.
  intros lo hi Hle. unfold Zrange.
  replace (hi - 1 + 1 - lo) with (hi - lo) by lia.
  replace (hi + 1 - lo) with ((hi - lo) + 1) by lia.
  rewrite Z2Nat.inj_add by lia.
  rewrite Zrange_aux_app. simpl.
  rewrite Z2Nat.id by lia.
  replace (lo + (hi - lo)) with hi by lia. reflexivity.
Qed.

Lemma zrange_snoc :
  forall n,
    0 <= n ->
    (Zrange 0 (n + 1)) = (Zrange 0 n) ++ [n].
Proof.
  intros n Hn.
  pose proof (zrange_between_snoc 0 n Hn) as H.
  replace (n - 1 + 1) with n in H by lia. exact H.
Qed.
Lemma zrange_In :
  forall x n,
    In x ((Zrange 0 n)) ->
    0 <= x < n.
Proof.
  intros x n H. apply (proj2 (In_Zrange 0 n x)). exact H.
Qed.
Lemma affordable_betweenb_hi_true :
  forall costs p lo hi,
    lo <= hi ->
    Znth hi costs 0 <= p ->
    InnsAffordable costs p lo hi = true.
Proof.
  intros costs p lo hi Hle Hcost.
  unfold InnsAffordable.
  rewrite zrange_between_snoc by lia.
  rewrite existsb_app.
  simpl.
  apply Z.leb_le in Hcost.
  rewrite Hcost.
  rewrite orb_true_r.
  reflexivity.
Qed.
Lemma affordable_betweenb_extend_expensive :
  forall costs p lo hi,
    lo <= hi ->
    p < Znth hi costs 0 ->
    InnsAffordable costs p lo hi =
    InnsAffordable costs p lo (hi - 1).
Proof.
  intros costs p lo hi Hle Hcost.
  unfold InnsAffordable.
  rewrite zrange_between_snoc by lia.
  rewrite existsb_app.
  simpl.
  assert (Hleb : (Znth hi costs 0 <=? p) = false) by (apply Z.leb_gt; lia).
  rewrite Hleb.
  rewrite orb_false_r.
  reflexivity.
Qed.
Lemma affordable_betweenb_single_expensive :
  forall costs p i,
    p < Znth i costs 0 ->
    InnsAffordable costs p i i = false.
Proof.
  intros costs p i Hcost.
  unfold InnsAffordable. unfold Zrange.
  replace (i + 1 - i) with 1 by lia.
  simpl.
  replace (i + 0) with i by lia.
  assert (Hleb : (Znth i costs 0 <=? p) = false) by (apply Z.leb_gt; lia).
  rewrite Hleb.
  reflexivity.
Qed.
Lemma filter_length_le :
  forall {A : Type} (f : A -> bool) (xs : list A),
    (length (filter f xs) <= length xs)%nat.
Proof.
  intros A f xs.
  induction xs as [|x xs IH]; simpl.
  - lia.
  - destruct (f x); simpl; lia.
Qed.
Lemma filter_map_ext_in :
  forall {A B : Type} (f : A -> B) (p : B -> bool) (q : A -> bool) xs,
    (forall x, In x xs -> p (f x) = q x) ->
    filter p (map f xs) = map f (filter q xs).
Proof.
  intros A B f p q xs Hext.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite Hext by (left; reflexivity).
    rewrite IH.
    + destruct (q x); reflexivity.
    + intros y Hy.
      apply Hext.
      right; exact Hy.
Qed.
Lemma choosing_pairs_up_to_snoc :
  forall n,
    0 <= n ->
    InnsPairs (n + 1) =
    InnsPairs n ++ map (fun left => (left, n)) ((Zrange 0 n)).
Proof.
  intros n Hn.
  unfold InnsPairs at 1.
  rewrite zrange_snoc by lia.
  rewrite flat_map_app.
  simpl.
  unfold InnsPairs.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma choosing_pairs_up_to_Zlength_twice :
  forall n,
    0 <= n ->
    2 * Zlength (InnsPairs n) = n * (n - 1).
Proof.
  intros n Hn.
  remember (Z.to_nat n) as m eqn:Hm.
  assert (Hn_eq : n = Z.of_nat m).
  { subst m. rewrite Z2Nat.id by lia. reflexivity. }
  subst n.
  clear Hn Hm.
  induction m as [|m IH].
  - simpl.
    reflexivity.
  - replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
    rewrite choosing_pairs_up_to_snoc by lia.
    rewrite Zlength_app.
    replace
      (Zlength (map (fun left : Z => (left, Z.of_nat m)) ((Zrange 0 (Z.of_nat m)))))
      with (Zlength ((Zrange 0 (Z.of_nat m)))).
    2:{ rewrite !Zlength_correct, length_map. reflexivity. }
    rewrite zrange_length_nonneg by lia.
    nia.
Qed.
Lemma choosing_pair_count_prefix_bound :
  forall (colors costs : list Z) p limit n,
    0 <= limit <= n ->
    n <= 200000 ->
    0 <= InnsPairCount colors costs p limit <= 19999900000.
Proof.
  intros colors costs p limit n Hlimit Hn.
  unfold InnsPairCount.
  try rewrite !Zlength_correct;
  split.
  - apply Nat2Z.is_nonneg.
  - assert (Hfilter :
        Z.of_nat
          (length
             (filter (InnsPairAllowed colors costs p)
                (InnsPairs limit))) <=
        Zlength (InnsPairs limit)).
    {
      rewrite Zlength_correct.
      apply Nat2Z.inj_le.
      apply filter_length_le.
    }
    assert (Htwice :=
      choosing_pairs_up_to_Zlength_twice limit ltac:(lia)).
    assert (2 *
        Z.of_nat
          (length
             (filter (InnsPairAllowed colors costs p)
                (InnsPairs limit)))
        <= 2 * Zlength (InnsPairs limit)) by lia.
    rewrite Htwice in H.
    assert (limit * (limit - 1) <= 2 * 19999900000) by nia.
    lia.
Qed.
Lemma color_count_snoc :
  forall colors i color,
    0 <= i ->
    InnsColorCount colors (i + 1) color =
    InnsColorCount colors i color +
    (if Z.eqb (Znth i colors 0) color then 1 else 0).
Proof.
  intros colors i color Hi.
  unfold InnsColorCount.
  try rewrite !Zlength_correct;
  rewrite zrange_snoc by lia.
  rewrite filter_app, length_app.
  rewrite Nat2Z.inj_add.
  simpl.
  destruct (Z.eqb (Znth i colors 0) color); simpl; lia.
Qed.
Lemma good_color_count_affordable_as_color_count :
  forall (colors costs : list Z) i p color,
    0 <= i ->
    Znth i costs 0 <= p ->
    InnsGoodColorCount colors costs (i + 1) p color =
    InnsColorCount colors (i + 1) color.
Proof.
  intros colors costs i p color Hi Hcost.
  unfold InnsGoodColorCount, InnsColorCount.
  try rewrite !Zlength_correct;
  assert (Hf :
    filter
      (fun idx : Z =>
         Z.eqb (Znth idx colors 0) color &&
         InnsAffordable costs p idx (i + 1 - 1))
      ((Zrange 0 (i + 1))) =
    filter (fun idx : Z => Z.eqb (Znth idx colors 0) color)
      ((Zrange 0 (i + 1)))).
  {
    apply filter_ext_in.
    intros idx Hidx.
    apply zrange_In in Hidx.
    replace (i + 1 - 1) with i by lia.
    rewrite affordable_betweenb_hi_true by lia.
    rewrite andb_true_r.
    reflexivity.
  }
  rewrite Hf.
  reflexivity.
Qed.
Lemma good_color_count_snoc_expensive :
  forall (colors costs : list Z) i p color,
    0 <= i ->
    p < Znth i costs 0 ->
    InnsGoodColorCount colors costs (i + 1) p color =
    InnsGoodColorCount colors costs i p color.
Proof.
  intros colors costs i p color Hi Hcost.
  unfold InnsGoodColorCount.
  try rewrite !Zlength_correct;
  rewrite zrange_snoc by lia.
  rewrite filter_app, length_app.
  assert (Hf :
    filter
      (fun idx : Z =>
         Z.eqb (Znth idx colors 0) color &&
         InnsAffordable costs p idx (i + 1 - 1))
      ((Zrange 0 i)) =
    filter
      (fun idx : Z =>
         Z.eqb (Znth idx colors 0) color &&
         InnsAffordable costs p idx (i - 1))
      ((Zrange 0 i))).
  {
    apply filter_ext_in.
    intros idx Hidx.
    apply zrange_In in Hidx.
    replace (i + 1 - 1) with i by lia.
    rewrite affordable_betweenb_extend_expensive by lia.
    reflexivity.
  }
  rewrite Hf.
  simpl.
  replace (i + 0) with i by lia.
  replace (i + 1 - 1) with i by lia.
  rewrite affordable_betweenb_single_expensive by lia.
  destruct (Z.eqb (Znth i colors 0) color); simpl; lia.
Qed.
Lemma choosing_pair_count_snoc_affordable :
  forall (colors costs : list Z) p i c,
    0 <= i ->
    c = Znth i colors 0 ->
    Znth i costs 0 <= p ->
    InnsPairCount colors costs p (i + 1) =
    InnsPairCount colors costs p i + InnsColorCount colors i c.
Proof.
  intros colors costs p i c Hi Hc Hcost.
  unfold InnsPairCount.
  try rewrite !Zlength_correct;
  rewrite choosing_pairs_up_to_snoc by lia.
  rewrite filter_app, length_app, Nat2Z.inj_add.
  f_equal.
  unfold InnsColorCount.
  try rewrite !Zlength_correct;
  assert (Hmap :
    filter (InnsPairAllowed colors costs p)
      (map (fun left : Z => (left, i)) ((Zrange 0 i))) =
    map (fun left : Z => (left, i))
      (filter (fun idx : Z => Z.eqb (Znth idx colors 0) c) ((Zrange 0 i)))).
  {
    apply filter_map_ext_in.
    intros left Hleft.
    apply zrange_In in Hleft.
    unfold InnsPairAllowed, same_colorb.
    rewrite <- Hc.
    rewrite affordable_betweenb_hi_true by lia.
    rewrite andb_true_r.
    reflexivity.
  }
  rewrite Hmap, length_map.
  reflexivity.
Qed.
Lemma choosing_pair_count_snoc_expensive :
  forall (colors costs : list Z) p i c,
    0 <= i ->
    c = Znth i colors 0 ->
    p < Znth i costs 0 ->
    InnsPairCount colors costs p (i + 1) =
    InnsPairCount colors costs p i +
    InnsGoodColorCount colors costs i p c.
Proof.
  intros colors costs p i c Hi Hc Hcost.
  unfold InnsPairCount.
  try rewrite !Zlength_correct;
  rewrite choosing_pairs_up_to_snoc by lia.
  rewrite filter_app, length_app, Nat2Z.inj_add.
  f_equal.
  unfold InnsGoodColorCount.
  try rewrite !Zlength_correct;
  assert (Hmap :
    filter (InnsPairAllowed colors costs p)
      (map (fun left : Z => (left, i)) ((Zrange 0 i))) =
    map (fun left : Z => (left, i))
      (filter
        (fun idx : Z =>
          Z.eqb (Znth idx colors 0) c &&
          InnsAffordable costs p idx (i - 1)) ((Zrange 0 i)))).
  {
    apply filter_map_ext_in.
    intros left Hleft.
    apply zrange_In in Hleft.
    unfold InnsPairAllowed, same_colorb.
    rewrite <- Hc.
    rewrite affordable_betweenb_extend_expensive by lia.
    reflexivity.
  }
  rewrite Hmap, length_map.
  reflexivity.
Qed.
Lemma ChoosingPrefixState_answer_bound :
  forall (colors costs : list Z) limit k p answer seen good n,
    (0 <= limit <= Zlength colors /\ Zlength costs = Zlength colors /\ (Zlength seen = k /\ Forall (fun value
      : Z => 0 <= value <= limit) seen) /\ (Zlength good = k /\ Forall (fun value : Z => 0 <= value <= limit)
      good)) ->
    InnsPrefixCounts colors costs limit k p answer seen good ->
    limit <= n ->
    n <= 200000 ->
    0 <= answer <= 19999900000.
Proof.
  intros colors costs limit k p answer seen good n Hsafe Hstate Hlimit Hn.
  destruct Hsafe as [Hsafe_limit _].
  unfold InnsPrefixCounts in Hstate.
  destruct Hstate as [Hanswer _].
  rewrite Hanswer.
  apply choosing_pair_count_prefix_bound with (n := n).
  - lia.
  - exact Hn.
Qed.
Lemma ChoosingPrefixState_step_affordable_after_copy :
  forall (colors costs : list Z) i k p old_answer answer seen good seen_next c,
    (0 <= i <= Zlength colors /\ Zlength costs = Zlength colors /\ (Zlength seen = k /\ Forall (fun value : Z
      => 0 <= value <= i) seen) /\ (Zlength good = k /\ Forall (fun value : Z => 0 <= value <= i) good)) ->
    InnsPrefixCounts colors costs i k p old_answer seen good ->
    0 <= i < Zlength colors ->
    0 <= c < k ->
    c = Znth i colors 0 ->
    Znth i costs 0 <= p ->
    answer = old_answer + Znth c seen 0 ->
    seen_next = replace_Znth c (Znth c seen 0 + 1) seen ->
    InnsPrefixCounts colors costs (i + 1) k p answer seen_next seen_next.
Proof.
  intros colors costs i k p old_answer answer seen good seen_next c
         Hsafe Hstate Hi Hc_range Hc Hcost Hanswer Hseen_next.
  destruct Hsafe as [_ [_ [[Hseen_len _] [Hgood_len _]]]].
  unfold InnsPrefixCounts in Hstate.
  destruct Hstate as [Hold_answer [Hseen_count Hgood_count]].
  subst answer.
  subst seen_next.
  assert (Hseen_next_count :
    forall color,
      0 <= color < k ->
      Znth color (replace_Znth c (Znth c seen 0 + 1) seen) 0 =
      InnsColorCount colors (i + 1) color).
  {
    intros color Hcolor.
    rewrite color_count_snoc by lia.
    destruct (Z.eq_dec color c) as [Heq | Hneq].
    - subst color.
      rewrite Znth_replace_Znth_Same by (rewrite Hseen_len; lia).
      rewrite Hseen_count by lia.
      rewrite <- Hc, Z.eqb_refl.
      lia.
    - rewrite Znth_replace_Znth_Diff by (try rewrite Hseen_len; lia).
      rewrite Hseen_count by lia.
      rewrite <- Hc.
      assert (Z.eqb c color = false) by (apply Z.eqb_neq; lia).
      rewrite H.
      lia.
  }
  unfold InnsPrefixCounts.
  split.
  - rewrite Hold_answer.
    rewrite Hseen_count by lia.
    rewrite choosing_pair_count_snoc_affordable with (c := c) by lia.
    reflexivity.
  - split.
    + exact Hseen_next_count.
    + intros color Hcolor.
      rewrite good_color_count_affordable_as_color_count by lia.
      apply Hseen_next_count.
      exact Hcolor.
Qed.
Lemma ChoosingPrefixState_step_expensive :
  forall (colors costs : list Z) i k p old_answer answer seen good seen_next c,
    (0 <= i <= Zlength colors /\ Zlength costs = Zlength colors /\ (Zlength seen = k /\ Forall (fun value : Z
      => 0 <= value <= i) seen) /\ (Zlength good = k /\ Forall (fun value : Z => 0 <= value <= i) good)) ->
    InnsPrefixCounts colors costs i k p old_answer seen good ->
    0 <= i < Zlength colors ->
    0 <= c < k ->
    c = Znth i colors 0 ->
    p < Znth i costs 0 ->
    answer = old_answer + Znth c good 0 ->
    seen_next = replace_Znth c (Znth c seen 0 + 1) seen ->
    InnsPrefixCounts colors costs (i + 1) k p answer seen_next good.
Proof.
  intros colors costs i k p old_answer answer seen good seen_next c
         Hsafe Hstate Hi Hc_range Hc Hcost Hanswer Hseen_next.
  destruct Hsafe as [_ [_ [[Hseen_len _] [Hgood_len _]]]].
  unfold InnsPrefixCounts in Hstate.
  destruct Hstate as [Hold_answer [Hseen_count Hgood_count]].
  subst answer.
  subst seen_next.
  unfold InnsPrefixCounts.
  split.
  - rewrite Hold_answer.
    rewrite Hgood_count by lia.
    rewrite choosing_pair_count_snoc_expensive with (c := c) by lia.
    reflexivity.
  - split.
    + intros color Hcolor.
    rewrite color_count_snoc by lia.
    destruct (Z.eq_dec color c) as [Heq | Hneq].
    * subst color.
      rewrite Znth_replace_Znth_Same by (rewrite Hseen_len; lia).
      rewrite Hseen_count by lia.
      rewrite <- Hc.
      rewrite Z.eqb_refl.
      lia.
    * rewrite Znth_replace_Znth_Diff by (try rewrite Hseen_len; lia).
      rewrite Hseen_count by lia.
      rewrite <- Hc.
      assert (Z.eqb c color = false) by (apply Z.eqb_neq; lia).
      rewrite H.
      lia.
    + intros color Hcolor.
    rewrite Hgood_count by lia.
    rewrite good_color_count_snoc_expensive by lia.
    reflexivity.
Qed.
