Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition zrange (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat n)).

Definition zrange_between (lo hi : Z) : list Z :=
  map (fun t => lo + Z.of_nat t) (seq 0 (Z.to_nat (hi - lo + 1))).

Definition affordable_betweenb (costs : list Z) (p lo hi : Z) : bool :=
  existsb (fun idx => Z.leb (Znth idx costs 0) p) (zrange_between lo hi).

Definition same_colorb (colors : list Z) (a b : Z) : bool :=
  Z.eqb (Znth a colors 0) (Znth b colors 0).

Definition choosing_pairb (colors costs : list Z) (p : Z) (pair : Z * Z) : bool :=
  let (left, right) := pair in
  same_colorb colors left right && affordable_betweenb costs p left right.

Definition choosing_pairs_up_to (n : Z) : list (Z * Z) :=
  flat_map (fun right => map (fun left => (left, right)) (zrange right))
           (zrange n).

Definition choosing_pair_count (colors costs : list Z) (p n : Z) : Z :=
  Z.of_nat
    (length
       (filter (choosing_pairb colors costs p) (choosing_pairs_up_to n))).

Definition color_count (colors : list Z) (limit color : Z) : Z :=
  Z.of_nat
    (length
       (filter (fun idx => Z.eqb (Znth idx colors 0) color)
               (zrange limit))).

Definition good_color_count
    (colors costs : list Z) (limit p color : Z) : Z :=
  Z.of_nat
    (length
       (filter
          (fun idx =>
             Z.eqb (Znth idx colors 0) color &&
             affordable_betweenb costs p idx (limit - 1))
          (zrange limit))).

(** Safety and representation facts for the immutable problem input.  This
    predicate deliberately contains no statement about the required answer. *)
Definition ChoosingInputSafe
    (colors costs : list Z) (n k p : Z) : Prop :=
  0 <= n <= 200000 /\
  1 <= k <= 50 /\
  0 <= p <= 100 /\
  Zlength colors = n /\
  Zlength costs = n /\
  (forall idx, 0 <= idx < n -> 0 <= Znth idx colors 0 < k) /\
  (forall idx, 0 <= idx < n -> 0 <= Znth idx costs 0 <= 100).

(** Shape and arithmetic bounds for a concrete per-colour count array. *)
Definition CountArraySafe (xs : list Z) (k limit : Z) : Prop :=
  Zlength xs = k /\
  forall idx, 0 <= idx < k -> 0 <= Znth idx xs 0 <= limit.

Definition CountsZeroPrefix (xs : list Z) (written : Z) : Prop :=
  Zlength xs = written /\
  forall idx, 0 <= idx < written -> Znth idx xs 0 = 0.

Definition CountsZeroFull (k : Z) (xs : list Z) : Prop :=
  Zlength xs = k /\
  forall idx, 0 <= idx < k -> Znth idx xs 0 = 0.

Definition CopyCountsPrefix
    (src old dst : list Z) (written k : Z) : Prop :=
  (forall idx, 0 <= idx < written -> Znth idx dst 0 = Znth idx src 0) /\
  (forall idx, written <= idx < k -> Znth idx dst 0 = Znth idx old 0).

(** Safety facts for the mutable prefix state.  The mathematical meanings of
    [answer], [seen], and [good] are intentionally absent. *)
Definition ChoosingPrefixDataSafe
    (colors costs : list Z) (limit k : Z) (seen good : list Z) : Prop :=
  0 <= limit <= Zlength colors /\
  Zlength costs = Zlength colors /\
  CountArraySafe seen k limit /\
  CountArraySafe good k limit.

(** Functional meaning of a processed prefix, independent of C array shape
    and machine-integer bounds. *)
Definition ChoosingPrefixState
    (colors costs : list Z) (limit k p answer : Z)
    (seen good : list Z) : Prop :=
  answer = choosing_pair_count colors costs p limit /\
  (forall color,
      0 <= color < k ->
      Znth color seen 0 = color_count colors limit color) /\
  (forall color,
      0 <= color < k ->
      Znth color good 0 = good_color_count colors costs limit p color).

Definition ChoosingInnsAnswer
    (colors costs : list Z) (n k p answer : Z) : Prop :=
  answer = choosing_pair_count colors costs p n.

Require Import Coq.micromega.Psatz.
Lemma CountsZeroPrefix_nil : CountsZeroPrefix nil 0.
Proof.
  unfold CountsZeroPrefix.
  split.
  - rewrite Zlength_nil. reflexivity.
  - intros idx Hidx. lia.
Qed.
Lemma CountsZeroPrefix_snoc_zero :
  forall xs i,
    CountsZeroPrefix xs i ->
    0 <= i ->
    CountsZeroPrefix (xs ++ [0]) (i + 1).
Proof.
  intros xs i [Hlen Hzero] Hi.
  unfold CountsZeroPrefix.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros idx Hidx.
    destruct (Z_lt_ge_dec idx i) as [Hlt | Hge].
    + rewrite app_Znth1.
      * apply Hzero. lia.
      * rewrite Hlen. lia.
    + assert (idx = i) by lia.
      subst idx.
      rewrite app_Znth2.
      * rewrite Hlen.
        replace (i - i) with 0 by lia.
        reflexivity.
      * rewrite Hlen. lia.
Qed.
Lemma CountsZeroPrefix_to_full :
  forall xs k,
    CountsZeroPrefix xs k ->
    CountsZeroFull k xs.
Proof.
  intros xs k H.
  exact H.
Qed.
Lemma CopyCountsPrefix_zero :
  forall src old k,
    Zlength src = k ->
    Zlength old = k ->
    CopyCountsPrefix src old old 0 k.
Proof.
  unfold CopyCountsPrefix.
  intros src old k Hsrc Hold.
  split.
  - intros idx Hidx. lia.
  - intros idx Hidx. reflexivity.
Qed.
Lemma CopyCountsPrefix_step_replace :
  forall src old dst i k,
    CopyCountsPrefix src old dst i k ->
    Zlength dst = k ->
    0 <= i < k ->
    CopyCountsPrefix src old (replace_Znth i (Znth i src 0) dst) (i + 1) k.
Proof.
  unfold CopyCountsPrefix.
  intros src old dst i k (Hdone & Hrest) Hdst Hi.
  split.
  - intros idx Hidx.
    destruct (Z.eq_dec idx i) as [Heq | Hneq].
    + subst idx.
      rewrite Znth_replace_Znth_Same by (rewrite Hdst; lia).
      reflexivity.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Hdst; lia).
      apply Hdone. lia.
  - intros idx Hidx.
    rewrite Znth_replace_Znth_Diff by (try rewrite Hdst; lia).
    apply Hrest. lia.
Qed.
Lemma CopyCountsPrefix_full_eq :
  forall src old dst i k,
    CopyCountsPrefix src old dst i k ->
    Zlength src = k ->
    Zlength dst = k ->
    i >= k ->
    i <= k ->
    dst = src.
Proof.
  unfold CopyCountsPrefix.
  intros src old dst i k (Hdone & Hrest) Hsrc Hdst Hge Hle.
  apply (proj2 (list_eq_ext dst src 0)).
  split; [lia |].
  intros idx Hidx.
  apply Hdone. lia.
Qed.
Lemma replace_Znth_preserves_bounds :
  forall xs i v k lo hi,
    Zlength xs = k ->
    0 <= i < k ->
    lo <= v <= hi ->
    (forall idx, 0 <= idx < k -> lo <= Znth idx xs 0 <= hi) ->
    forall idx,
      0 <= idx < k ->
      lo <= Znth idx (replace_Znth i v xs) 0 <= hi.
Proof.
  intros xs i v k lo hi Hlen Hi Hv Hxs idx Hidx.
  destruct (Z.eq_dec idx i) as [Heq | Hneq].
  - subst idx.
    rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    exact Hv.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
    apply Hxs. lia.
Qed.
Lemma CountArraySafe_weaken_limit :
  forall xs k old_limit new_limit,
    CountArraySafe xs k old_limit ->
    old_limit <= new_limit ->
    CountArraySafe xs k new_limit.
Proof.
  unfold CountArraySafe.
  intros xs k old_limit new_limit [Hlen Hbounds] Hle.
  split; [exact Hlen |].
  intros idx Hidx.
  specialize (Hbounds idx Hidx).
  lia.
Qed.
Lemma CountArraySafe_increment_at :
  forall xs k limit c,
    CountArraySafe xs k limit ->
    0 <= c < k ->
    CountArraySafe
      (replace_Znth c (Znth c xs 0 + 1) xs) k (limit + 1).
Proof.
  unfold CountArraySafe.
  intros xs k limit c [Hlen Hbounds] Hc.
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - eapply replace_Znth_preserves_bounds with (lo := 0) (hi := limit + 1).
    + exact Hlen.
    + exact Hc.
    + specialize (Hbounds c Hc). lia.
    + intros idx Hidx. specialize (Hbounds idx Hidx). lia.
Qed.
Lemma ChoosingPrefixDataSafe_step_affordable_after_copy :
  forall colors costs i k seen good c,
    ChoosingPrefixDataSafe colors costs i k seen good ->
    i < Zlength colors ->
    0 <= c < k ->
    ChoosingPrefixDataSafe colors costs (i + 1) k
      (replace_Znth c (Znth c seen 0 + 1) seen)
      (replace_Znth c (Znth c seen 0 + 1) seen).
Proof.
  unfold ChoosingPrefixDataSafe.
  intros colors costs i k seen good c
    [Hlimit [Hcosts [Hseen Hgood]]] Hi Hc.
  split; [lia |].
  split; [exact Hcosts |].
  split.
  - now apply CountArraySafe_increment_at.
  - now apply CountArraySafe_increment_at.
Qed.
Lemma ChoosingPrefixDataSafe_step_expensive :
  forall colors costs i k seen good c,
    ChoosingPrefixDataSafe colors costs i k seen good ->
    i < Zlength colors ->
    0 <= c < k ->
    ChoosingPrefixDataSafe colors costs (i + 1) k
      (replace_Znth c (Znth c seen 0 + 1) seen) good.
Proof.
  unfold ChoosingPrefixDataSafe.
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
  forall colors costs p,
    choosing_pair_count colors costs p 0 = 0.
Proof.
  intros.
  unfold choosing_pair_count, choosing_pairs_up_to, zrange.
  simpl.
  reflexivity.
Qed.
Lemma color_count_zero :
  forall colors color,
    color_count colors 0 color = 0.
Proof.
  intros.
  unfold color_count, zrange.
  simpl.
  reflexivity.
Qed.
Lemma good_color_count_zero :
  forall colors costs p color,
    good_color_count colors costs 0 p color = 0.
Proof.
  intros.
  unfold good_color_count, zrange.
  simpl.
  reflexivity.
Qed.
Lemma CountsZeroFull_to_ChoosingPrefixState_zero :
  forall colors costs k p seen good,
    CountsZeroFull k seen ->
    CountsZeroFull k good ->
    ChoosingPrefixState colors costs 0 k p 0 seen good.
Proof.
  intros colors costs k p seen good Hseen Hgood.
  destruct Hseen as [_ Hseen_zero].
  destruct Hgood as [_ Hgood_zero].
  unfold ChoosingPrefixState.
  split.
  - rewrite choosing_pair_count_zero; reflexivity.
  - split.
    + intros color Hcolor.
      rewrite Hseen_zero by lia.
      rewrite color_count_zero.
      reflexivity.
    + intros color Hcolor.
      rewrite Hgood_zero by lia.
      rewrite good_color_count_zero.
      reflexivity.
Qed.
Lemma CountsZeroFull_to_CountArraySafe_zero :
  forall k xs,
    CountsZeroFull k xs ->
    CountArraySafe xs k 0.
Proof.
  intros k xs [Hlen Hzero].
  split; [exact Hlen |].
  intros idx Hidx.
  rewrite Hzero by lia.
  lia.
Qed.
Lemma CountsZeroFull_to_ChoosingPrefixDataSafe_zero :
  forall colors costs k seen good,
    CountsZeroFull k seen ->
    CountsZeroFull k good ->
    Zlength costs = Zlength colors ->
    ChoosingPrefixDataSafe colors costs 0 k seen good.
Proof.
  intros colors costs k seen good Hseen Hgood Hcosts.
  unfold ChoosingPrefixDataSafe.
  split.
  - pose proof (Zlength_nonneg colors); lia.
  - split; [exact Hcosts |].
    split.
    + now apply CountsZeroFull_to_CountArraySafe_zero.
    + now apply CountsZeroFull_to_CountArraySafe_zero.
Qed.
Lemma CountsZeroFull_bounds_zero :
  forall k xs idx,
    CountsZeroFull k xs ->
    0 <= idx < k ->
    0 <= Znth idx xs 0 <= 0.
Proof.
  intros k xs idx Hfull Hidx.
  destruct Hfull as [_ Hzero].
  rewrite Hzero by lia.
  lia.
Qed.
Lemma ChoosingPrefixState_to_ChoosingInnsAnswer_full :
  forall colors costs n k p answer seen good,
    Zlength colors = n ->
    ChoosingPrefixState colors costs n k p answer seen good ->
    1 <= k ->
    ChoosingInnsAnswer colors costs n k p answer.
Proof.
  intros colors costs n k p answer seen good Hcolors Hstate Hk.
  unfold ChoosingPrefixState in Hstate.
  unfold ChoosingInnsAnswer.
  exact (proj1 Hstate).
Qed.
Lemma zrange_length_nonneg :
  forall n,
    0 <= n ->
    Zlength (zrange n) = n.
Proof.
  intros n Hn.
  unfold zrange.
  rewrite Zlength_correct, length_map, length_seq.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma zrange_snoc :
  forall n,
    0 <= n ->
    zrange (n + 1) = zrange n ++ [n].
Proof.
  intros n Hn.
  unfold zrange.
  replace (Z.to_nat (n + 1)) with (Z.to_nat n + 1)%nat.
  2:{ rewrite Z2Nat.inj_add by lia. reflexivity. }
  rewrite seq_app.
  rewrite map_app.
  simpl.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma zrange_In :
  forall x n,
    In x (zrange n) ->
    0 <= x < n.
Proof.
  intros x n H.
  unfold zrange in H.
  apply in_map_iff in H as [m [Hx Hm]].
  subst x.
  apply in_seq in Hm.
  destruct (Z_lt_ge_dec n 0) as [Hneg | Hnonneg].
  - destruct n as [|p|p]; simpl in Hm; lia.
  - simpl in Hm.
    destruct Hm as [_ Hm].
    apply Nat2Z.inj_lt in Hm.
    rewrite Z2Nat.id in Hm by lia.
    lia.
Qed.
Lemma zrange_between_snoc :
  forall lo hi,
    lo <= hi ->
    zrange_between lo hi = zrange_between lo (hi - 1) ++ [hi].
Proof.
  intros lo hi Hle.
  unfold zrange_between.
  replace (hi - 1 - lo + 1) with (hi - lo) by lia.
  replace (hi - lo + 1) with ((hi - lo) + 1) by lia.
  replace (Z.to_nat (hi - lo + 1)) with (Z.to_nat (hi - lo) + 1)%nat.
  2:{ rewrite Z2Nat.inj_add by lia. reflexivity. }
  rewrite seq_app.
  rewrite map_app.
  simpl.
  rewrite Z2Nat.id by lia.
  replace (lo + (hi - lo)) with hi by lia.
  reflexivity.
Qed.
Lemma affordable_betweenb_hi_true :
  forall costs p lo hi,
    lo <= hi ->
    Znth hi costs 0 <= p ->
    affordable_betweenb costs p lo hi = true.
Proof.
  intros costs p lo hi Hle Hcost.
  unfold affordable_betweenb.
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
    affordable_betweenb costs p lo hi =
    affordable_betweenb costs p lo (hi - 1).
Proof.
  intros costs p lo hi Hle Hcost.
  unfold affordable_betweenb.
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
    affordable_betweenb costs p i i = false.
Proof.
  intros costs p i Hcost.
  unfold affordable_betweenb, zrange_between.
  replace (i - i + 1) with 1 by lia.
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
    choosing_pairs_up_to (n + 1) =
    choosing_pairs_up_to n ++ map (fun left => (left, n)) (zrange n).
Proof.
  intros n Hn.
  unfold choosing_pairs_up_to at 1.
  rewrite zrange_snoc by lia.
  rewrite flat_map_app.
  simpl.
  unfold choosing_pairs_up_to.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma choosing_pairs_up_to_Zlength_twice :
  forall n,
    0 <= n ->
    2 * Zlength (choosing_pairs_up_to n) = n * (n - 1).
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
      (Zlength (map (fun left : Z => (left, Z.of_nat m)) (zrange (Z.of_nat m))))
      with (Zlength (zrange (Z.of_nat m))).
    2:{ rewrite !Zlength_correct, length_map. reflexivity. }
    rewrite zrange_length_nonneg by lia.
    nia.
Qed.
Lemma choosing_pair_count_prefix_bound :
  forall colors costs p limit n,
    0 <= limit <= n ->
    n <= 200000 ->
    0 <= choosing_pair_count colors costs p limit <= 19999900000.
Proof.
  intros colors costs p limit n Hlimit Hn.
  unfold choosing_pair_count.
  split.
  - apply Nat2Z.is_nonneg.
  - assert (Hfilter :
        Z.of_nat
          (length
             (filter (choosing_pairb colors costs p)
                (choosing_pairs_up_to limit))) <=
        Zlength (choosing_pairs_up_to limit)).
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
             (filter (choosing_pairb colors costs p)
                (choosing_pairs_up_to limit)))
        <= 2 * Zlength (choosing_pairs_up_to limit)) by lia.
    rewrite Htwice in H.
    assert (limit * (limit - 1) <= 2 * 19999900000) by nia.
    lia.
Qed.
Lemma color_count_snoc :
  forall colors i color,
    0 <= i ->
    color_count colors (i + 1) color =
    color_count colors i color +
    (if Z.eqb (Znth i colors 0) color then 1 else 0).
Proof.
  intros colors i color Hi.
  unfold color_count.
  rewrite zrange_snoc by lia.
  rewrite filter_app, length_app.
  rewrite Nat2Z.inj_add.
  simpl.
  destruct (Z.eqb (Znth i colors 0) color); simpl; lia.
Qed.
Lemma good_color_count_affordable_as_color_count :
  forall colors costs i p color,
    0 <= i ->
    Znth i costs 0 <= p ->
    good_color_count colors costs (i + 1) p color =
    color_count colors (i + 1) color.
Proof.
  intros colors costs i p color Hi Hcost.
  unfold good_color_count, color_count.
  assert (Hf :
    filter
      (fun idx : Z =>
         Z.eqb (Znth idx colors 0) color &&
         affordable_betweenb costs p idx (i + 1 - 1)) 
      (zrange (i + 1)) =
    filter (fun idx : Z => Z.eqb (Znth idx colors 0) color)
      (zrange (i + 1))).
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
  forall colors costs i p color,
    0 <= i ->
    p < Znth i costs 0 ->
    good_color_count colors costs (i + 1) p color =
    good_color_count colors costs i p color.
Proof.
  intros colors costs i p color Hi Hcost.
  unfold good_color_count.
  rewrite zrange_snoc by lia.
  rewrite filter_app, length_app.
  assert (Hf :
    filter
      (fun idx : Z =>
         Z.eqb (Znth idx colors 0) color &&
         affordable_betweenb costs p idx (i + 1 - 1)) 
      (zrange i) =
    filter
      (fun idx : Z =>
         Z.eqb (Znth idx colors 0) color &&
         affordable_betweenb costs p idx (i - 1)) 
      (zrange i)).
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
  forall colors costs p i c,
    0 <= i ->
    c = Znth i colors 0 ->
    Znth i costs 0 <= p ->
    choosing_pair_count colors costs p (i + 1) =
    choosing_pair_count colors costs p i + color_count colors i c.
Proof.
  intros colors costs p i c Hi Hc Hcost.
  unfold choosing_pair_count.
  rewrite choosing_pairs_up_to_snoc by lia.
  rewrite filter_app, length_app, Nat2Z.inj_add.
  f_equal.
  unfold color_count.
  assert (Hmap :
    filter (choosing_pairb colors costs p)
      (map (fun left : Z => (left, i)) (zrange i)) =
    map (fun left : Z => (left, i))
      (filter (fun idx : Z => Z.eqb (Znth idx colors 0) c) (zrange i))).
  {
    apply filter_map_ext_in.
    intros left Hleft.
    apply zrange_In in Hleft.
    unfold choosing_pairb, same_colorb.
    rewrite <- Hc.
    rewrite affordable_betweenb_hi_true by lia.
    rewrite andb_true_r.
    reflexivity.
  }
  rewrite Hmap, length_map.
  reflexivity.
Qed.
Lemma choosing_pair_count_snoc_expensive :
  forall colors costs p i c,
    0 <= i ->
    c = Znth i colors 0 ->
    p < Znth i costs 0 ->
    choosing_pair_count colors costs p (i + 1) =
    choosing_pair_count colors costs p i +
    good_color_count colors costs i p c.
Proof.
  intros colors costs p i c Hi Hc Hcost.
  unfold choosing_pair_count.
  rewrite choosing_pairs_up_to_snoc by lia.
  rewrite filter_app, length_app, Nat2Z.inj_add.
  f_equal.
  unfold good_color_count.
  assert (Hmap :
    filter (choosing_pairb colors costs p)
      (map (fun left : Z => (left, i)) (zrange i)) =
    map (fun left : Z => (left, i))
      (filter
        (fun idx : Z =>
          Z.eqb (Znth idx colors 0) c &&
          affordable_betweenb costs p idx (i - 1)) (zrange i))).
  {
    apply filter_map_ext_in.
    intros left Hleft.
    apply zrange_In in Hleft.
    unfold choosing_pairb, same_colorb.
    rewrite <- Hc.
    rewrite affordable_betweenb_extend_expensive by lia.
    reflexivity.
  }
  rewrite Hmap, length_map.
  reflexivity.
Qed.
Lemma ChoosingPrefixState_answer_bound :
  forall colors costs limit k p answer seen good n,
    ChoosingPrefixDataSafe colors costs limit k seen good ->
    ChoosingPrefixState colors costs limit k p answer seen good ->
    limit <= n ->
    n <= 200000 ->
    0 <= answer <= 19999900000.
Proof.
  intros colors costs limit k p answer seen good n Hsafe Hstate Hlimit Hn.
  unfold ChoosingPrefixDataSafe in Hsafe.
  destruct Hsafe as [Hsafe_limit _].
  unfold ChoosingPrefixState in Hstate.
  destruct Hstate as [Hanswer _].
  rewrite Hanswer.
  apply choosing_pair_count_prefix_bound with (n := n).
  - lia.
  - exact Hn.
Qed.
Lemma ChoosingPrefixState_step_affordable_after_copy :
  forall colors costs i k p old_answer answer seen good seen_next c,
    ChoosingPrefixDataSafe colors costs i k seen good ->
    ChoosingPrefixState colors costs i k p old_answer seen good ->
    0 <= i < Zlength colors ->
    0 <= c < k ->
    c = Znth i colors 0 ->
    Znth i costs 0 <= p ->
    answer = old_answer + Znth c seen 0 ->
    seen_next = replace_Znth c (Znth c seen 0 + 1) seen ->
    ChoosingPrefixState colors costs (i + 1) k p answer seen_next seen_next.
Proof.
  intros colors costs i k p old_answer answer seen good seen_next c
         Hsafe Hstate Hi Hc_range Hc Hcost Hanswer Hseen_next.
  unfold ChoosingPrefixDataSafe in Hsafe.
  destruct Hsafe as [_ [_ [[Hseen_len _] [Hgood_len _]]]].
  unfold ChoosingPrefixState in Hstate.
  destruct Hstate as [Hold_answer [Hseen_count Hgood_count]].
  subst answer.
  subst seen_next.
  assert (Hseen_next_count :
    forall color,
      0 <= color < k ->
      Znth color (replace_Znth c (Znth c seen 0 + 1) seen) 0 =
      color_count colors (i + 1) color).
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
  unfold ChoosingPrefixState.
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
  forall colors costs i k p old_answer answer seen good seen_next c,
    ChoosingPrefixDataSafe colors costs i k seen good ->
    ChoosingPrefixState colors costs i k p old_answer seen good ->
    0 <= i < Zlength colors ->
    0 <= c < k ->
    c = Znth i colors 0 ->
    p < Znth i costs 0 ->
    answer = old_answer + Znth c good 0 ->
    seen_next = replace_Znth c (Znth c seen 0 + 1) seen ->
    ChoosingPrefixState colors costs (i + 1) k p answer seen_next good.
Proof.
  intros colors costs i k p old_answer answer seen good seen_next c
         Hsafe Hstate Hi Hc_range Hc Hcost Hanswer Hseen_next.
  unfold ChoosingPrefixDataSafe in Hsafe.
  destruct Hsafe as [_ [_ [[Hseen_len _] [Hgood_len _]]]].
  unfold ChoosingPrefixState in Hstate.
  destruct Hstate as [Hold_answer [Hseen_count Hgood_count]].
  subst answer.
  subst seen_next.
  unfold ChoosingPrefixState.
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
