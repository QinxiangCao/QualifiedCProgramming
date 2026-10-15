Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition MinimumEqualDistance (a : list Z) (d : Z) : Prop :=
  min_value_of_subset Z.le
    (fun positions : Z * Z =>
      0 <= fst positions < snd positions /\
      snd positions < Zlength a /\
      Znth (fst positions) a 0 = Znth (snd positions) a 0)
    (fun positions => snd positions - fst positions - 1) d.

Definition Pre (a : list Z) : Prop :=
  2 <= Zlength a <= 100000 /\
  Forall (fun x => 1 <= x <= Zlength a) a /\
  exists x i j, 0 <= i < Zlength a /\ 0 <= j < Zlength a /\ i <> j /\
    Znth i a 0 = x /\ Znth j a 0 = x.

Definition ArrangementSpec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      Permutation a (fst candidate) /\
      MinimumEqualDistance (fst candidate) (snd candidate))
    snd out.

Definition CountPrefix (a : list Z) (i : Z) (counts : list Z) : Prop :=
  Zlength counts = Zlength a + 1 /\
  forall value,
    0 <= value <= Zlength a ->
    Znth value counts 0 =
      Z.of_nat (count_occ Z.eq_dec (sublist 0 i a) value).

Definition MaximumFrequencyPrefix
    (counts : list Z) (i mx multiplicity : Z) : Prop :=
  1 <= i <= Zlength counts /\
  (forall value,
    1 <= value < i ->
    Znth value counts 0 <= mx) /\
  ((i = 1 /\ mx = 0 /\ multiplicity = 0) \/
   (1 < i /\
    (exists value,
      1 <= value < i /\ Znth value counts 0 = mx) /\
    multiplicity =
      Z.of_nat (count_occ Z.eq_dec (sublist 1 i counts) mx))).

(* This is the closed-form characterization of the arrangement optimum used
   by the solver: [mx] is the largest input multiplicity and [multiplicity]
   is the number of values attaining it.  Unlike a loop mirror, the
   characterization depends only on the complete mathematical frequency
   profile of the input. *)
Definition Spec (a : list Z) (out : Z) : Prop :=
  exists counts mx multiplicity,
    CountPrefix a (Zlength a) counts /\
    MaximumFrequencyPrefix counts (Zlength a + 1) mx multiplicity /\
    out = (Zlength a - multiplicity) / (mx - 1) - 1.

Lemma terminal_frequency_summary_implies_Spec :
  forall a counts mx multiplicity,
    CountPrefix a (Zlength a) counts ->
    MaximumFrequencyPrefix counts (Zlength a + 1) mx multiplicity ->
    Spec a ((Zlength a - multiplicity) / (mx - 1) - 1).
Proof.
  intros a counts mx multiplicity Hcounts Hmaximum.
  unfold Spec.
  exists counts, mx, multiplicity.
  split; [exact Hcounts |].
  split; [exact Hmaximum | reflexivity].
Qed.

Require Import Coq.micromega.Lia.
Lemma length_replace_nth__counting_invariant :
  forall {A : Type} (n : nat) (l : list A) (v : A),
    length (replace_nth n l v) = length l.
Proof.
  intros A n l.
  revert n.
  induction l as [| x l IH]; intros n v; destruct n; simpl; auto.
Qed.
Lemma Zlength_replace_Znth__counting_invariant :
  forall {A : Type} (i : Z) (l : list A) (v : A),
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros.
  unfold replace_Znth.
  repeat rewrite Zlength_correct.
  rewrite length_replace_nth__counting_invariant.
  reflexivity.
Qed.
Lemma count_prefix_step__counting_invariant :
  forall (a counts : list Z) (i : Z),
    0 <= i < Zlength a ->
    0 <= Znth i a 0 <= Zlength a ->
    CountPrefix a i counts ->
    CountPrefix a (i + 1)
      (replace_Znth (Znth i a 0) (Znth (Znth i a 0) counts 0 + 1) counts).
Proof.
  intros a counts i Hi Hvalue Hprefix.
  unfold CountPrefix in Hprefix |- *.
  destruct Hprefix as [Hlength Hprefix].
  split.
  - rewrite Zlength_replace_Znth__counting_invariant.
    exact Hlength.
  - intros value Hvalue_bounds.
    assert (Hindex : 0 <= Znth i a 0 < Zlength counts) by lia.
    assert (Hvalue_index : 0 <= value < Zlength counts) by lia.
    rewrite (sublist_split 0 (i + 1) i a) by lia.
    rewrite (sublist_single 0 i a) by lia.
    rewrite count_occ_app.
    simpl.
    destruct (Z.eq_dec (Znth i a 0) value) as [Heq | Hneq].
    + subst value.
      rewrite Znth_replace_Znth_Same by exact Hindex.
      rewrite Hprefix by lia.
      lia.
    + rewrite Znth_replace_Znth_Diff by (try exact Hindex; try exact Hvalue_index; lia).
      rewrite Hprefix by lia.
      destruct (Z.eq_dec value (Znth i a 0)) as [Heq' | Hneq'].
      * exfalso.
        apply Hneq.
        symmetry.
        exact Heq'.
      * f_equal.
        lia.
Qed.
Lemma maximum_frequency_prefix_zero__counting_invariant :
  forall counts : list Z,
    1 <= Zlength counts ->
    MaximumFrequencyPrefix counts 1 0 0.
Proof.
  intros counts Hlength.
  unfold MaximumFrequencyPrefix.
  split; [lia |].
  split.
  - intros value Hvalue.
    lia.
  - left.
    repeat split; reflexivity.
Qed.
Lemma sublist_snoc_at__frequency_transitions :
  forall (l : list Z) lo i,
    0 <= lo <= i ->
    i < Zlength l ->
    sublist lo (i + 1) l = sublist lo i l ++ Znth i l 0 :: nil.
Proof.
  intros l lo i Hlo Hi.
  rewrite (sublist_split lo (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  reflexivity.
Qed.
Lemma count_occ_sublist_zero_above__frequency_transitions :
  forall (l : list Z) lo hi mx x,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> Znth k l 0 <= mx) ->
    mx < x ->
    count_occ Z.eq_dec (sublist lo hi l) x = 0%nat.
Proof.
  intros l lo hi mx x Hlohi Hhi Hbound Habove.
  apply (proj1 (count_occ_not_In Z.eq_dec (sublist lo hi l) x)).
  intros Hin.
  destruct (In_nth (sublist lo hi l) x 0 Hin)
    as [n [Hn_length Hnth]].
  assert (Hn_range : 0 <= Z.of_nat n < hi - lo).
  { rewrite <- (Zlength_sublist lo hi l) by lia.
    rewrite Zlength_correct.
    lia. }
  pose proof (Znth_sublist 0 lo (Z.of_nat n) hi l ltac:(lia) Hn_range)
    as Hsublist_nth.
  unfold Znth in Hsublist_nth at 1.
  rewrite Nat2Z.id in Hsublist_nth.
  specialize (Hbound (Z.of_nat n + lo) ltac:(lia)).
  rewrite Hnth in Hsublist_nth.
  lia.
Qed.
Lemma maximum_frequency_prefix_raise__frequency_transitions :
  forall (counts : list Z) i mx c,
    1 <= i ->
    i < Zlength counts ->
    MaximumFrequencyPrefix counts i mx c ->
    mx < Znth i counts 0 ->
    MaximumFrequencyPrefix counts (i + 1) (Znth i counts 0) 1.
Proof.
  intros counts i mx c Hi Hilen Hprefix Hraise.
  unfold MaximumFrequencyPrefix in *.
  destruct Hprefix as [[Hi_lower Hi_upper] [Hdominates Hmaximum]].
  split.
  - lia.
  - split.
    + intros value Hvalue.
      destruct (Z_lt_ge_dec value i) as [Hold | Hnew].
      * specialize (Hdominates value ltac:(lia)). lia.
      * assert (value = i) by lia. subst value. lia.
    + right.
      split; [lia |].
      split.
      * exists i. lia.
      * rewrite sublist_snoc_at__frequency_transitions by lia.
        rewrite count_occ_app.
        rewrite (count_occ_sublist_zero_above__frequency_transitions
          counts 1 i mx (Znth i counts 0)); try lia.
        2: { intros k Hk. apply Hdominates. lia. }
        simpl.
        destruct (Z.eq_dec (Znth i counts 0) (Znth i counts 0));
          [| contradiction].
        reflexivity.
Qed.
Lemma maximum_frequency_prefix_tie__frequency_transitions :
  forall (counts : list Z) i mx c,
    1 <= i ->
    i < Zlength counts ->
    MaximumFrequencyPrefix counts i mx c ->
    Znth i counts 0 = mx ->
    MaximumFrequencyPrefix counts (i + 1) mx (c + 1).
Proof.
  intros counts i mx c Hi Hilen Hprefix Htie.
  unfold MaximumFrequencyPrefix in *.
  destruct Hprefix as [[Hi_lower Hi_upper] [Hdominates Hmaximum]].
  split.
  - lia.
  - split.
    + intros value Hvalue.
      destruct (Z_lt_ge_dec value i) as [Hold | Hnew].
      * apply Hdominates. lia.
      * assert (value = i) by lia. subst value. lia.
    + right.
      split; [lia |].
      split.
      * exists i. lia.
      * assert (Hold_count :
          c = Z.of_nat (count_occ Z.eq_dec (sublist 1 i counts) mx)).
        { destruct Hmaximum as [[Hi_one [Hmx_zero Hc_zero]] |
                                [Hi_many [Hwitness Hcount]]].
          - subst i mx c.
            replace (sublist 1 1 counts) with (@nil Z).
            + reflexivity.
            + unfold sublist.
              symmetry.
              apply skipn_all2.
              rewrite length_firstn.
              lia.
          - exact Hcount. }
        rewrite sublist_snoc_at__frequency_transitions by lia.
        rewrite count_occ_app.
        simpl.
        rewrite Htie.
        destruct (Z.eq_dec mx mx); [| contradiction].
        rewrite Nat2Z.inj_add.
        simpl.
        lia.
Qed.
Lemma maximum_frequency_prefix_below__frequency_transitions :
  forall (counts : list Z) i mx c,
    1 <= i ->
    i < Zlength counts ->
    MaximumFrequencyPrefix counts i mx c ->
    0 <= Znth i counts 0 ->
    Znth i counts 0 <= mx ->
    Znth i counts 0 <> mx ->
    MaximumFrequencyPrefix counts (i + 1) mx c.
Proof.
  intros counts i mx c Hi Hilen Hprefix Hnonnegative Hbelow Hunequal.
  unfold MaximumFrequencyPrefix in *.
  destruct Hprefix as [[Hi_lower Hi_upper] [Hdominates Hmaximum]].
  split.
  - lia.
  - split.
    + intros value Hvalue.
      destruct (Z_lt_ge_dec value i) as [Hold | Hnew].
      * apply Hdominates. lia.
      * assert (value = i) by lia. subst value. exact Hbelow.
    + right.
      split; [lia |].
      destruct Hmaximum as [[Hi_one [Hmx_zero Hc_zero]] |
                            [Hi_many [Hwitness Hcount]]].
      * subst i mx c. exfalso. apply Hunequal. lia.
      * split.
        -- destruct Hwitness as [value [Hvalue Hvalue_eq]].
           exists value. split; [lia | exact Hvalue_eq].
        -- rewrite sublist_snoc_at__frequency_transitions by lia.
           rewrite count_occ_app.
           simpl.
           destruct (Z.eq_dec (Znth i counts 0) mx);
             [contradiction |].
           simpl.
           replace (count_occ Z.eq_dec (sublist 1 i counts) mx + 0)%nat
             with (count_occ Z.eq_dec (sublist 1 i counts) mx) by lia.
           exact Hcount.
Qed.
Lemma two_occurrences_nat_count_occ__terminal_result :
  forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y})
    (l : list A) (x d : A) (p q : nat),
    (p < length l)%nat ->
    (q < length l)%nat ->
    p <> q ->
    nth p l d = x ->
    nth q l d = x ->
    (2 <= count_occ dec l x)%nat.
Proof.
  intros A dec l.
  induction l as [| a l IH]; intros x d p q Hp Hq Hpq Hpx Hqx.
  - simpl in Hp. lia.
  - destruct p as [| p], q as [| q].
    + contradiction.
    + simpl in Hpx. subst a.
      simpl in Hq, Hqx |- *.
      destruct (dec x x) as [_ | Hxx]; [| contradiction].
      assert (Hin : In (nth q l d) l) by (apply nth_In; lia).
      rewrite Hqx in Hin.
      apply (proj1 (count_occ_In dec l x)) in Hin.
      lia.
    + simpl in Hqx. subst a.
      simpl in Hp, Hpx |- *.
      destruct (dec x x) as [_ | Hxx]; [| contradiction].
      assert (Hin : In (nth p l d) l) by (apply nth_In; lia).
      rewrite Hpx in Hin.
      apply (proj1 (count_occ_In dec l x)) in Hin.
      lia.
    + simpl in Hp, Hq, Hpx, Hqx.
      assert (Hpq' : p <> q) by congruence.
      specialize (IH x d p q ltac:(lia) ltac:(lia) Hpq' Hpx Hqx).
      simpl.
      destruct (dec a x); lia.
Qed.
Lemma two_distinct_Znth_count_occ__terminal_result :
  forall (l : list Z) (x i j : Z),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    i <> j ->
    Znth i l 0 = x ->
    Znth j l 0 = x ->
    (2 <= count_occ Z.eq_dec l x)%nat.
Proof.
  intros l x i j Hi Hj Hij Hix Hjx.
  eapply (two_occurrences_nat_count_occ__terminal_result
    Z Z.eq_dec l x 0 (Z.to_nat i) (Z.to_nat j)).
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  - intro Heq.
    apply Hij.
    apply (f_equal Z.of_nat) in Heq.
    repeat rewrite Z2Nat.id in Heq by lia.
    exact Heq.
  - exact Hix.
  - exact Hjx.
Qed.
Lemma Znth_in_range_In__terminal_result :
  forall (A : Type) (l : list A) (i : Z) (d : A),
    0 <= i < Zlength l ->
    In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_In.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.
Lemma terminal_frequency_bounds__terminal_result :
  forall (a counts : list Z) (n i mx c : Z),
    n = Zlength a ->
    Pre a ->
    1 <= i ->
    i <= n + 1 ->
    i > n ->
    0 <= mx ->
    mx <= n ->
    0 <= c ->
    c <= i - 1 ->
    CountPrefix a n counts ->
    MaximumFrequencyPrefix counts i mx c ->
    i = n + 1 /\ 2 <= mx <= n /\ 1 <= c <= n.
Proof.
  intros a counts n i mx c Hn Hpre Hi_lower Hi_upper Hi_done
    Hmx_lower Hmx_upper Hc_lower Hc_upper Hcounts Hmaximum.
  assert (Hi_eq : i = n + 1) by lia.
  unfold Pre in Hpre.
  destruct Hpre as
    [Ha_length [Ha_values [x [p [q [Hp [Hq [Hpq [Hpx Hqx]]]]]]]]].
  unfold CountPrefix in Hcounts.
  destruct Hcounts as [Hcounts_length Hcounts_value].
  assert (Hxin : In x a).
  { rewrite <- Hpx.
    apply Znth_in_range_In__terminal_result.
    exact Hp. }
  pose proof (proj1 (@Forall_forall Z
    (fun z => 1 <= z <= Zlength a) a) Ha_values x Hxin) as Hx_bounds.
  rewrite <- Hn in Hx_bounds.
  assert (Htwo_nat : (2 <= count_occ Z.eq_dec a x)%nat).
  { eapply two_distinct_Znth_count_occ__terminal_result
      with (i := p) (j := q).
    - exact Hp.
    - exact Hq.
    - exact Hpq.
    - exact Hpx.
    - exact Hqx. }
  assert (Hsublist : sublist 0 n a = a).
  { rewrite Hn.
    apply sublist_self.
    reflexivity. }
  specialize (Hcounts_value x ltac:(lia)).
  rewrite Hsublist in Hcounts_value.
  unfold MaximumFrequencyPrefix in Hmaximum.
  destruct Hmaximum as [Hmaximum_bounds [Hdominates Hmaximum_case]].
  assert (Hmx_two : 2 <= mx).
  { specialize (Hdominates x ltac:(lia)).
    rewrite Hcounts_value in Hdominates.
    apply Nat2Z.inj_le in Htwo_nat.
    simpl in Htwo_nat.
    lia. }
  assert (Hc_positive : 1 <= c).
  { destruct Hmaximum_case as
      [[Hi_one [Hmx_zero Hc_zero]] |
       [Hi_many [[value [Hvalue_bounds Hvalue_max]] Hc_count]]].
    - lia.
    - assert (Hsub_length : Zlength (sublist 1 i counts) = i - 1).
      { rewrite Zlength_sublist by lia.
        lia. }
      assert (Hvalue_index :
        0 <= value - 1 < Zlength (sublist 1 i counts)) by lia.
      assert (Hvalue_in : In mx (sublist 1 i counts)).
      { rewrite <- Hvalue_max.
        replace (Znth value counts 0)
          with (Znth (value - 1) (sublist 1 i counts) 0).
        - apply Znth_in_range_In__terminal_result.
          exact Hvalue_index.
        - rewrite (Znth_sublist 0 1 (value - 1) i counts) by lia.
          f_equal.
          lia. }
      apply (proj1 (count_occ_In Z.eq_dec (sublist 1 i counts) mx))
        in Hvalue_in.
      rewrite Hc_count.
      lia. }
  repeat split; lia.
Qed.
