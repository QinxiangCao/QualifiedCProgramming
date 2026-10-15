Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition GoodAdjacentSums (b : list Z) : Prop :=
  exists k, forall i,
    0 <= i < Zlength b - 1 ->
    Znth i b 0 + Znth (i + 1) b 0 = k.

Definition Pre (a : list Z) : Prop :=
  2 <= Zlength a <= 100 /\
  Forall (fun x => 1 <= x <= 100000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> exists b, Permutation a b /\ GoodAdjacentSums b).

Definition Occurrences (v : Z) (l : list Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec l v).

(** Mathematical meaning of the counters after scanning the prefix [0, i).
    The sentinel [-1] is outside the input range, so [y = -1] precisely
    denotes that no second value has been observed. *)
Definition PaintScanState
    (a : list Z) (i x y cx cy : Z) : Prop :=
  0 <= i <= Zlength a /\
  x = Znth 0 a 0 /\
  0 <= cx <= i /\
  0 <= cy <= i /\
  cx + cy = i /\
  (y = -1 <-> cy = 0) /\
  (y <> -1 -> y <> x) /\
  cx = Occurrences x (sublist 0 i a) /\
  (y <> -1 -> cy = Occurrences y (sublist 0 i a)) /\
  (forall j, 0 <= j < i ->
    Znth j a 0 = x \/ (y <> -1 /\ Znth j a 0 = y)).

Require Import Coq.micromega.Lia.
Lemma sublist_snoc_at_index__scan_transitions :
  forall (a : list Z) i,
    0 <= i < Zlength a ->
    sublist 0 (i + 1) a = sublist 0 i a ++ Znth i a 0 :: nil.
Proof.
  intros a i Hi.
  rewrite (sublist_split 0 (i + 1) i a) by lia.
  rewrite (@sublist_single Z 0 i a) by lia.
  reflexivity.
Qed.
Lemma occurrences_sublist_snoc_eq__scan_transitions :
  forall (a : list Z) i v,
    0 <= i < Zlength a ->
    Znth i a 0 = v ->
    Occurrences v (sublist 0 (i + 1) a) =
      Occurrences v (sublist 0 i a) + 1.
Proof.
  intros a i v Hi Hv.
  rewrite sublist_snoc_at_index__scan_transitions by exact Hi.
  unfold Occurrences.
  rewrite count_occ_app.
  simpl.
  rewrite Hv.
  destruct (Z.eq_dec v v); lia.
Qed.
Lemma occurrences_sublist_snoc_neq__scan_transitions :
  forall (a : list Z) i v,
    0 <= i < Zlength a ->
    Znth i a 0 <> v ->
    Occurrences v (sublist 0 (i + 1) a) =
      Occurrences v (sublist 0 i a).
Proof.
  intros a i v Hi Hv.
  rewrite sublist_snoc_at_index__scan_transitions by exact Hi.
  unfold Occurrences.
  rewrite count_occ_app.
  simpl.
  destruct (Z.eq_dec (Znth i a 0) v); lia.
Qed.
Lemma sublist0_In_Znth_exists__scan_transitions :
  forall (a : list Z) n v,
    0 <= n <= Zlength a ->
    In v (sublist 0 n a) ->
    exists j, 0 <= j < n /\ Znth j a 0 = v.
Proof.
  intros a n v Hn Hin.
  pose proof (In_nth (sublist 0 n a) v 0 Hin) as [k [Hk Hnth]].
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
Lemma paint_scan_state_init__scan_transitions :
  forall (a : list Z),
    PaintScanState a 0 (Znth 0 a 0) (-1) 0 0.
Proof.
  intros a.
  unfold PaintScanState, Occurrences, sublist.
  simpl.
  repeat split; try lia; try reflexivity.
  all: try apply Zlength_nonneg.
  all: intros; lia.
Qed.
Lemma paint_scan_state_step_x__scan_transitions :
  forall (a : list Z) i x y cx cy,
    0 <= i < Zlength a ->
    Znth i a 0 = x ->
    PaintScanState a i x y cx cy ->
    PaintScanState a (i + 1) x y (cx + 1) cy.
Proof.
  intros a i x y cx cy Hi Hcur Hstate.
  unfold PaintScanState in Hstate |- *.
  destruct Hstate as
    [Hib [Hx [Hcxb [Hcyb [Hsum [Hsent [Hdistinct [Hcx [Hcy Hcover]]]]]]]]].
  repeat split.
  - lia.
  - lia.
  - exact Hx.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact (proj1 Hsent).
  - exact (proj2 Hsent).
  - exact Hdistinct.
  - rewrite (occurrences_sublist_snoc_eq__scan_transitions a i x Hi Hcur).
    lia.
  - intros Hy.
    rewrite (occurrences_sublist_snoc_neq__scan_transitions a i y Hi).
    + apply Hcy; exact Hy.
    + rewrite Hcur. apply not_eq_sym. apply Hdistinct; exact Hy.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hji].
    + left; exact Hcur.
    + apply Hcover. lia.
Qed.
Lemma paint_scan_state_step_first_y__scan_transitions :
  forall (a : list Z) i x y cx cy,
    0 <= i < Zlength a ->
    1 <= Znth i a 0 ->
    y = -1 ->
    Znth i a 0 <> x ->
    PaintScanState a i x y cx cy ->
    PaintScanState a (i + 1) x (Znth i a 0) cx (cy + 1).
Proof.
  intros a i x y cx cy Hi Hpositive Hy Hcurx Hstate.
  unfold PaintScanState in Hstate |- *.
  destruct Hstate as
    [Hib [Hx [Hcxb [Hcyb [Hsum [Hsent [Hdistinct [Hcx [Hcy Hcover]]]]]]]]].
  assert (Hcy0 : cy = 0) by (apply (proj1 Hsent); exact Hy).
  assert (Hnotin : ~ In (Znth i a 0) (sublist 0 i a)).
  {
    intros Hin.
    destruct (sublist0_In_Znth_exists__scan_transitions a i (Znth i a 0))
      as [j [Hj Hjv]]; try lia; try exact Hin.
    specialize (Hcover j Hj).
    destruct Hcover as [Hjx | [Hyn Hjval]].
    - apply Hcurx. rewrite <- Hjv. exact Hjx.
    - apply Hyn. exact Hy.
  }
  assert (Holdzero : Occurrences (Znth i a 0) (sublist 0 i a) = 0).
  {
    unfold Occurrences.
    rewrite count_occ_not_In in Hnotin.
    rewrite Hnotin.
    reflexivity.
  }
  repeat split.
  - lia.
  - lia.
  - exact Hx.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - intro H; lia.
  - intro H; lia.
  - intros _. exact Hcurx.
  - rewrite (occurrences_sublist_snoc_neq__scan_transitions a i x Hi Hcurx).
    exact Hcx.
  - intros _.
    rewrite (occurrences_sublist_snoc_eq__scan_transitions a i (Znth i a 0) Hi eq_refl).
    lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hji].
    + right. split; [lia | reflexivity].
    + specialize (Hcover j ltac:(lia)).
      destruct Hcover as [Hjx | [Hyn Hjval]].
      * left; exact Hjx.
      * exfalso. apply Hyn. exact Hy.
Qed.
Lemma paint_scan_state_step_y__scan_transitions :
  forall (a : list Z) i x y cx cy,
    0 <= i < Zlength a ->
    y <> -1 ->
    Znth i a 0 = y ->
    Znth i a 0 <> x ->
    PaintScanState a i x y cx cy ->
    PaintScanState a (i + 1) x y cx (cy + 1).
Proof.
  intros a i x y cx cy Hi Hyn Hcur Hcurx Hstate.
  unfold PaintScanState in Hstate |- *.
  destruct Hstate as
    [Hib [Hx [Hcxb [Hcyb [Hsum [Hsent [Hdistinct [Hcx [Hcy Hcover]]]]]]]]].
  repeat split.
  - lia.
  - lia.
  - exact Hx.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - intro H. exfalso. apply Hyn. exact H.
  - intro H; lia.
  - exact Hdistinct.
  - rewrite (occurrences_sublist_snoc_neq__scan_transitions a i x Hi Hcurx).
    exact Hcx.
  - intros _.
    rewrite (occurrences_sublist_snoc_eq__scan_transitions a i y Hi Hcur).
    specialize (Hcy Hyn). lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hji].
    + right. split; [exact Hyn | exact Hcur].
    + apply Hcover. lia.
Qed.
Lemma good_adjacent_sums_uniform__accepted_results :
  forall (a : list Z) (x : Z),
    (forall i, 0 <= i < Zlength a -> Znth i a 0 = x) ->
    GoodAdjacentSums a.
Proof.
  intros a x Hall.
  exists (2 * x).
  intros i Hi.
  rewrite (Hall i), (Hall (i + 1)); lia.
Qed.
Lemma balanced_two_value_permutation__accepted_results :
  forall (a : list Z) (x y : Z),
    x <> y ->
    (forall i, 0 <= i < Zlength a ->
       Znth i a 0 = x \/ Znth i a 0 = y) ->
    (Z.of_nat (count_occ Z.eq_dec a y) -
       Z.of_nat (count_occ Z.eq_dec a x) <= 1) ->
    (Z.of_nat (count_occ Z.eq_dec a x) -
       Z.of_nat (count_occ Z.eq_dec a y) <= 1) ->
    exists b, Permutation a b /\ GoodAdjacentSums b.
Proof.
  intros a x y Hxy Hcover Hbal_yx Hbal_xy.
  assert (Hcover_forall : Forall (fun z => z = x \/ z = y) a).
  {
    apply (proj2 (Forall_Znth (fun z => z = x \/ z = y) 0 a)).
    exact Hcover.
  }
  assert (Hcanonical :
    forall l,
      Forall (fun z => z = x \/ z = y) l ->
      Permutation l
        (repeat x (count_occ Z.eq_dec l x) ++
         repeat y (count_occ Z.eq_dec l y))).
  {
    intros l Hl.
    induction Hl as [| z l Hz Hl IH].
    - simpl. constructor.
    - destruct Hz as [-> | ->].
      + simpl.
        destruct (Z.eq_dec x x) as [_ | Hbad];
          [| exfalso; apply Hbad; reflexivity].
        destruct (Z.eq_dec x y) as [Hbad | _];
          [exfalso; exact (Hxy Hbad) |].
        now apply perm_skip.
      + simpl.
        destruct (Z.eq_dec y x) as [Hbad | _];
          [exfalso; apply Hxy; symmetry; exact Hbad |].
        destruct (Z.eq_dec y y) as [_ | Hbad];
          [| exfalso; apply Hbad; reflexivity].
        eapply Permutation_trans.
        * apply perm_skip. exact IH.
        * apply Permutation_middle.
  }
  assert (Hequal :
    forall (n : nat) (u v : Z),
      exists b,
        Permutation (repeat u n ++ repeat v n) b /\
        (n <> O -> exists t, b = u :: t) /\
        (forall i, 0 <= i < Zlength b - 1 ->
           Znth i b 0 + Znth (i + 1) b 0 = u + v)).
  {
    intros n.
    induction n as [| n IH]; intros u v.
    - exists nil. simpl.
      split; [constructor |].
      split; [intros Hbad; contradiction |].
      intros i Hi. lia.
    - destruct (IH u v) as (b & Hperm & Hhead & Hadj).
      exists (u :: v :: b).
      split.
      + simpl.
        apply perm_skip.
        eapply Permutation_trans.
        * apply Permutation_sym. apply Permutation_middle.
        * apply perm_skip. exact Hperm.
      + split.
        * intros _. exists (v :: b). reflexivity.
        * intros i Hi.
          rewrite !Zlength_cons in Hi.
          destruct (Z.eq_dec i 0) as [-> | Hi0].
          -- rewrite Znth0_cons, Znth_cons by lia.
             rewrite Znth0_cons. lia.
          -- destruct (Z.eq_dec i 1) as [-> | Hi1].
             ++ rewrite !Znth_cons by lia.
                rewrite Znth0_cons.
                assert (n <> O).
                { intro Hn. subst n. simpl in Hperm.
                  apply Permutation_nil in Hperm. subst b. simpl in Hi. lia. }
                destruct (Hhead H) as (t & ->).
                change (v + u = u + v). lia.
             ++ rewrite !Znth_cons by lia.
                replace (i - 1 - 1) with (i - 2) by lia.
                replace (i + 1 - 1 - 1) with (i - 1) by lia.
                replace (i - 1) with (i - 2 + 1) by lia.
                apply Hadj. lia.
  }
  pose (nx := count_occ Z.eq_dec a x).
  pose (ny := count_occ Z.eq_dec a y).
  assert (Hcases : (nx = ny \/ nx = S ny \/ ny = S nx)%nat).
  {
    destruct (Nat.lt_trichotomy nx ny) as [Hlt | [Heq | Hgt]].
    - right; right. lia.
    - left. exact Heq.
    - right; left. lia.
  }
  destruct Hcases as [Heq | [Hextra_x | Hextra_y]].
  - destruct (Hequal nx x y) as (b & Hperm & _ & Hadj).
    exists b. split.
    + eapply Permutation_trans; [apply Hcanonical; exact Hcover_forall |].
      change (Permutation
        (repeat x nx ++ repeat y ny) b).
      rewrite <- Heq. exact Hperm.
    + exists (x + y). exact Hadj.
  - destruct (Hequal ny y x) as (b & Hperm & Hhead & Hadj).
    exists (x :: b). split.
    + eapply Permutation_trans; [apply Hcanonical; exact Hcover_forall |].
      unfold nx, ny in Hextra_x. rewrite Hextra_x. simpl.
      apply perm_skip.
      eapply Permutation_trans.
      * apply Permutation_app_comm.
      * exact Hperm.
    + exists (x + y). intros i Hi.
      rewrite Zlength_cons in Hi.
      destruct (Z.eq_dec i 0) as [-> | Hi0].
      * rewrite Znth0_cons, Znth_cons by lia.
        assert (ny <> O).
        { intro Hny. rewrite Hny in Hperm. simpl in Hperm.
          apply Permutation_nil in Hperm. subst b. simpl in Hi. lia. }
        destruct (Hhead H) as (t & ->).
        rewrite Znth0_cons. lia.
      * rewrite !Znth_cons by lia.
        replace (i + 1 - 1) with ((i - 1) + 1) by lia.
        specialize (Hadj (i - 1) ltac:(lia)). lia.
  - destruct (Hequal nx x y) as (b & Hperm & Hhead & Hadj).
    exists (y :: b). split.
    + eapply Permutation_trans; [apply Hcanonical; exact Hcover_forall |].
      unfold nx, ny in Hextra_y. rewrite Hextra_y.
      simpl.
      eapply Permutation_trans.
      * apply Permutation_sym. apply Permutation_middle.
      * apply perm_skip. exact Hperm.
    + exists (x + y). intros i Hi.
      rewrite Zlength_cons in Hi.
      destruct (Z.eq_dec i 0) as [-> | Hi0].
      * rewrite Znth0_cons, Znth_cons by lia.
        assert (nx <> O).
        { intro Hnx. rewrite Hnx in Hperm. simpl in Hperm.
          apply Permutation_nil in Hperm. subst b. simpl in Hi. lia. }
        destruct (Hhead H) as (t & ->).
        rewrite Znth0_cons. lia.
      * rewrite !Znth_cons by lia.
        replace (i + 1 - 1) with ((i - 1) + 1) by lia.
        apply Hadj. lia.
Qed.
Lemma good_adjacent_sums_period_two__rejected_results :
  forall (b : list Z) (j : Z),
    GoodAdjacentSums b ->
    0 <= j -> j + 2 < Zlength b ->
    Znth j b 0 = Znth (j + 2) b 0.
Proof.
  intros b j [k Hsum] Hj Hj2.
  pose proof (Hsum j ltac:(lia)) as Hsum1.
  pose proof (Hsum (j + 1) ltac:(lia)) as Hsum2.
  replace (j + 1 + 1) with (j + 2) in Hsum2 by lia.
  lia.
Qed.
Lemma Znth_drop_two__rejected_results :
  forall (j p q : Z) (l : list Z),
    0 <= j ->
    Znth (j + 2) (p :: q :: l) 0 = Znth j l 0.
Proof.
  intros j p q l Hj.
  rewrite Znth_cons by lia.
  rewrite Znth_cons by lia.
  replace (j + 2 - 1 - 1) with j by lia.
  reflexivity.
Qed.
Lemma adjacent_sums_tail_values__rejected_results :
  forall (tl : list Z) (p q k : Z),
    (forall j : Z,
        0 <= j < Zlength (p :: q :: tl) - 1 ->
        Znth j (p :: q :: tl) 0 +
        Znth (j + 1) (p :: q :: tl) 0 = k) ->
    forall z, In z (p :: q :: tl) -> z = p \/ z = q.
Proof.
  fix IH 1.
  intros [| r [| s tl]] p q k Hsum z Hz.
  - simpl in Hz.
    destruct Hz as [Hz | [Hz | []]]; subst; auto.
  - assert (Hr : r = p).
    { pose proof (Hsum 0 ltac:(simpl; lia)) as Hsum0.
      pose proof (Hsum 1 ltac:(simpl; lia)) as Hsum1.
      change (p + q = k) in Hsum0.
      change (q + r = k) in Hsum1.
      lia. }
    subst r.
    simpl in Hz.
    destruct Hz as [Hz | [Hz | [Hz | []]]]; subst; auto.
  - pose proof (Zlength_nonneg tl) as Htl.
    assert (Hr : r = p).
    { pose proof (Hsum 0 ltac:(rewrite !Zlength_cons; lia)) as Hsum0.
      pose proof (Hsum 1 ltac:(rewrite !Zlength_cons; lia)) as Hsum1.
      change (p + q = k) in Hsum0.
      change (q + r = k) in Hsum1. lia. }
    assert (Hs : s = q).
    { pose proof (Hsum 1 ltac:(rewrite !Zlength_cons; lia)) as Hsum1.
      pose proof (Hsum 2 ltac:(rewrite !Zlength_cons; lia)) as Hsum2.
      change (q + r = k) in Hsum1.
      change (r + s = k) in Hsum2. lia. }
    subst r; subst s.
    apply (IH tl p q k).
    + intros j Hj.
      assert (Hshift :
        0 <= j + 2 < Zlength (p :: q :: p :: q :: tl) - 1).
      { repeat rewrite Zlength_cons in Hj.
        repeat rewrite Zlength_cons. lia. }
      pose proof (Hsum (j + 2) Hshift) as Hsum_shift.
      replace (j + 2 + 1) with ((j + 1) + 2) in Hsum_shift by lia.
      rewrite (Znth_drop_two__rejected_results j p q (p :: q :: tl))
        in Hsum_shift by lia.
      rewrite (Znth_drop_two__rejected_results (j + 1) p q (p :: q :: tl))
        in Hsum_shift by lia.
      exact Hsum_shift.
    + simpl in Hz |- *.
      destruct Hz as [Hz | [Hz | [Hz | [Hz | Hz]]]]; auto.
Qed.
Lemma good_adjacent_sums_at_most_two_values__rejected_results :
  forall (b : list Z) (z : Z),
    2 <= Zlength b ->
    GoodAdjacentSums b ->
    In z b ->
    z = Znth 0 b 0 \/ z = Znth 1 b 0.
Proof.
  intros b z Hlen Hgood Hz.
  destruct b as [| p [| q tl]].
  - unfold Zlength in Hlen. simpl in Hlen. lia.
  - unfold Zlength in Hlen. simpl in Hlen. lia.
  - destruct Hgood as [k Hsum].
    change (z = p \/ z = q).
    eapply adjacent_sums_tail_values__rejected_results; eauto.
Qed.
Lemma occurrences_cons_distinct_pair__rejected_results :
  forall (l : list Z) (p q : Z),
    p <> q ->
    Occurrences p (p :: q :: l) - Occurrences q (p :: q :: l) =
    Occurrences p l - Occurrences q l.
Proof.
  intros l p q Hpq.
  unfold Occurrences.
  simpl.
  destruct (Z.eq_dec p p), (Z.eq_dec q p),
           (Z.eq_dec p q), (Z.eq_dec q q); try contradiction;
    repeat rewrite Nat2Z.inj_succ; lia.
Qed.
Lemma adjacent_sums_count_balance_core__rejected_results :
  forall (tl : list Z) (p q k : Z),
    p <> q ->
    (forall j : Z,
        0 <= j < Zlength (p :: q :: tl) - 1 ->
        Znth j (p :: q :: tl) 0 +
        Znth (j + 1) (p :: q :: tl) 0 = k) ->
    Z.abs
      (Z.of_nat (count_occ Z.eq_dec (p :: q :: tl) p) -
       Z.of_nat (count_occ Z.eq_dec (p :: q :: tl) q)) <= 1.
Proof.
  fix IH 1.
  intros [| r [| s tl]] p q k Hpq Hsum.
  - simpl.
    destruct (Z.eq_dec p p), (Z.eq_dec q p),
             (Z.eq_dec p q), (Z.eq_dec q q); try contradiction; simpl; lia.
  - assert (Hr : r = p).
    { pose proof (Hsum 0 ltac:(simpl; lia)) as Hsum0.
      pose proof (Hsum 1 ltac:(simpl; lia)) as Hsum1.
      change (p + q = k) in Hsum0.
      change (q + r = k) in Hsum1. lia. }
    subst r.
    simpl.
    destruct (Z.eq_dec p p), (Z.eq_dec q p),
             (Z.eq_dec p q), (Z.eq_dec q q); try contradiction; simpl; lia.
  - pose proof (Zlength_nonneg tl) as Htl.
    assert (Hr : r = p).
    { pose proof (Hsum 0 ltac:(rewrite !Zlength_cons; lia)) as Hsum0.
      pose proof (Hsum 1 ltac:(rewrite !Zlength_cons; lia)) as Hsum1.
      change (p + q = k) in Hsum0.
      change (q + r = k) in Hsum1. lia. }
    assert (Hs : s = q).
    { pose proof (Hsum 1 ltac:(rewrite !Zlength_cons; lia)) as Hsum1.
      pose proof (Hsum 2 ltac:(rewrite !Zlength_cons; lia)) as Hsum2.
      change (q + r = k) in Hsum1.
      change (r + s = k) in Hsum2. lia. }
    subst r; subst s.
    specialize (IH tl p q k Hpq).
    assert (Htail :
      forall j : Z,
        0 <= j < Zlength (p :: q :: tl) - 1 ->
        Znth j (p :: q :: tl) 0 + Znth (j + 1) (p :: q :: tl) 0 = k).
    { intros j Hj.
      assert (Hshift :
        0 <= j + 2 < Zlength (p :: q :: p :: q :: tl) - 1).
      { repeat rewrite Zlength_cons in Hj.
        repeat rewrite Zlength_cons. lia. }
      pose proof (Hsum (j + 2) Hshift) as Hsum_shift.
      replace (j + 2 + 1) with ((j + 1) + 2) in Hsum_shift by lia.
      rewrite (Znth_drop_two__rejected_results j p q (p :: q :: tl))
        in Hsum_shift by lia.
      rewrite (Znth_drop_two__rejected_results (j + 1) p q (p :: q :: tl))
        in Hsum_shift by lia.
      exact Hsum_shift. }
    specialize (IH Htail).
    change (Z.abs
      (Occurrences p (p :: q :: p :: q :: tl) -
       Occurrences q (p :: q :: p :: q :: tl)) <= 1).
    rewrite occurrences_cons_distinct_pair__rejected_results by exact Hpq.
    exact IH.
Qed.
Lemma good_adjacent_sums_count_balance__rejected_results :
  forall (a b : list Z) (x y : Z),
    2 <= Zlength a ->
    x <> y ->
    In x a -> In y a ->
    Permutation a b ->
    GoodAdjacentSums b ->
    Z.abs (Occurrences x a - Occurrences y a) <= 1.
Proof.
  intros a b x y Hlen Hxy Hinx Hiny Hperm Hgood.
  assert (Hinxb : In x b) by (eapply Permutation_in; eauto).
  assert (Hinyb : In y b) by (eapply Permutation_in; eauto).
  destruct b as [| p [| q tl]].
  - simpl in Hinxb. contradiction.
  - simpl in Hinxb, Hinyb.
    destruct Hinxb as [Hinxb | []].
    destruct Hinyb as [Hinyb | []].
    subst x; subst y. contradiction.
  -
  destruct Hgood as [k Hsum].
  assert (Hxpq : x = p \/ x = q).
  { eapply adjacent_sums_tail_values__rejected_results.
    - exact Hsum.
    - eapply Permutation_in; eauto. }
  assert (Hypq : y = p \/ y = q).
  { eapply adjacent_sums_tail_values__rejected_results.
    - exact Hsum.
    - eapply Permutation_in; eauto. }
  assert (Hpq : p <> q).
  { intro Heq. subst q.
    destruct Hxpq as [Hx | Hx]; destruct Hypq as [Hy | Hy];
      subst x; subst y; contradiction. }
  assert (Hbal := adjacent_sums_count_balance_core__rejected_results
                    tl p q k Hpq Hsum).
  unfold Occurrences.
  assert (Hcounts : forall v,
    count_occ Z.eq_dec a v = count_occ Z.eq_dec (p :: q :: tl) v).
  { apply (Permutation_count_occ Z.eq_dec). exact Hperm. }
  rewrite (Hcounts x), (Hcounts y).
  destruct Hxpq as [Hx | Hx]; destruct Hypq as [Hy | Hy];
    subst x; subst y; try contradiction;
    rewrite Z.abs_le in Hbal |- *; lia.
Qed.
Lemma Znth_in_range__rejected_results :
  forall (l : list Z) (j d : Z),
    0 <= j < Zlength l ->
    In (Znth j l d) l.
Proof.
  intros l j d Hj.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hj.
  lia.
Qed.
Lemma In_sublist_from_zero__rejected_results :
  forall (l : list Z) (hi z : Z),
    In z (sublist 0 hi l) ->
    In z l.
Proof.
  intros l hi z Hz.
  unfold sublist in Hz.
  simpl in Hz.
  rewrite <- (firstn_skipn (Z.to_nat hi) l).
  apply in_or_app. left. exact Hz.
Qed.
Lemma good_adjacent_sums_no_three_distinct__rejected_results :
  forall (a b : list Z) (x y z : Z),
    x <> y -> x <> z -> y <> z ->
    In x a -> In y a -> In z a ->
    Permutation a b ->
    GoodAdjacentSums b ->
    False.
Proof.
  intros a b x y z Hxy Hxz Hyz Hinx Hiny Hinz Hperm Hgood.
  assert (Hinxb : In x b) by (eapply Permutation_in; eauto).
  assert (Hinyb : In y b) by (eapply Permutation_in; eauto).
  assert (Hinzb : In z b) by (eapply Permutation_in; eauto).
  destruct b as [| p [| q tl]].
  - simpl in Hinxb. contradiction.
  - simpl in Hinxb, Hinyb.
    destruct Hinxb as [Hinxb | []].
    destruct Hinyb as [Hinyb | []].
    subst x; subst y. contradiction.
  - destruct Hgood as [k Hsum].
    pose proof (adjacent_sums_tail_values__rejected_results
      tl p q k Hsum x Hinxb) as Hxpq.
    pose proof (adjacent_sums_tail_values__rejected_results
      tl p q k Hsum y Hinyb) as Hypq.
    pose proof (adjacent_sums_tail_values__rejected_results
      tl p q k Hsum z Hinzb) as Hzpq.
    destruct Hxpq as [Hx | Hx]; destruct Hypq as [Hy | Hy];
      destruct Hzpq as [Hz | Hz]; subst; contradiction.
Qed.
Lemma paint_scan_state_full_count_balance__rejected_results :
  forall (input b : list Z) (n i x y cx cy : Z),
    2 <= n ->
    n = Zlength input ->
    i >= n -> i <= n ->
    cy <> 0 ->
    PaintScanState input i x y cx cy ->
    Permutation input b ->
    GoodAdjacentSums b ->
    Z.abs (cx - cy) <= 1.
Proof.
  intros input b n i x y cx cy Hn Hnlen Hin Hile Hcy0
    Hstate Hperm Hgood.
  assert (Hi : i = n) by lia.
  subst i.
  destruct Hstate as
    [Hbounds [Hx [Hcx [Hcy [Htotal [Hsentinel [Hyx
      [Hcxocc [Hcyocc Hcover]]]]]]]]].
  assert (Hyneq : y <> -1).
  { intro Hy. apply Hcy0.
    apply (proj1 Hsentinel). exact Hy. }
  specialize (Hcyocc Hyneq).
  assert (Hsub : sublist 0 n input = input).
  { apply sublist_self. exact Hnlen. }
  rewrite Hsub in Hcxocc, Hcyocc.
  assert (Hxy : x <> y).
  { intro Hxy. apply (Hyx Hyneq). symmetry. exact Hxy. }
  assert (Hinx : In x input).
  { rewrite Hx.
    apply Znth_in_range__rejected_results.
    rewrite <- Hnlen. lia. }
  assert (Hiny : In y input).
  { apply (count_occ_In Z.eq_dec).
    unfold Occurrences in Hcyocc.
    lia. }
  pose proof (good_adjacent_sums_count_balance__rejected_results
    input b x y ltac:(rewrite <- Hnlen; lia) Hxy Hinx Hiny Hperm Hgood) as Hbal.
  rewrite Hcxocc, Hcyocc.
  exact Hbal.
Qed.
