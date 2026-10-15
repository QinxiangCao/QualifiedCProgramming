Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition OneXorMerge (a b : list Z) : Prop :=
  exists i, 0 <= i < Zlength a - 1 /\
    b = sublist 0 i a ++
      (Z.lxor (Znth i a 0) (Znth (i + 1) a 0)) ::
      sublist (i + 2) (Zlength a) a.

Definition DestroyTrace (a : list Z) (m : Z) : Prop :=
  exists states, Zlength states = m + 1 /\ Znth 0 states nil = a /\
    (forall i, 0 <= i < m ->
      OneXorMerge (Znth i states nil) (Znth (i + 1) states nil)) /\
    exists i, 0 <= i < Zlength (Znth m states nil) - 1 /\
      Znth i (Znth m states nil) 0 > Znth (i + 1) (Znth m states nil) 0.

Definition Pre (a : list Z) : Prop :=
  2 <= Zlength a <= 100000 /\
  Forall (fun x => 1 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = -1 /\ forall m, ~ DestroyTrace a m) \/
  min_value_of_subset Z.le (DestroyTrace a) (fun moves => moves) out.

Definition NoEqualBitTriplePrefix (a : list Z) (next_center : Z) : Prop :=
  forall i, 1 <= i < next_center ->
    ~ (Z.log2 (Znth (i - 1) a 0) = Z.log2 (Znth i a 0) /\
       Z.log2 (Znth i a 0) = Z.log2 (Znth (i + 1) a 0)).

Definition BitScanState (original current shifts : Z) : Prop :=
  current = Z.shiftr original shifts.

Definition PrefixXor (a : list Z) (hi : Z) : Z :=
  fold_left Z.lxor (sublist 0 hi a) 0.

Definition PrefixXorTable
    (a table : list Z) (done : Z) : Prop :=
  forall k, 0 <= k <= done -> Znth k table 0 = PrefixXor a k.

Definition DestructiveWindow
    (a : list Z) (l mid r : Z) : Prop :=
  0 <= l <= mid /\ mid < r < Zlength a /\
  Z.lxor (PrefixXor a (mid + 1)) (PrefixXor a l) >
  Z.lxor (PrefixXor a (r + 1)) (PrefixXor a (mid + 1)).

Definition WindowBefore
    (next_l next_mid next_r l mid r : Z) : Prop :=
  l < next_l \/
  (l = next_l /\
    (mid < next_mid \/ (mid = next_mid /\ r < next_r))).

Definition WindowMoveCandidate
    (a : list Z) (next_l next_mid next_r moves : Z) : Prop :=
  exists l mid r,
    DestructiveWindow a l mid r /\
    WindowBefore next_l next_mid next_r l mid r /\
    moves = r - l - 1.

Definition BruteSearchState
    (a : list Z) (next_l next_mid next_r best : Z) : Prop :=
  (best = 2147483647 /\
    forall moves, ~ WindowMoveCandidate a next_l next_mid next_r moves) \/
  min_value_of_subset Z.le
    (WindowMoveCandidate a next_l next_mid next_r)
    (fun moves => moves) best.

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Wf_nat.
Lemma bitscan_zero__scan_setup :
  forall v, BitScanState v v 0.
Proof.
  intros v.
  unfold BitScanState.
  reflexivity.
Qed.
Lemma no_equal_prefix_one__scan_setup :
  forall values, NoEqualBitTriplePrefix values 1.
Proof.
  intros values.
  unfold NoEqualBitTriplePrefix.
  intros i Hi.
  lia.
Qed.
Lemma bitscan_shift_step__bit_shift_loops :
  forall original current shifts,
    0 <= shifts ->
    BitScanState original current shifts ->
    BitScanState original (Z.shiftr current 1) (shifts + 1).
Proof.
  intros original current shifts Hshifts Hstate.
  unfold BitScanState in *.
  subst current.
  rewrite Z.shiftr_shiftr by lia.
  f_equal.
Qed.
Lemma bitscan_positive_step_bounds__bit_shift_loops :
  forall original current shifts,
    original <= 1000000000 ->
    BitScanState original current shifts ->
    current > 1 ->
    current <= original ->
    0 <= shifts <= 30 ->
    1 <= Z.shiftr current 1 /\
    Z.shiftr current 1 <= original /\
    shifts + 1 <= 30.
Proof.
  intros original current shifts Horiginal Hstate Hcurrent Hle Hshifts.
  assert (Hshiftlt : shifts < 30).
  {
    destruct (Z.eq_dec shifts 30) as [Heq | Hneq].
    - subst shifts.
      unfold BitScanState in Hstate.
      rewrite Z.shiftr_div_pow2 in Hstate by lia.
      cbn in Hstate.
      rewrite Z.div_small in Hstate by lia.
      lia.
    - lia.
  }
  rewrite Z.shiftr_div_pow2 by lia.
  cbn.
  split.
  - apply Z.div_le_lower_bound; lia.
  - split.
    + assert (Hdiv : current / 2 <= current).
      { apply Z.div_le_upper_bound; lia. }
      lia.
    + lia.
Qed.
Lemma bitscan_terminal_log2__equal_bit_boundary :
  forall original shifts,
    0 < original ->
    0 <= shifts ->
    BitScanState original 1 shifts ->
    shifts = Z.log2 original.
Proof.
  intros original shifts Hpositive Hshifts Hscan.
  unfold BitScanState in Hscan.
  rewrite Z.shiftr_div_pow2 in Hscan by exact Hshifts.
  assert (Hpow : 0 < 2 ^ shifts) by
    (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod original (2 ^ shifts) ltac:(lia)) as Hdecomp.
  pose proof (Z.mod_pos_bound original (2 ^ shifts) Hpow) as Hmod.
  apply eq_sym, Z.log2_unique; [exact Hshifts |].
  rewrite Z.pow_succ_r by exact Hshifts.
  rewrite <- Hscan in Hdecomp.
  lia.
Qed.
Lemma no_equal_prefix_step__equal_bit_boundary :
  forall a i,
    NoEqualBitTriplePrefix a i ->
    ~ (Z.log2 (Znth (i - 1) a 0) = Z.log2 (Znth i a 0) /\
       Z.log2 (Znth i a 0) = Z.log2 (Znth (i + 1) a 0)) ->
    NoEqualBitTriplePrefix a (i + 1).
Proof.
  intros a i Hold Hnew.
  unfold NoEqualBitTriplePrefix in *.
  intros j Hj Hequal.
  destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
  - exact (Hold j ltac:(lia) Hequal).
  - assert (j = i) by lia.
    subst j.
    exact (Hnew Hequal).
Qed.
Lemma shiftr_log2_eq_one__equal_bit_boundary :
  forall a,
    0 < a ->
    Z.shiftr a (Z.log2 a) = 1.
Proof.
  intros a Hpositive.
  pose proof (Z.log2_nonneg a) as Hlog.
  pose proof (Z.log2_spec a Hpositive) as Hspec.
  rewrite Z.shiftr_div_pow2 by exact Hlog.
  apply eq_sym.
  apply (Z.div_unique a (2 ^ Z.log2 a) 1
           (a - 2 ^ Z.log2 a)).
  - left.
    rewrite Z.pow_succ_r in Hspec by exact Hlog.
    lia.
  - ring.
Qed.
Lemma equal_log_lxor_lt_lower__equal_bit_boundary :
  forall lower left right,
    0 < lower ->
    0 < left ->
    0 < right ->
    Z.log2 lower = Z.log2 left ->
    Z.log2 left = Z.log2 right ->
    Z.lxor left right < lower.
Proof.
  intros lower left right Hlower Hleft Hright Hlowerlog Hlogs.
  pose proof (Z.log2_nonneg left) as Hlog.
  pose proof (Z.log2_spec lower Hlower) as Hlower_spec.
  assert (Hshift_left : Z.shiftr left (Z.log2 left) = 1) by
    (apply shiftr_log2_eq_one__equal_bit_boundary; exact Hleft).
  assert (Hshift_right : Z.shiftr right (Z.log2 left) = 1).
  { rewrite Hlogs.
    apply shiftr_log2_eq_one__equal_bit_boundary.
    exact Hright. }
  assert (Hshift_xor : Z.shiftr (Z.lxor left right) (Z.log2 left) = 0).
  { rewrite Z.shiftr_lxor, Hshift_left, Hshift_right.
    reflexivity. }
  rewrite Z.shiftr_div_pow2 in Hshift_xor by exact Hlog.
  assert (Hpow : 0 < 2 ^ Z.log2 left) by
    (apply Z.pow_pos_nonneg; lia).
  pose proof
    (Z.div_mod (Z.lxor left right) (2 ^ Z.log2 left) ltac:(lia))
    as Hdecomp.
  pose proof
    (Z.mod_pos_bound (Z.lxor left right) (2 ^ Z.log2 left) Hpow)
    as Hmod.
  rewrite Hlowerlog in Hlower_spec.
  rewrite Hshift_xor in Hdecomp.
  lia.
Qed.
Lemma equal_adjacent_bits_spec_one__equal_bit_boundary :
  forall a n i vx vy vz,
    n = Zlength a ->
    1 <= i ->
    i + 1 < n ->
    vx = Znth (i - 1) a 0 ->
    vy = Znth i a 0 ->
    vz = Znth (i + 1) a 0 ->
    0 < vx ->
    0 < vy ->
    0 < vz ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k a 0 <= Znth (k + 1) a 0) ->
    Z.log2 vx = Z.log2 vy ->
    Z.log2 vy = Z.log2 vz ->
    Spec a 1.
Proof.
  intros a n i vx vy vz Hn Hi Hi_upper Hvx Hvy Hvz
    Hvx_pos Hvy_pos Hvz_pos Hsorted Hxy Hyz.
  set (merged :=
    sublist 0 i a ++
      Z.lxor (Znth i a 0) (Znth (i + 1) a 0) ::
      sublist (i + 2) (Zlength a) a).
  assert (Hmerge : OneXorMerge a merged).
  { unfold OneXorMerge.
    exists i.
    split; [lia | reflexivity]. }
  assert (Hmerged_len : Zlength merged = n - 1).
  { unfold merged.
    rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia.
    simpl.
    lia. }
  assert (Hmerged_prev : Znth (i - 1) merged 0 = vx).
  { unfold merged.
    rewrite app_Znth1.
    - rewrite Znth_sublist by lia.
      replace (i - 1 + 0) with (i - 1) by lia.
      symmetry; exact Hvx.
    - rewrite Zlength_sublist by lia.
      lia. }
  assert (Hmerged_xor : Znth i merged 0 = Z.lxor vy vz).
  { unfold merged.
    rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
    rewrite Zlength_sublist by lia.
    replace (i - (i - 0)) with 0 by lia.
    rewrite Znth0_cons, Hvy, Hvz.
    reflexivity. }
  assert (Hxor_lt : Z.lxor vy vz < vx).
  { eapply equal_log_lxor_lt_lower__equal_bit_boundary; eauto. }
  right.
  unfold min_value_of_subset, min_object_of_subset.
  exists 1.
  split.
  - split.
    + unfold DestroyTrace.
      exists (a :: merged :: nil).
      split.
      * repeat rewrite Zlength_cons.
        simpl.
        lia.
      * split.
        { apply Znth0_cons. }
        split.
        { intros j Hj.
          assert (j = 0) by lia.
          subst j.
          change (OneXorMerge a merged).
          exact Hmerge. }
        exists (i - 1).
        repeat rewrite Znth_cons by lia.
        repeat rewrite Znth0_cons.
        replace (i - 1 + 1) with i by lia.
        change (0 <= i - 1 < Zlength merged - 1 /\
          Znth (i - 1) merged 0 > Znth i merged 0).
        rewrite Hmerged_prev, Hmerged_xor, Hmerged_len.
        lia.
    + intros m Htrace.
      unfold DestroyTrace in Htrace.
      destruct Htrace as
        [states [Hstates_len [Hstate0 [Hsteps [j [Hj_bounds Hj_desc]]]]]].
      assert (Hm_nonneg : 0 <= m).
      { pose proof (Zlength_nonneg states) as Hstates_nonneg.
        destruct (Z_lt_ge_dec m 0) as [Hmneg | Hmge]; [| lia].
        assert (m = -1) by lia.
        subst m.
        destruct states as [| state states_tail].
        - simpl in Hstate0.
          subst a.
          unfold Zlength in Hn.
          simpl in Hn.
          lia.
        - rewrite Zlength_cons in Hstates_len.
          pose proof (Zlength_nonneg states_tail).
          lia. }
      destruct (Z.eq_dec m 0) as [Hmzero | Hmzero].
      * subst m.
        rewrite Hstate0 in Hj_bounds, Hj_desc.
        specialize (Hsorted j ltac:(lia)).
        lia.
      * lia.
  - reflexivity.
Qed.
Lemma prefix_xor_table_zero__prefix_table : forall a,
  PrefixXorTable a (repeat 0 64%nat) 0.
Proof.
  intros a.
  unfold PrefixXorTable.
  intros k Hk.
  assert (k = 0) by lia.
  subst k.
  rewrite Znth_repeat.
  unfold PrefixXor, sublist.
  reflexivity.
Qed.
Lemma prefix_xor_table_replace_step__prefix_table : forall a table i,
  PrefixXorTable a table i ->
  0 <= i < Zlength a ->
  i + 1 < Zlength table ->
  PrefixXorTable a
    (replace_Znth (i + 1)
      (Z.lxor (Znth i table 0) (Znth i a 0)) table)
    (i + 1).
Proof.
  intros a table i Htable Hi Hroom.
  unfold PrefixXorTable in *.
  intros k Hk.
  destruct (Z.eq_dec k (i + 1)) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia.
    unfold PrefixXor in *.
    rewrite (sublist_split 0 (i + 1) i a) by lia.
    rewrite (@sublist_single Z 0 i a) by lia.
    rewrite fold_left_app.
    simpl.
    rewrite Htable by lia.
    reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Htable.
    lia.
Qed.
Lemma brute_search_state_origin__prefix_table : forall a,
  BruteSearchState a 0 0 1 2147483647.
Proof.
  intros a.
  unfold BruteSearchState.
  left.
  split; [reflexivity |].
  intros moves Hcandidate.
  unfold WindowMoveCandidate in Hcandidate.
  destruct Hcandidate as (l & mid & r & Hdestructive & Hbefore & Hmoves).
  unfold DestructiveWindow in Hdestructive.
  unfold WindowBefore in Hbefore.
  lia.
Qed.
Lemma brute_search_state_next_l__brute_search_cursor :
  forall a n l mid best,
    n = Zlength a ->
    mid + 1 >= n ->
    mid <= n - 1 ->
    BruteSearchState a l mid (mid + 1) best ->
    BruteSearchState a (l + 1) (l + 1) ((l + 1) + 1) best.
Proof.
  intros a n l mid best Hlen Hlo Hhi Hstate.
  assert (HCand : forall moves,
    WindowMoveCandidate a l mid (mid + 1) moves <->
    WindowMoveCandidate a (l + 1) (l + 1) ((l + 1) + 1) moves).
  {
    intro moves.
    unfold WindowMoveCandidate.
    split.
    - intros (wl & wm & wr & Hdes & Hbefore & Hmoves).
      exists wl, wm, wr.
      split; [exact Hdes |].
      split; [| exact Hmoves].
      unfold DestructiveWindow in Hdes.
      unfold WindowBefore in *.
      lia.
    - intros (wl & wm & wr & Hdes & Hbefore & Hmoves).
      exists wl, wm, wr.
      split; [exact Hdes |].
      split; [| exact Hmoves].
      unfold DestructiveWindow in Hdes.
      unfold WindowBefore in *.
      lia.
  }
  unfold BruteSearchState in *.
  destruct Hstate as [[Hbest Hnone] | Hmin].
  - left.
    split; [exact Hbest |].
    intros moves Hnew.
    apply (Hnone moves).
    apply (proj2 (HCand moves)).
    exact Hnew.
  - right.
    unfold min_value_of_subset, min_object_of_subset in *.
    destruct Hmin as (moves & (Hmember & Hleast) & Hbest).
    exists moves.
    split; [split | exact Hbest].
    + apply (proj1 (HCand moves)).
      exact Hmember.
    + intros other Hother.
      apply Hleast.
      apply (proj2 (HCand other)).
      exact Hother.
Qed.
Lemma brute_search_state_next_mid__brute_search_cursor :
  forall a n l mid r best,
    n = Zlength a ->
    r >= n ->
    r <= n ->
    BruteSearchState a l mid r best ->
    BruteSearchState a l (mid + 1) ((mid + 1) + 1) best.
Proof.
  intros a n l mid r best Hlen Hlo Hhi Hstate.
  assert (HCand : forall moves,
    WindowMoveCandidate a l mid r moves <->
    WindowMoveCandidate a l (mid + 1) ((mid + 1) + 1) moves).
  {
    intro moves.
    unfold WindowMoveCandidate.
    split.
    - intros (wl & wm & wr & Hdes & Hbefore & Hmoves).
      exists wl, wm, wr.
      split; [exact Hdes |].
      split; [| exact Hmoves].
      unfold DestructiveWindow in Hdes.
      unfold WindowBefore in *.
      lia.
    - intros (wl & wm & wr & Hdes & Hbefore & Hmoves).
      exists wl, wm, wr.
      split; [exact Hdes |].
      split; [| exact Hmoves].
      unfold DestructiveWindow in Hdes.
      unfold WindowBefore in *.
      lia.
  }
  unfold BruteSearchState in *.
  destruct Hstate as [[Hbest Hnone] | Hmin].
  - left.
    split; [exact Hbest |].
    intros moves Hnew.
    apply (Hnone moves).
    apply (proj2 (HCand moves)).
    exact Hnew.
  - right.
    unfold min_value_of_subset, min_object_of_subset in *.
    destruct Hmin as (moves & (Hmember & Hleast) & Hbest).
    exists moves.
    split; [split | exact Hbest].
    + apply (proj1 (HCand moves)).
      exact Hmember.
    + intros other Hother.
      apply Hleast.
      apply (proj2 (HCand other)).
      exact Hother.
Qed.
Lemma prefix_table_destructive_window__brute_search_window :
  forall a table done l mid r,
    PrefixXorTable a table done ->
    0 <= l <= mid ->
    mid < r < Zlength a ->
    r + 1 <= done ->
    Z.lxor (Znth (mid + 1) table 0) (Znth l table 0) >
      Z.lxor (Znth (r + 1) table 0) (Znth (mid + 1) table 0) ->
    DestructiveWindow a l mid r.
Proof.
  intros a table done l mid r Htable Hlm Hmr Hr Hxor.
  unfold DestructiveWindow.
  split; [exact Hlm |].
  split; [exact Hmr |].
  specialize (Htable l ltac:(lia)) as Hl.
  specialize (Htable (mid + 1) ltac:(lia)) as Hmid.
  specialize (Htable (r + 1) ltac:(lia)) as Hright.
  rewrite <- Hl, <- Hmid, <- Hright.
  exact Hxor.
Qed.
Lemma brute_search_state_consume__brute_search_window :
  forall a l mid r best,
    BruteSearchState a l mid r best ->
    (~ DestructiveWindow a l mid r ->
      BruteSearchState a l mid (r + 1) best) /\
    (DestructiveWindow a l mid r -> r - l - 1 < best ->
      BruteSearchState a l mid (r + 1) (r - l - 1)) /\
    (DestructiveWindow a l mid r -> best <= r - l - 1 ->
      best <> 2147483647 ->
      BruteSearchState a l mid (r + 1) best).
Proof.
  intros a l mid r best Hstate.
  assert (Hcandidate : forall moves,
    WindowMoveCandidate a l mid (r + 1) moves <->
    WindowMoveCandidate a l mid r moves \/
      (DestructiveWindow a l mid r /\ moves = r - l - 1)).
  {
    intros moves.
    unfold WindowMoveCandidate, WindowBefore.
    split.
    - intros [l0 [mid0 [r0 [Hwindow [Hbefore Hmoves]]]]].
      destruct Hbefore as [Hleft | [Hl0 [Hmiddle | [Hmid0 Hr0]]]].
      + left. exists l0, mid0, r0. split; [exact Hwindow |].
        split; [left; exact Hleft | exact Hmoves].
      + left. exists l0, mid0, r0. split; [exact Hwindow |].
        split; [right; split; [exact Hl0 | left; exact Hmiddle] | exact Hmoves].
      + destruct (Z_lt_ge_dec r0 r) as [Hlt | Hge].
        * left. exists l0, mid0, r0. split; [exact Hwindow |].
          split; [right; split; [exact Hl0 | right; auto] | exact Hmoves].
        * right. subst l0 mid0. assert (r0 = r) by lia. subst r0.
          split; auto.
    - intros [[l0 [mid0 [r0 [Hwindow [Hbefore Hmoves]]]]] |
              [Hwindow Hmoves]].
      + exists l0, mid0, r0. split; [exact Hwindow |].
        split; [| exact Hmoves].
        destruct Hbefore as [Hleft | [Hl0 [Hmiddle | [Hmid0 Hr0]]]].
        * left; exact Hleft.
        * right; split; [exact Hl0 | left; exact Hmiddle].
        * right; split; [exact Hl0 | right; split; [exact Hmid0 | lia]].
      + exists l, mid, r. split; [exact Hwindow |].
        split.
        * right; split; [reflexivity |].
          right; split; [reflexivity | lia].
        * exact Hmoves.
  }
  split.
  - intros Hnot.
    destruct Hstate as [[Hbest Hnone] | Hmin].
    + left. split; [exact Hbest |].
      intros moves Hnew.
      apply Hcandidate in Hnew.
      destruct Hnew as [Hold | [Hwindow _]].
      * exact (Hnone moves Hold).
      * exact (Hnot Hwindow).
    + right.
      unfold min_value_of_subset, min_object_of_subset in *.
      destruct Hmin as [moves [[Hold Hleast] Hvalue]].
      exists moves. split.
      * split.
        -- apply Hcandidate. left. exact Hold.
        -- intros other Hnew.
           apply Hcandidate in Hnew.
           destruct Hnew as [Hother | [Hwindow _]].
           ++ exact (Hleast other Hother).
           ++ contradiction.
      * exact Hvalue.
  - split.
    + intros Hwindow Himproves.
      right.
      unfold min_value_of_subset, min_object_of_subset in *.
      exists (r - l - 1). split.
      * split.
        -- apply Hcandidate. right. auto.
        -- intros other Hnew.
           apply Hcandidate in Hnew.
           destruct Hnew as [Hother | [_ Hother]].
           ++ destruct Hstate as [[_ Hnone] | [old [[Hold Hleast] Hvalue]]].
              ** exfalso. exact (Hnone other Hother).
              ** subst old. specialize (Hleast other Hother). lia.
           ++ lia.
      * reflexivity.
    + intros Hwindow Hnonimproves Hfinite.
      destruct Hstate as [[Hbest _] | Hmin].
      * contradiction.
      * right.
        unfold min_value_of_subset, min_object_of_subset in *.
        destruct Hmin as [moves [[Hold Hleast] Hvalue]].
        exists moves. split.
        -- split.
           ++ apply Hcandidate. left. exact Hold.
           ++ intros other Hnew.
              apply Hcandidate in Hnew.
              destruct Hnew as [Hother | [_ Hother]].
              ** exact (Hleast other Hother).
              ** subst other. rewrite Hvalue. exact Hnonimproves.
        -- exact Hvalue.
Qed.
Lemma xor_fold_acc__final_search_result :
  forall xs acc,
    fold_left Z.lxor xs acc =
    Z.lxor acc (fold_left Z.lxor xs 0).
Proof.
  induction xs as [| x xs IH]; intros acc.
  - simpl.
    rewrite Z.lxor_0_r; reflexivity.
  - simpl.
    rewrite (IH (Z.lxor acc x)).
    rewrite (IH x).
    rewrite Z.lxor_assoc.
    reflexivity.
Qed.
Lemma xor_value_app__final_search_result :
  forall xs ys,
    fold_left Z.lxor (xs ++ ys) 0 =
    Z.lxor (fold_left Z.lxor xs 0) (fold_left Z.lxor ys 0).
Proof.
  intros xs ys.
  rewrite fold_left_app.
  rewrite xor_fold_acc__final_search_result.
  reflexivity.
Qed.
Lemma xor_cancel_prefix__final_search_result :
  forall x y, Z.lxor (Z.lxor x y) x = y.
Proof.
  intros x y.
  rewrite (Z.lxor_comm x y).
  rewrite Z.lxor_assoc.
  rewrite Z.lxor_nilpotent.
  apply Z.lxor_0_r.
Qed.
Lemma sublist_map__final_search_result :
  forall (A B : Type) (f : A -> B) lo hi xs,
    sublist lo hi (map f xs) = map f (sublist lo hi xs).
Proof.
  intros A B f lo hi xs.
  unfold sublist.
  rewrite firstn_map, skipn_map.
  reflexivity.
Qed.
Lemma Zlength_map__final_search_result :
  forall (A B : Type) (f : A -> B) xs,
    Zlength (map f xs) = Zlength xs.
Proof.
  intros A B f xs.
  rewrite !Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.
Lemma Znth_map__final_search_result :
  forall (A B : Type) (f : A -> B) xs i da db,
    0 <= i < Zlength xs ->
    Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs i da db Hi.
  rewrite (Znth_indep (map f xs) i db (f da)).
  2:{ rewrite Zlength_map__final_search_result; exact Hi. }
  unfold Znth.
  apply map_nth.
Qed.
Lemma two_adjacent_decompose__final_search_result :
  forall (A : Type) (xs : list A) (d : A) i,
    0 <= i < Zlength xs - 1 ->
    xs = sublist 0 i xs ++ Znth i xs d ::
      Znth (i + 1) xs d :: sublist (i + 2) (Zlength xs) xs.
Proof.
  intros A xs d i Hi.
  rewrite <- (sublist_self xs) at 1 by reflexivity.
  rewrite (sublist_split 0 (Zlength xs) i xs) by lia.
  rewrite (sublist_split i (Zlength xs) (i + 1) xs) by lia.
  rewrite (sublist_split (i + 1) (Zlength xs) (i + 2) xs) by lia.
  rewrite (sublist_single d i xs) by lia.
  replace (i + 2) with ((i + 1) + 1) by lia.
  rewrite (sublist_single d (i + 1) xs) by lia.
  simpl.
  repeat rewrite app_assoc.
  reflexivity.
Qed.
Lemma xor_partition_initial__final_search_result :
  forall a,
    concat (map (fun x => x :: nil) a) = a /\
    Forall (fun block => block <> nil) (map (fun x => x :: nil) a) /\
    a = map (fun block => fold_left Z.lxor block 0)
      (map (fun x => x :: nil) a).
Proof.
  intros a.
  induction a as [| x xs IH].
  - simpl; repeat split; auto.
  - destruct IH as [Hcat [Hnon Hmap]].
    simpl in *.
    split.
    + f_equal; exact Hcat.
    + split.
      * constructor; [discriminate | exact Hnon].
      * f_equal.
        simpl.
        exact Hmap.
Qed.
Lemma xor_partition_merge__final_search_result :
  forall a blocks b c,
    concat blocks = a ->
    Forall (fun block => block <> nil) blocks ->
    b = map (fun block => fold_left Z.lxor block 0) blocks ->
    OneXorMerge b c ->
    exists blocks',
      concat blocks' = a /\
      Forall (fun block => block <> nil) blocks' /\
      c = map (fun block => fold_left Z.lxor block 0) blocks'.
Proof.
  intros a blocks b c Hcat Hnon Hmap Hmerge.
  destruct Hmerge as [i [Hi Hc]].
  assert (Hiblocks : 0 <= i < Zlength blocks - 1).
  { rewrite Hmap in Hi.
    rewrite Zlength_map__final_search_result in Hi.
    exact Hi. }
  pose proof (two_adjacent_decompose__final_search_result
    (list Z) blocks nil i Hiblocks) as Hblocks.
  exists (sublist 0 i blocks ++
    (Znth i blocks nil ++ Znth (i + 1) blocks nil) ::
    sublist (i + 2) (Zlength blocks) blocks).
  split.
  - rewrite concat_app; simpl.
    rewrite Hblocks in Hcat.
    rewrite concat_app in Hcat.
    simpl in Hcat.
    repeat rewrite app_assoc in *.
    exact Hcat.
  - split.
    + rewrite Hblocks in Hnon.
      rewrite Forall_app in Hnon.
      destruct Hnon as [Hleft Htail].
      inversion Htail as [| bi tail Hbi Htail']; subst.
      inversion Htail' as [| bj right Hbj Hright]; subst.
      rewrite Forall_app.
      split; [exact Hleft |].
      constructor.
      * intro Hnil.
        apply app_eq_nil in Hnil.
        destruct Hnil as [Hbi_nil Hbj_nil].
        contradiction.
      * exact Hright.
    + rewrite Hc, Hmap.
      rewrite Zlength_map__final_search_result.
      rewrite !sublist_map__final_search_result.
      rewrite (Znth_map__final_search_result (list Z) Z
        (fun block => fold_left Z.lxor block 0) blocks i nil 0) by lia.
      rewrite (Znth_map__final_search_result (list Z) Z
        (fun block => fold_left Z.lxor block 0) blocks (i + 1) nil 0) by lia.
      rewrite !map_app; simpl.
      rewrite xor_value_app__final_search_result.
      reflexivity.
Qed.
Lemma xor_merge_chain_partition__final_search_result :
  forall a states (n : nat),
    Z.of_nat n < Zlength states ->
    Znth 0 states nil = a ->
    (forall i, 0 <= i < Z.of_nat n ->
      OneXorMerge (Znth i states nil) (Znth (i + 1) states nil)) ->
    exists blocks,
      concat blocks = a /\
      Forall (fun block => block <> nil) blocks /\
      Znth (Z.of_nat n) states nil =
        map (fun block => fold_left Z.lxor block 0) blocks.
Proof.
  intros a states n.
  induction n as [| n IH]; intros Hbound Hstart Hsteps.
  - pose proof (xor_partition_initial__final_search_result a)
      as [Hcat [Hnon Hmap]].
    exists (map (fun x => x :: nil) a).
    split; [exact Hcat |].
    split; [exact Hnon |].
    simpl.
    rewrite Hstart.
    exact Hmap.
  - assert (Hprev_bound : Z.of_nat n < Zlength states) by lia.
    assert (Hprev_steps : forall i, 0 <= i < Z.of_nat n ->
      OneXorMerge (Znth i states nil) (Znth (i + 1) states nil)).
    { intros i Hi; apply Hsteps; lia. }
    destruct (IH Hprev_bound Hstart Hprev_steps)
      as [blocks [Hcat [Hnon Hmap]]].
    assert (Hlast : OneXorMerge
      (Znth (Z.of_nat n) states nil)
      (Znth (Z.of_nat n + 1) states nil)).
    { apply Hsteps; lia. }
    destruct (xor_partition_merge__final_search_result
      a blocks (Znth (Z.of_nat n) states nil)
      (Znth (Z.of_nat n + 1) states nil)
      Hcat Hnon Hmap Hlast)
      as [blocks' [Hcat' [Hnon' Hmap']]].
    exists blocks'.
    split; [exact Hcat' |].
    split; [exact Hnon' |].
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    exact Hmap'.
Qed.
Lemma concat_nonempty_length__final_search_result :
  forall blocks : list (list Z),
    Forall (fun block => block <> nil) blocks ->
    Zlength blocks <= Zlength (concat blocks).
Proof.
  intros blocks Hnon.
  induction Hnon as [| block blocks Hblock Hnon IH].
  - change (0 <= 0); lia.
  - change (Zlength (block :: blocks) <= Zlength (block ++ concat blocks)).
    rewrite Zlength_cons, Zlength_app.
    destruct block as [| x block]; [contradiction |].
    pose proof (Zlength_nonneg block).
    rewrite Zlength_cons.
    lia.
Qed.
Lemma prefix_xor_segment__final_search_result :
  forall left block right,
    Z.lxor
      (PrefixXor (left ++ block ++ right)
        (Zlength left + Zlength block))
      (PrefixXor (left ++ block ++ right) (Zlength left)) =
    fold_left Z.lxor block 0.
Proof.
  intros left block right.
  unfold PrefixXor.
  assert (Hbig : sublist 0 (Zlength left + Zlength block)
      (left ++ block ++ right) = left ++ block).
  { replace (left ++ block ++ right) with ((left ++ block) ++ right)
      by (rewrite <- app_assoc; reflexivity).
    replace (Zlength left + Zlength block)
      with (Zlength (left ++ block)) by (rewrite Zlength_app; lia).
    apply sublist_app_exact1. }
  assert (Hsmall : sublist 0 (Zlength left)
      (left ++ block ++ right) = left).
  { replace (left ++ block ++ right) with (left ++ (block ++ right))
      by (rewrite app_assoc; reflexivity).
    apply sublist_app_exact1. }
  rewrite Hbig, Hsmall.
  rewrite xor_value_app__final_search_result.
  apply xor_cancel_prefix__final_search_result.
Qed.
Lemma nonempty_Zlength__final_search_result :
  forall (xs : list Z), xs <> nil -> 1 <= Zlength xs.
Proof.
  intros xs Hnon.
  destruct xs as [| x xs]; [contradiction |].
  rewrite Zlength_cons.
  pose proof (Zlength_nonneg xs).
  lia.
Qed.
Lemma xor_partition_inversion_window__final_search_result :
  forall a blocks b i,
    concat blocks = a ->
    Forall (fun block => block <> nil) blocks ->
    b = map (fun block => fold_left Z.lxor block 0) blocks ->
    0 <= i < Zlength b - 1 ->
    Znth i b 0 > Znth (i + 1) b 0 ->
    exists l mid r,
      DestructiveWindow a l mid r /\
      r - l - 1 <= Zlength a - Zlength b.
Proof.
  intros a blocks b i Hcat Hnon Hmap Hi Hinv.
  assert (Hiblocks : 0 <= i < Zlength blocks - 1).
  { rewrite Hmap in Hi.
    rewrite Zlength_map__final_search_result in Hi.
    exact Hi. }
  pose proof (two_adjacent_decompose__final_search_result
    (list Z) blocks nil i Hiblocks) as Hblocks.
  rewrite Hblocks in Hnon.
  rewrite Forall_app in Hnon.
  destruct Hnon as [Hleft Htail].
  inversion Htail as [| bi tail Hbi Htail']; clear Htail.
  inversion Htail' as [| bj right Hbj Hright]; clear Htail'.
  pose proof (nonempty_Zlength__final_search_result
    (Znth i blocks nil) Hbi) as Hbi_len.
  pose proof (nonempty_Zlength__final_search_result
    (Znth (i + 1) blocks nil) Hbj) as Hbj_len.
  pose proof (concat_nonempty_length__final_search_result
    (sublist 0 i blocks) Hleft) as Hleft_len.
  pose proof (concat_nonempty_length__final_search_result
    (sublist (i + 2) (Zlength blocks) blocks) Hright) as Hright_len.
  rewrite Hmap in Hinv.
  rewrite (Znth_map__final_search_result (list Z) Z
    (fun block => fold_left Z.lxor block 0) blocks i nil 0)
    in Hinv by lia.
  rewrite (Znth_map__final_search_result (list Z) Z
    (fun block => fold_left Z.lxor block 0) blocks (i + 1) nil 0)
    in Hinv by lia.
  rewrite Hblocks in Hcat.
  rewrite concat_app in Hcat.
  simpl in Hcat.
  repeat rewrite app_assoc in Hcat.
  assert (Hblocks_len :
    Zlength blocks = Zlength (sublist 0 i blocks) + 2 +
      Zlength (sublist (i + 2) (Zlength blocks) blocks)).
  { rewrite !Zlength_sublist by lia.
    lia. }
  assert (Ha_len :
    Zlength a = Zlength (concat (sublist 0 i blocks)) +
      Zlength (Znth i blocks nil) +
      Zlength (Znth (i + 1) blocks nil) +
      Zlength (concat (sublist (i + 2) (Zlength blocks) blocks))).
  { rewrite <- Hcat.
    repeat rewrite Zlength_app.
    lia. }
  assert (Hb_len : Zlength b = Zlength blocks).
  { rewrite Hmap; apply Zlength_map__final_search_result. }
  exists (Zlength (concat (sublist 0 i blocks))).
  exists (Zlength (concat (sublist 0 i blocks)) +
    Zlength (Znth i blocks nil) - 1).
  exists (Zlength (concat (sublist 0 i blocks)) +
    Zlength (Znth i blocks nil) +
    Zlength (Znth (i + 1) blocks nil) - 1).
  split.
  - unfold DestructiveWindow.
    split.
    + split; [apply Zlength_nonneg | lia].
    + split.
      * split; [lia | rewrite Ha_len; pose proof
          (Zlength_nonneg (concat
            (sublist (i + 2) (Zlength blocks) blocks))); lia].
      * assert (Hxor1 :
          Z.lxor
            (PrefixXor a
              (Zlength (concat (sublist 0 i blocks)) +
                Zlength (Znth i blocks nil)))
            (PrefixXor a (Zlength (concat (sublist 0 i blocks)))) =
          fold_left Z.lxor (Znth i blocks nil) 0).
        { rewrite <- Hcat.
          replace
            (((concat (sublist 0 i blocks) ++ Znth i blocks nil) ++
              Znth (i + 1) blocks nil) ++
              concat (sublist (i + 2) (Zlength blocks) blocks))
            with
            (concat (sublist 0 i blocks) ++ Znth i blocks nil ++
              (Znth (i + 1) blocks nil ++
                concat (sublist (i + 2) (Zlength blocks) blocks)))
            by (repeat rewrite app_assoc; reflexivity).
          apply prefix_xor_segment__final_search_result. }
        assert (Hxor2 :
          Z.lxor
            (PrefixXor a
              (Zlength (concat (sublist 0 i blocks)) +
                Zlength (Znth i blocks nil) +
                Zlength (Znth (i + 1) blocks nil)))
            (PrefixXor a
              (Zlength (concat (sublist 0 i blocks)) +
                Zlength (Znth i blocks nil))) =
          fold_left Z.lxor (Znth (i + 1) blocks nil) 0).
        { rewrite <- Hcat.
          replace
            (((concat (sublist 0 i blocks) ++ Znth i blocks nil) ++
              Znth (i + 1) blocks nil) ++
              concat (sublist (i + 2) (Zlength blocks) blocks))
            with
            ((concat (sublist 0 i blocks) ++ Znth i blocks nil) ++
              Znth (i + 1) blocks nil ++
              concat (sublist (i + 2) (Zlength blocks) blocks))
            by (repeat rewrite app_assoc; reflexivity).
          replace
            (Zlength (concat (sublist 0 i blocks)) +
              Zlength (Znth i blocks nil))
            with
            (Zlength
              (concat (sublist 0 i blocks) ++ Znth i blocks nil))
            by (rewrite Zlength_app; reflexivity).
          apply prefix_xor_segment__final_search_result. }
        replace
          (Zlength (concat (sublist 0 i blocks)) +
             Zlength (Znth i blocks nil) - 1 + 1)
          with
          (Zlength (concat (sublist 0 i blocks)) +
             Zlength (Znth i blocks nil)) by lia.
        replace
          (Zlength (concat (sublist 0 i blocks)) +
             Zlength (Znth i blocks nil) +
             Zlength (Znth (i + 1) blocks nil) - 1 + 1)
          with
          (Zlength (concat (sublist 0 i blocks)) +
             Zlength (Znth i blocks nil) +
             Zlength (Znth (i + 1) blocks nil)) by lia.
        rewrite Hxor1, Hxor2.
        exact Hinv.
  - rewrite Ha_len, Hb_len.
    lia.
Qed.
Lemma one_xor_merge_length__final_search_result :
  forall a b, OneXorMerge a b -> Zlength b = Zlength a - 1.
Proof.
  intros a b [i [Hi Hb]].
  rewrite Hb.
  rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia.
  lia.
Qed.
Lemma xor_merge_chain_length__final_search_result :
  forall states (n : nat),
    Z.of_nat n < Zlength states ->
    (forall i, 0 <= i < Z.of_nat n ->
      OneXorMerge (Znth i states nil) (Znth (i + 1) states nil)) ->
    Zlength (Znth (Z.of_nat n) states nil) =
      Zlength (Znth 0 states nil) - Z.of_nat n.
Proof.
  intros states n.
  induction n as [| n IH]; intros Hbound Hsteps.
  - simpl; lia.
  - assert (Hprev_bound : Z.of_nat n < Zlength states) by lia.
    assert (Hprev_steps : forall i, 0 <= i < Z.of_nat n ->
      OneXorMerge (Znth i states nil) (Znth (i + 1) states nil)).
    { intros i Hi; apply Hsteps; lia. }
    pose proof (IH Hprev_bound Hprev_steps) as Hlen.
    pose proof (one_xor_merge_length__final_search_result
      (Znth (Z.of_nat n) states nil)
      (Znth (Z.of_nat n + 1) states nil)) as Hlast.
    specialize (Hlast (Hsteps (Z.of_nat n) ltac:(lia))).
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    lia.
Qed.
Lemma destroy_trace_to_window__final_search_result :
  forall a moves,
    1 <= Zlength a ->
    DestroyTrace a moves ->
    exists l mid r,
      DestructiveWindow a l mid r /\ r - l - 1 <= moves.
Proof.
  intros a moves Ha Htrace.
  destruct Htrace as [states [Hstates [Hstart [Hsteps Hbad]]]].
  destruct Hbad as [i [Hi Hinv]].
  assert (Hstates_nonempty : 1 <= Zlength states).
  { destruct states as [| s states].
    - unfold Znth in Hstart; simpl in Hstart.
      symmetry in Hstart; subst a.
      rewrite Zlength_correct in Ha; simpl in Ha; lia.
    - rewrite Zlength_cons.
      pose proof (Zlength_nonneg states); lia. }
  assert (Hmoves : 0 <= moves) by lia.
  assert (Hnat : Z.of_nat (Z.to_nat moves) = moves).
  { rewrite Z2Nat.id; lia. }
  assert (Hbound : Z.of_nat (Z.to_nat moves) < Zlength states) by lia.
  assert (Hsteps_nat : forall j, 0 <= j < Z.of_nat (Z.to_nat moves) ->
    OneXorMerge (Znth j states nil) (Znth (j + 1) states nil)).
  { intros j Hj; apply Hsteps; lia. }
  destruct (xor_merge_chain_partition__final_search_result
    a states (Z.to_nat moves) Hbound Hstart Hsteps_nat)
    as [blocks [Hcat [Hnon Hmap]]].
  pose proof (xor_merge_chain_length__final_search_result
    states (Z.to_nat moves) Hbound Hsteps_nat) as Hlen.
  rewrite Hnat in Hmap, Hlen.
  destruct (xor_partition_inversion_window__final_search_result
    a blocks (Znth moves states nil) i Hcat Hnon Hmap Hi Hinv)
    as [l [mid [r [Hwindow Hmove]]]].
  exists l, mid, r.
  split; [exact Hwindow |].
  rewrite Hstart in Hlen.
  lia.
Qed.
Lemma finished_window_candidate__final_search_result :
  forall a n l mid r,
    n = Zlength a ->
    DestructiveWindow a l mid r ->
    WindowMoveCandidate a n n (n + 1) (r - l - 1).
Proof.
  intros a n l mid r Hn Hwindow.
  exists l, mid, r.
  split; [exact Hwindow |].
  split; [| reflexivity].
  unfold WindowBefore, DestructiveWindow in *.
  destruct Hwindow as [[Hl Hlm] [[Hmr Hr] Hxor]].
  left; lia.
Qed.
Lemma finished_window_search_spec_none__final_search_result :
  forall a n,
    2 <= n <= 60 ->
    n = Zlength a ->
    BruteSearchState a n n (n + 1) 2147483647 ->
    Spec a (-1).
Proof.
  intros a n Hn Hlen Hstate.
  unfold Spec.
  left.
  split; [reflexivity |].
  intros moves Htrace.
  destruct (destroy_trace_to_window__final_search_result a moves
    ltac:(lia) Htrace) as [l [mid [r [Hwindow Hmove]]]].
  pose proof (finished_window_candidate__final_search_result
    a n l mid r Hlen Hwindow) as Hcandidate.
  unfold BruteSearchState in Hstate.
  destruct Hstate as [[_ Hnone] | Hminimum].
  - exact (Hnone (r - l - 1) Hcandidate).
  - unfold min_value_of_subset, min_object_of_subset in Hminimum.
    destruct Hminimum as [best [[Hbest _] Heq]].
    unfold WindowMoveCandidate in Hbest.
    destruct Hbest as [l' [mid' [r' [Hwindow' [_ Hbest]]]]].
    unfold DestructiveWindow in Hwindow'.
    destruct Hwindow' as [[Hl' Hlm'] [[Hmr' Hr'] Hxor']].
    simpl in Heq.
    subst best.
    lia.
Qed.
Lemma head_one_xor_merge__final_search_result :
  forall x y rest,
    OneXorMerge (x :: y :: rest) (Z.lxor x y :: rest).
Proof.
  intros x y rest.
  exists 0.
  split.
  - repeat rewrite Zlength_cons.
    pose proof (Zlength_nonneg rest); lia.
  - rewrite Zsublist_nil by lia.
    simpl.
    f_equal.
    replace (x :: y :: rest) with ((x :: y :: nil) ++ rest)
      by reflexivity.
    assert (Hprefixlen : Zlength (x :: y :: nil) = 2).
    { repeat rewrite Zlength_cons.
      rewrite Zlength_correct; simpl; lia. }
    assert (Hbounds : 2 <= 2 <= Zlength ((x :: y :: nil) ++ rest)).
    { rewrite Zlength_app, Hprefixlen.
      pose proof (Zlength_nonneg rest); lia. }
    erewrite sublist_split_app_r;
      [| exact Hprefixlen | exact Hbounds].
    replace (Zlength ((x :: y :: nil) ++ rest) - 2)
      with (Zlength rest) by (rewrite Zlength_app, Hprefixlen; lia).
    rewrite sublist_self by reflexivity.
    reflexivity.
Qed.
Lemma collapse_all_xor_path__final_search_result :
  forall xs,
    xs <> nil ->
    exists states,
      Zlength states = Zlength xs /\
      Znth 0 states nil = xs /\
      (forall i, 0 <= i < Zlength xs - 1 ->
        OneXorMerge (Znth i states nil) (Znth (i + 1) states nil)) /\
      Znth (Zlength xs - 1) states nil =
        (fold_left Z.lxor xs 0 :: nil).
Proof.
  intro xs.
  pattern xs.
  apply (well_founded_induction
    (well_founded_ltof (list Z) (@length Z))).
  intros current IH Hnon.
  destruct current as [| x xs_tail]; [contradiction |].
  destruct xs_tail as [| y rest].
  - exists ((x :: nil) :: nil).
    split; [reflexivity |].
    split; [reflexivity |].
    split.
    + intros i Hi.
      repeat rewrite Zlength_cons in Hi.
      rewrite Zlength_correct in Hi; simpl in Hi; lia.
    + reflexivity.
  - assert (Hmerged : Z.lxor x y :: rest <> nil) by discriminate.
    destruct (IH (Z.lxor x y :: rest) ltac:(unfold ltof; simpl; lia) Hmerged)
      as [states [Hstates [Hstart [Hsteps Hend]]]].
    exists ((x :: y :: rest) :: states).
    split.
    + rewrite Zlength_cons, Hstates.
      repeat rewrite Zlength_cons.
      lia.
    + split; [reflexivity |].
      split.
      * intros i Hi.
        destruct (Z.eq_dec i 0) as [-> | Hnz].
        -- change (OneXorMerge (x :: y :: rest) (Znth 0 states nil)).
           rewrite Hstart.
           apply head_one_xor_merge__final_search_result.
        -- assert (Hipos : 0 < i) by lia.
           rewrite !Znth_cons by lia.
           replace (i - 1 + 1) with i by lia.
           replace (i + 1 - 1) with i by lia.
           pose proof (Hsteps (i - 1) ltac:(
             repeat rewrite Zlength_cons;
             repeat rewrite Zlength_cons in Hi; lia)) as Hstep.
           replace (i - 1 + 1) with i in Hstep by lia.
           exact Hstep.
      * assert (Hpos : 0 < Zlength (x :: y :: rest) - 1).
        { repeat rewrite Zlength_cons.
          pose proof (Zlength_nonneg rest); lia. }
        rewrite Znth_cons by lia.
        assert (Hidx : Zlength (x :: y :: rest) - 1 - 1 =
          Zlength (Z.lxor x y :: rest) - 1).
        { repeat rewrite Zlength_cons; lia. }
        rewrite Hidx.
        rewrite Hend.
        simpl.
        reflexivity.
Qed.
Lemma one_xor_merge_decompose__final_search_result :
  forall left x y right,
    OneXorMerge
      (left ++ x :: y :: right)
      (left ++ Z.lxor x y :: right).
Proof.
  intros left x y right.
  exists (Zlength left).
  split.
  - repeat rewrite Zlength_app.
    repeat rewrite Zlength_cons.
    pose proof (Zlength_nonneg left).
    pose proof (Zlength_nonneg right).
    lia.
  - assert (Hprefix :
      sublist 0 (Zlength left) (left ++ x :: y :: right) = left).
    { apply sublist_app_exact1. }
    rewrite Hprefix.
    rewrite (app_Znth2 0 left (x :: y :: right) (Zlength left)) by lia.
    rewrite (app_Znth2 0 left (x :: y :: right) (Zlength left + 1)) by lia.
    replace (Zlength left - Zlength left) with 0 by lia.
    replace (Zlength left + 1 - Zlength left) with 1 by lia.
    simpl.
    f_equal.
    replace (left ++ x :: y :: right)
      with ((left ++ x :: y :: nil) ++ right)
      by (rewrite <- app_assoc; reflexivity).
    assert (Hframe_len : Zlength (left ++ x :: y :: nil) =
      Zlength left + 2).
    { rewrite Zlength_app, !Zlength_cons.
      rewrite Zlength_correct; simpl; lia. }
    assert (Hframe_bounds :
      Zlength left + 2 <= Zlength left + 2 <=
        Zlength ((left ++ x :: y :: nil) ++ right)).
    { rewrite Zlength_app, Hframe_len.
      pose proof (Zlength_nonneg right); lia. }
    erewrite sublist_split_app_r;
      [| exact Hframe_len | exact Hframe_bounds].
    replace (Zlength left + 2 - (Zlength left + 2)) with 0 by lia.
    replace
      (Zlength ((left ++ x :: y :: nil) ++ right) -
        (Zlength left + 2))
      with (Zlength right)
      by (rewrite Zlength_app, Hframe_len; lia).
    rewrite sublist_self by reflexivity.
    reflexivity.
Qed.
Lemma one_xor_merge_frame__final_search_result :
  forall prefix suffix a b,
    OneXorMerge a b ->
    OneXorMerge (prefix ++ a ++ suffix) (prefix ++ b ++ suffix).
Proof.
  intros prefix suffix a b Hmerge.
  destruct Hmerge as [i [Hi Hb]].
  pose proof (two_adjacent_decompose__final_search_result
    Z a 0 i Hi) as Ha.
  subst b.
  replace
    (prefix ++ a ++ suffix)
    with
    ((prefix ++ sublist 0 i a) ++
      Znth i a 0 :: Znth (i + 1) a 0 ::
      (sublist (i + 2) (Zlength a) a ++ suffix)).
  2:{ pose proof (f_equal
        (fun t : list Z => prefix ++ t ++ suffix) Ha) as Hctx.
      cbv beta in Hctx.
      repeat rewrite <- app_assoc in Hctx.
      repeat rewrite <- app_assoc.
      symmetry; exact Hctx. }
  replace
    (prefix ++
      (sublist 0 i a ++
       Z.lxor (Znth i a 0) (Znth (i + 1) a 0) ::
       sublist (i + 2) (Zlength a) a) ++ suffix)
    with
    ((prefix ++ sublist 0 i a) ++
      Z.lxor (Znth i a 0) (Znth (i + 1) a 0) ::
      (sublist (i + 2) (Zlength a) a ++ suffix))
    by (repeat rewrite <- app_assoc; reflexivity).
  apply one_xor_merge_decompose__final_search_result.
Qed.
Lemma collapse_xor_path_frame__final_search_result :
  forall prefix xs suffix,
    xs <> nil ->
    exists states,
      Zlength states = Zlength xs /\
      Znth 0 states nil = prefix ++ xs ++ suffix /\
      (forall i, 0 <= i < Zlength xs - 1 ->
        OneXorMerge (Znth i states nil) (Znth (i + 1) states nil)) /\
      Znth (Zlength xs - 1) states nil =
        prefix ++ (fold_left Z.lxor xs 0 :: nil) ++ suffix.
Proof.
  intros prefix xs suffix Hnon.
  destruct (collapse_all_xor_path__final_search_result xs Hnon)
    as [raw [Hlen [Hstart [Hsteps Hend]]]].
  exists (map (fun s => prefix ++ s ++ suffix) raw).
  split.
  - rewrite Zlength_map__final_search_result; exact Hlen.
  - assert (Hxslen : 1 <= Zlength xs).
    { apply nonempty_Zlength__final_search_result; exact Hnon. }
    split.
    + rewrite (Znth_map__final_search_result
        (list Z) (list Z) (fun s => prefix ++ s ++ suffix)
        raw 0 nil nil) by lia.
      rewrite Hstart; reflexivity.
    + split.
      * intros i Hi.
        rewrite (Znth_map__final_search_result
          (list Z) (list Z) (fun s => prefix ++ s ++ suffix)
          raw i nil nil) by (rewrite Hlen; lia).
        rewrite (Znth_map__final_search_result
          (list Z) (list Z) (fun s => prefix ++ s ++ suffix)
          raw (i + 1) nil nil) by (rewrite Hlen; lia).
        apply one_xor_merge_frame__final_search_result.
        apply Hsteps; exact Hi.
      * rewrite (Znth_map__final_search_result
          (list Z) (list Z) (fun s => prefix ++ s ++ suffix)
          raw (Zlength xs - 1) nil nil) by (rewrite Hlen; lia).
        rewrite Hend; reflexivity.
Qed.
Lemma append_merge_paths__final_search_result :
  forall states1 states2 m1 m2,
    0 <= m1 -> 0 <= m2 ->
    Zlength states1 = m1 + 1 ->
    Zlength states2 = m2 + 1 ->
    Znth m1 states1 nil = Znth 0 states2 nil ->
    (forall i, 0 <= i < m1 ->
      OneXorMerge (Znth i states1 nil) (Znth (i + 1) states1 nil)) ->
    (forall i, 0 <= i < m2 ->
      OneXorMerge (Znth i states2 nil) (Znth (i + 1) states2 nil)) ->
    exists states,
      Zlength states = m1 + m2 + 1 /\
      Znth 0 states nil = Znth 0 states1 nil /\
      (forall i, 0 <= i < m1 + m2 ->
        OneXorMerge (Znth i states nil) (Znth (i + 1) states nil)) /\
      Znth (m1 + m2) states nil = Znth m2 states2 nil.
Proof.
  intros states1 states2 m1 m2 Hm1 Hm2 Hlen1 Hlen2 Hjoin Hstep1 Hstep2.
  set (tail2 := sublist 1 (Zlength states2) states2).
  assert (Htail : Zlength tail2 = m2).
  { unfold tail2.
    rewrite Zlength_sublist by lia.
    rewrite Hlen2; lia. }
  exists (states1 ++ tail2).
  split.
  - rewrite Zlength_app, Hlen1, Htail; lia.
  - split.
    + rewrite (app_Znth1 nil states1 tail2 0) by lia.
      reflexivity.
    + split.
      * intros i Hi.
        destruct (Z_lt_dec i m1) as [Hil | Hil].
        -- rewrite (app_Znth1 nil states1 tail2 i) by lia.
           rewrite (app_Znth1 nil states1 tail2 (i + 1)) by lia.
           apply Hstep1; lia.
        -- assert (Him1 : i = m1 \/ m1 < i) by lia.
           destruct Him1 as [-> | Higt].
           ++ rewrite (app_Znth1 nil states1 tail2 m1) by lia.
              rewrite (app_Znth2 nil states1 tail2 (m1 + 1)) by lia.
              replace (m1 + 1 - Zlength states1) with 0 by lia.
              unfold tail2.
              rewrite (Znth_sublist nil 1 0 (Zlength states2) states2) by lia.
              replace (0 + 1) with 1 by lia.
              rewrite Hjoin.
              apply Hstep2; lia.
           ++ rewrite (app_Znth2 nil states1 tail2 i) by lia.
              rewrite (app_Znth2 nil states1 tail2 (i + 1)) by lia.
              unfold tail2.
              rewrite (Znth_sublist nil 1
                (i - Zlength states1) (Zlength states2) states2) by lia.
              rewrite (Znth_sublist nil 1
                (i + 1 - Zlength states1) (Zlength states2) states2) by lia.
              replace (i - Zlength states1 + 1) with (i - m1) by lia.
              replace (i + 1 - Zlength states1 + 1) with (i - m1 + 1) by lia.
              apply Hstep2; lia.
      * destruct (Z.eq_dec m2 0) as [-> | Hm2nz].
        -- replace (m1 + 0) with m1 by lia.
           rewrite (app_Znth1 nil states1 tail2 m1) by lia.
           exact Hjoin.
        -- assert (Hm2pos : 0 < m2) by lia.
           rewrite (app_Znth2 nil states1 tail2 (m1 + m2)) by lia.
           unfold tail2.
           rewrite (Znth_sublist nil 1
             (m1 + m2 - Zlength states1) (Zlength states2) states2) by lia.
           replace (m1 + m2 - Zlength states1 + 1) with m2 by lia.
           reflexivity.
Qed.
Lemma adjacent_blocks_destroy_trace__final_search_result :
  forall prefix left right suffix,
    left <> nil -> right <> nil ->
    fold_left Z.lxor left 0 > fold_left Z.lxor right 0 ->
    DestroyTrace (prefix ++ left ++ right ++ suffix)
      (Zlength left + Zlength right - 2).
Proof.
  intros prefix left right suffix Hleft Hright Hxor.
  set (xl := fold_left Z.lxor left 0).
  set (xr := fold_left Z.lxor right 0).
  destruct (collapse_xor_path_frame__final_search_result
    prefix left (right ++ suffix) Hleft)
    as [states1 [Hlen1 [Hstart1 [Hstep1 Hend1]]]].
  destruct (collapse_xor_path_frame__final_search_result
    (prefix ++ xl :: nil) right suffix Hright)
    as [states2 [Hlen2 [Hstart2 [Hstep2 Hend2]]]].
  assert (Hleftlen : 1 <= Zlength left).
  { apply nonempty_Zlength__final_search_result; exact Hleft. }
  assert (Hrightlen : 1 <= Zlength right).
  { apply nonempty_Zlength__final_search_result; exact Hright. }
  assert (Hjoin :
    Znth (Zlength left - 1) states1 nil = Znth 0 states2 nil).
  { rewrite Hend1, Hstart2.
    unfold xl.
    repeat rewrite <- app_assoc.
    reflexivity. }
  destruct (append_merge_paths__final_search_result
    states1 states2 (Zlength left - 1) (Zlength right - 1)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    Hjoin Hstep1 Hstep2)
    as [states [Hstates [Hstart [Hsteps Hend]]]].
  unfold DestroyTrace.
  exists states.
  split; [lia |].
  split.
  - rewrite Hstart, Hstart1.
    repeat rewrite <- app_assoc.
    reflexivity.
  - split.
    + intros i Hi.
      apply Hsteps; lia.
    + exists (Zlength prefix).
      replace (Zlength left + Zlength right - 2)
        with ((Zlength left - 1) + (Zlength right - 1)) by lia.
      rewrite Hend, Hend2.
      unfold xl, xr in *.
      assert (Hfinal :
        (prefix ++ fold_left Z.lxor left 0 :: nil) ++
          (fold_left Z.lxor right 0 :: nil) ++ suffix =
        prefix ++ fold_left Z.lxor left 0 ::
          fold_left Z.lxor right 0 :: suffix).
      { repeat rewrite <- app_assoc; reflexivity. }
      rewrite Hfinal.
      split.
      * repeat rewrite Zlength_app.
        repeat rewrite Zlength_cons.
        rewrite Zlength_correct; simpl.
        pose proof (Zlength_nonneg prefix).
        pose proof (Zlength_nonneg suffix).
        lia.
      * rewrite (app_Znth2 0 prefix
          (fold_left Z.lxor left 0 ::
           fold_left Z.lxor right 0 :: suffix)
          (Zlength prefix)) by lia.
        rewrite (app_Znth2 0 prefix
          (fold_left Z.lxor left 0 ::
           fold_left Z.lxor right 0 :: suffix)
          (Zlength prefix + 1)) by lia.
        replace (Zlength prefix - Zlength prefix) with 0 by lia.
        replace (Zlength prefix + 1 - Zlength prefix) with 1 by lia.
        simpl; exact Hxor.
Qed.
Lemma prefix_xor_sublist__final_search_result :
  forall a lo hi,
    0 <= lo <= hi /\ hi <= Zlength a ->
    Z.lxor (PrefixXor a hi) (PrefixXor a lo) =
      fold_left Z.lxor (sublist lo hi a) 0.
Proof.
  intros a lo hi Hbounds.
  set (prefix := sublist 0 lo a).
  set (block := sublist lo hi a).
  set (suffix := sublist hi (Zlength a) a).
  assert (Hdecomp : a = prefix ++ block ++ suffix).
  { unfold prefix, block, suffix.
    rewrite <- (sublist_self a) at 1 by reflexivity.
    rewrite (sublist_split 0 (Zlength a) lo a) by lia.
    rewrite (sublist_split lo (Zlength a) hi a) by lia.
    rewrite app_assoc; reflexivity. }
  assert (Hprefix : Zlength prefix = lo).
  { unfold prefix; rewrite Zlength_sublist by lia; lia. }
  assert (Hblock : Zlength block = hi - lo).
  { unfold block; rewrite Zlength_sublist by lia; lia. }
  pose proof (prefix_xor_segment__final_search_result
    prefix block suffix) as Hsegment.
  rewrite <- Hdecomp in Hsegment.
  rewrite Hprefix, Hblock in Hsegment.
  replace (lo + (hi - lo)) with hi in Hsegment by lia.
  exact Hsegment.
Qed.
Lemma destructive_window_to_trace__final_search_result :
  forall a l mid r,
    DestructiveWindow a l mid r ->
    DestroyTrace a (r - l - 1).
Proof.
  intros a l mid r Hwindow.
  unfold DestructiveWindow in Hwindow.
  destruct Hwindow as [[Hl Hlm] [[Hmr Hr] Hxor]].
  set (prefix := sublist 0 l a).
  set (left := sublist l (mid + 1) a).
  set (right := sublist (mid + 1) (r + 1) a).
  set (suffix := sublist (r + 1) (Zlength a) a).
  assert (Hdecomp : a = prefix ++ left ++ right ++ suffix).
  { unfold prefix, left, right, suffix.
    rewrite <- (sublist_self a) at 1 by reflexivity.
    rewrite (sublist_split 0 (Zlength a) l a) by lia.
    rewrite (sublist_split l (Zlength a) (mid + 1) a) by lia.
    rewrite (sublist_split (mid + 1) (Zlength a) (r + 1) a) by lia.
    repeat rewrite app_assoc; reflexivity. }
  assert (Hleftlen : Zlength left = mid + 1 - l).
  { unfold left; rewrite Zlength_sublist by lia; lia. }
  assert (Hrightlen : Zlength right = r - mid).
  { unfold right; rewrite Zlength_sublist by lia; lia. }
  assert (Hleft : left <> nil).
  { intro Hnil; rewrite Hnil in Hleftlen.
    rewrite Zlength_correct in Hleftlen; simpl in Hleftlen; lia. }
  assert (Hright : right <> nil).
  { intro Hnil; rewrite Hnil in Hrightlen.
    rewrite Zlength_correct in Hrightlen; simpl in Hrightlen; lia. }
  assert (Hleftxor :
    Z.lxor (PrefixXor a (mid + 1)) (PrefixXor a l) =
      fold_left Z.lxor left 0).
  { unfold left.
    apply prefix_xor_sublist__final_search_result; lia. }
  assert (Hrightxor :
    Z.lxor (PrefixXor a (r + 1)) (PrefixXor a (mid + 1)) =
      fold_left Z.lxor right 0).
  { unfold right.
    apply prefix_xor_sublist__final_search_result; lia. }
  rewrite Hleftxor, Hrightxor in Hxor.
  rewrite Hdecomp.
  replace (r - l - 1)
    with (Zlength left + Zlength right - 2) by lia.
  apply adjacent_blocks_destroy_trace__final_search_result;
    assumption.
Qed.
Lemma destroy_trace_window_characterization__final_search_result :
  forall a,
    1 <= Zlength a ->
    (forall moves, DestroyTrace a moves ->
      exists l mid r,
        DestructiveWindow a l mid r /\ r - l - 1 <= moves) /\
    (forall l mid r, DestructiveWindow a l mid r ->
      DestroyTrace a (r - l - 1)).
Proof.
  intros a Ha.
  split.
  - intros moves Htrace.
    apply destroy_trace_to_window__final_search_result; assumption.
  - intros l mid r Hwindow.
    exact (destructive_window_to_trace__final_search_result
      a l mid r Hwindow).
Qed.
Lemma finished_window_search_spec_min__final_search_result :
  forall a n best,
    2 <= n ->
    n = Zlength a ->
    best <> 2147483647 ->
    BruteSearchState a n n (n + 1) best ->
    Spec a best.
Proof.
  intros a n best Hn Hlen Hbest_not Hstate.
  unfold BruteSearchState in Hstate.
  destruct Hstate as [[Hsentinel Hnone] | Hminimum].
  - contradiction.
  - unfold Spec.
    right.
    unfold min_value_of_subset, min_object_of_subset in *.
    destruct Hminimum as [chosen [[Hcandidate Hleast] Hbest]].
    unfold WindowMoveCandidate in Hcandidate.
    destruct Hcandidate as [l [mid [r [Hwindow [Hbefore Hchosen]]]]].
    assert (Hchosen_trace : DestroyTrace a chosen).
    { rewrite Hchosen.
      apply destructive_window_to_trace__final_search_result with (mid := mid).
      exact Hwindow. }
    exists chosen.
    split.
    + split; [exact Hchosen_trace |].
      intros moves Htrace.
      destruct (destroy_trace_to_window__final_search_result
        a moves ltac:(lia) Htrace)
        as [l' [mid' [r' [Hwindow' Hmoves]]]].
      pose proof (finished_window_candidate__final_search_result
        a n l' mid' r' Hlen Hwindow') as Hcandidate'.
      specialize (Hleast (r' - l' - 1) Hcandidate').
      simpl in Hleast.
      lia.
    + exact Hbest.
Qed.
Lemma sorted_no_equal_bit_triples_length_bound__large_input_final :
  forall (values : list Z) (n i : Z),
    n = Zlength values ->
    2 <= n ->
    (forall k, 0 <= k < n ->
      1 <= Znth k values 0 <= 1000000000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
      Znth k values 0 <= Znth (k + 1) values 0) ->
    1 <= i ->
    i <= n - 1 ->
    i + 1 >= n ->
    NoEqualBitTriplePrefix values i ->
    n <= 60.
Proof.
  intros values n i Hlength Hn Hbounds Hsorted Hi Hile Hdone Htriples.
  assert (Hlarge_dec : n <= 60 \/ n > 60) by lia.
  destruct Hlarge_dec as [Hsmall | Hlarge]; [exact Hsmall |].
  unfold NoEqualBitTriplePrefix in Htriples.
  assert (Hstep : forall j, 0 <= j < 30 ->
      Z.log2 (Znth (2 * j) values 0) <
      Z.log2 (Znth (2 * (j + 1)) values 0)).
  {
    intros j Hj.
    pose proof (Hsorted (2 * j) ltac:(lia)) as Hsorted01.
    pose proof (Hsorted (2 * j + 1) ltac:(lia)) as Hsorted12.
    pose proof (Z.log2_le_mono _ _ Hsorted01) as Hlog01.
    pose proof (Z.log2_le_mono _ _ Hsorted12) as Hlog12.
    replace (2 * j + 1 + 1) with (2 * (j + 1)) in Hlog12 by lia.
    pose proof (Htriples (2 * j + 1) ltac:(lia)) as Hnot_equal.
    replace (2 * j + 1 - 1) with (2 * j) in Hnot_equal by lia.
    replace (2 * j + 1 + 1) with (2 * (j + 1)) in Hnot_equal by lia.
    assert (Hends :
      Z.log2 (Znth (2 * j) values 0) <>
      Z.log2 (Znth (2 * (j + 1)) values 0)).
    {
      intro Heq.
      apply Hnot_equal.
      split; lia.
    }
    lia.
  }
  pose proof (Hstep 0 ltac:(lia)) as Hstep00.
  pose proof (Hstep 1 ltac:(lia)) as Hstep01.
  pose proof (Hstep 2 ltac:(lia)) as Hstep02.
  pose proof (Hstep 3 ltac:(lia)) as Hstep03.
  pose proof (Hstep 4 ltac:(lia)) as Hstep04.
  pose proof (Hstep 5 ltac:(lia)) as Hstep05.
  pose proof (Hstep 6 ltac:(lia)) as Hstep06.
  pose proof (Hstep 7 ltac:(lia)) as Hstep07.
  pose proof (Hstep 8 ltac:(lia)) as Hstep08.
  pose proof (Hstep 9 ltac:(lia)) as Hstep09.
  pose proof (Hstep 10 ltac:(lia)) as Hstep10.
  pose proof (Hstep 11 ltac:(lia)) as Hstep11.
  pose proof (Hstep 12 ltac:(lia)) as Hstep12.
  pose proof (Hstep 13 ltac:(lia)) as Hstep13.
  pose proof (Hstep 14 ltac:(lia)) as Hstep14.
  pose proof (Hstep 15 ltac:(lia)) as Hstep15.
  pose proof (Hstep 16 ltac:(lia)) as Hstep16.
  pose proof (Hstep 17 ltac:(lia)) as Hstep17.
  pose proof (Hstep 18 ltac:(lia)) as Hstep18.
  pose proof (Hstep 19 ltac:(lia)) as Hstep19.
  pose proof (Hstep 20 ltac:(lia)) as Hstep20.
  pose proof (Hstep 21 ltac:(lia)) as Hstep21.
  pose proof (Hstep 22 ltac:(lia)) as Hstep22.
  pose proof (Hstep 23 ltac:(lia)) as Hstep23.
  pose proof (Hstep 24 ltac:(lia)) as Hstep24.
  pose proof (Hstep 25 ltac:(lia)) as Hstep25.
  pose proof (Hstep 26 ltac:(lia)) as Hstep26.
  pose proof (Hstep 27 ltac:(lia)) as Hstep27.
  pose proof (Hstep 28 ltac:(lia)) as Hstep28.
  pose proof (Hstep 29 ltac:(lia)) as Hstep29.
  cbn in Hstep00, Hstep01, Hstep02, Hstep03, Hstep04,
    Hstep05, Hstep06, Hstep07, Hstep08, Hstep09,
    Hstep10, Hstep11, Hstep12, Hstep13, Hstep14,
    Hstep15, Hstep16, Hstep17, Hstep18, Hstep19,
    Hstep20, Hstep21, Hstep22, Hstep23, Hstep24,
    Hstep25, Hstep26, Hstep27, Hstep28, Hstep29.
  pose proof (Hbounds 60 ltac:(lia)) as Hvalue_bound.
  destruct Hvalue_bound as [Hpositive Hupper].
  assert (Hbelow_power : Znth 60 values 0 < 2 ^ 30).
  {
    change (Znth 60 values 0 < 1073741824).
    lia.
  }
  assert (Hpositive0 : 0 < Znth 60 values 0) by lia.
  pose proof
    (proj1 (Z.log2_lt_pow2 (Znth 60 values 0) 30 Hpositive0)
      Hbelow_power) as Hlog_upper.
  pose proof (Z.log2_nonneg (Znth 0 values 0)) as Hlog_nonnegative.
  lia.
Qed.
