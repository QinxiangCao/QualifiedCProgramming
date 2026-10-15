Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* The row two chosen rows combine into: each column keeps the larger value. *)
Definition CombinedEntry (rows : list (list Z)) (i j c : Z) : Z :=
  Z.max (Znth c (Znth i rows []) 0) (Znth c (Znth j rows []) 0).

(* What a pair of rows scores: the smallest entry of the combined row. *)
Definition PairScore (rows : list (list Z)) (i j score : Z) : Prop :=
  0 <= i < Zlength rows /\ 0 <= j < Zlength rows /\
  min_value_of_subset Z.le
    (fun v => exists c, 0 <= c < Zlength (Znth i rows []) /\
                v = CombinedEntry rows i j c)
    (fun x => x) score.
Definition Pre (rows : list (list Z)) : Prop :=
  (* Stated explicitly in the P066 solver Require, so dropped here:
       1 <= Zlength rows <= 300000  *)
  exists m, 1 <= m <= 8 /\
  Forall (fun row => Zlength row = m) rows
  (* Element bounds are stated explicitly in both solver and feasible Require. *)
  (* /\ Forall (Forall (fun x => 0 <= x <= 1000000000)) rows *)
  .

Definition MatrixEntriesBounded (rows : list (list Z)) : Prop :=
  Forall (Forall (fun x => 0 <= x <= 1000000000)) rows.

Definition Spec (rows : list (list Z)) (out : Z * Z) : Prop :=
  exists best, PairScore rows (fst out - 1) (snd out - 1) best /\
  max_value_of_subset Z.le
    (fun v => exists i j, PairScore rows i j v)
    (fun x => x) best.

(* A threshold is met when two valid rows cover every matrix column.  This is
   the public decision meaning of [feasible], independent of its mask-based
   implementation. *)
Definition PairAtLeast
    (rows : list (list Z)) (threshold i j : Z) : Prop :=
  0 <= i < Zlength rows /\
  0 <= j < Zlength rows /\
  forall c,
    0 <= c < Zlength (Znth 0 rows []) ->
    threshold <= CombinedEntry rows i j c.

Definition FeasibleAtThreshold
    (rows : list (list Z)) (threshold : Z) : Prop :=
  exists i j, PairAtLeast rows threshold i j.

(* The stable mathematical meaning of a partially constructed threshold mask.
   Machine ranges and the matrix resource stay explicit in the C invariant. *)
Definition RowMaskPrefix
    (rows : list (list Z))
    (threshold row cols mask : Z) : Prop :=
  0 <= mask < 2 ^ cols /\
  forall c,
    0 <= c < cols ->
    (Z.testbit mask c = true <->
     threshold <= Znth c (Znth row rows []) 0).

(* [reps] is complete and sound for the rows in [0, processed_rows). *)
Definition RepresentativePrefix
    (rows : list (list Z))
    (threshold width processed_rows : Z)
    (reps : list Z) : Prop :=
  forall mask,
    0 <= mask < 2 ^ width ->
    ((Znth mask reps (-1) = -1 /\
      forall row,
        0 <= row < processed_rows ->
        ~ RowMaskPrefix rows threshold row width mask) \/
     (exists row,
        0 <= row < processed_rows /\
        Znth mask reps (-1) = row /\
        RowMaskPrefix rows threshold row width mask)).

(* All represented mask pairs preceding [(first_mask,next_second_mask)] in
   lexicographic search order have been ruled out. *)
Definition NoCoverPrefix
    (reps : list Z) (full first_mask next_second_mask : Z) : Prop :=
  forall s u,
    0 <= s <= full ->
    0 <= u <= full ->
    (s < first_mask \/ (s = first_mask /\ u < next_second_mask)) ->
    0 <= Znth s reps (-1) ->
    0 <= Znth u reps (-1) ->
    Z.lor s u <> full.

Definition OptimalPairScore (rows : list (list Z)) (best : Z) : Prop :=
  max_value_of_subset Z.le
    (fun v => exists i j, PairScore rows i j v)
    (fun x => x) best.

Definition SolverSearchMeaning
    (rows : list (list Z)) (lo hi current_i current_j : Z) : Prop :=
  exists best,
    OptimalPairScore rows best /\
    lo <= best <= hi /\
    PairAtLeast rows lo current_i current_j.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.Zquot.
Lemma row_mask_set_next__row_mask_step :
  forall rows threshold row j mask,
    0 <= j ->
    RowMaskPrefix rows threshold row j mask ->
    threshold <= Znth j (Znth row rows []) 0 ->
    RowMaskPrefix rows threshold row (j + 1) (Z.lor mask (2 ^ j)).
Proof.
  intros rows threshold row j mask Hj Hprefix Hentry.
  unfold RowMaskPrefix in *.
  destruct Hprefix as [[Hmask_nonneg Hmask_bound] Hprefix].
  split.
  - split.
    + apply Z.lor_nonneg. split; [exact Hmask_nonneg |].
      apply Z.pow_nonneg; lia.
    + assert (Hpow_pos : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
      assert (Hlor_pos : 0 < Z.lor mask (2 ^ j)).
      { assert (Hlor_nonneg : 0 <= Z.lor mask (2 ^ j)).
        { apply Z.lor_nonneg. lia. }
        assert (Hlor_neq : Z.lor mask (2 ^ j) <> 0).
        { intro Heq.
          apply Z.lor_eq_0_iff in Heq.
          lia. }
        lia. }
      apply (proj2 (Z.log2_lt_pow2 _ _ Hlor_pos)).
      rewrite Z.log2_lor by lia.
      rewrite Z.log2_pow2 by lia.
      assert (Z.log2 mask <= j).
      { rewrite <- Z.log2_pow2 by lia.
        apply Z.log2_le_mono. lia. }
      apply Z.max_lub_lt; lia.
  - intros c Hc.
    rewrite Z.lor_spec.
    destruct (Z.lt_trichotomy c j) as [Hlt | [Heq | Hgt]].
    + rewrite Z.pow2_bits_false by lia.
      rewrite Bool.orb_false_r.
      apply Hprefix. lia.
    + subst c.
      rewrite Z.pow2_bits_true by lia.
      rewrite Bool.orb_true_r.
      split; intro; [exact Hentry | reflexivity].
    + exfalso. lia.
Qed.
Lemma row_mask_clear_next__row_mask_step :
  forall rows threshold row j mask,
    0 <= j ->
    RowMaskPrefix rows threshold row j mask ->
    Znth j (Znth row rows []) 0 < threshold ->
    RowMaskPrefix rows threshold row (j + 1) mask.
Proof.
  intros rows threshold row j mask Hj Hprefix Hentry.
  unfold RowMaskPrefix in *.
  destruct Hprefix as [[Hmask_nonneg Hmask_bound] Hprefix].
  split.
  - split; [exact Hmask_nonneg |].
    replace (j + 1) with (Z.succ j) by lia.
    rewrite Z.pow_succ_r by lia.
    assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    nia.
  - assert (Hbit_j : Z.testbit mask j = false).
    { apply (proj2 (Z.testbit_false mask j Hj)).
      rewrite Z.div_small by lia.
      reflexivity. }
    intros c Hc.
    destruct (Z.lt_trichotomy c j) as [Hlt | [Heq | Hgt]].
    + apply Hprefix. lia.
    + subst c. rewrite Hbit_j.
      split; intro H; [discriminate | lia].
    + exfalso. lia.
Qed.
Lemma row_mask_complete_unique__representative_update :
  forall rows threshold row width mask1 mask2,
    0 <= width ->
    RowMaskPrefix rows threshold row width mask1 ->
    RowMaskPrefix rows threshold row width mask2 ->
    mask1 = mask2.
Proof.
  intros rows threshold row width mask1 mask2 Hwidth Hmask1 Hmask2.
  unfold RowMaskPrefix in *.
  destruct Hmask1 as [[Hmask1_nonneg Hmask1_bound] Hbits1].
  destruct Hmask2 as [[Hmask2_nonneg Hmask2_bound] Hbits2].
  apply Z.bits_inj'.
  intros c Hc.
  destruct (Z_lt_ge_dec c width) as [Hbelow | Habove].
  - destruct (Z.testbit mask1 c) eqn:Hbit1,
             (Z.testbit mask2 c) eqn:Hbit2; auto.
    + exfalso.
      pose proof (proj1 (Hbits1 c ltac:(lia)) Hbit1) as Hentry.
      pose proof (proj2 (Hbits2 c ltac:(lia)) Hentry) as Hcontra.
      congruence.
    + exfalso.
      pose proof (proj1 (Hbits2 c ltac:(lia)) Hbit2) as Hentry.
      pose proof (proj2 (Hbits1 c ltac:(lia)) Hentry) as Hcontra.
      congruence.
  - rewrite <- (Z.mod_small mask1 (2 ^ width) ltac:(lia)).
    rewrite <- (Z.mod_small mask2 (2 ^ width) ltac:(lia)).
    rewrite !Z.mod_pow2_bits_high by lia.
    reflexivity.
Qed.
Lemma representative_insert__representative_update :
  forall rows threshold width i reps mask,
    0 <= width ->
    0 <= i ->
    0 <= mask < 2 ^ width ->
    2 ^ width <= Zlength reps ->
    RepresentativePrefix rows threshold width i reps ->
    Znth mask reps (-1) = -1 ->
    RowMaskPrefix rows threshold i width mask ->
    RepresentativePrefix rows threshold width (i + 1)
      (replace_Znth mask i reps).
Proof.
  intros rows threshold width i reps mask Hwidth Hi Hmask Hlen Hrep Hempty Hrow.
  unfold RepresentativePrefix in *.
  intros q Hq.
  destruct (Z.eq_dec q mask) as [-> | Hneq].
  - right. exists i. split; [lia |]. split.
    + rewrite Znth_replace_Znth_Same by lia. reflexivity.
    + exact Hrow.
  - assert (Hmask_in : 0 <= mask < Zlength reps) by lia.
    assert (Hq_in : 0 <= q < Zlength reps) by lia.
    rewrite (@Znth_replace_Znth_Diff Z (-1) reps mask q i
      Hmask_in Hq_in ltac:(lia)).
    specialize (Hrep q Hq).
    destruct Hrep as [[Hqempty Hnone] | [row [Hrow_range [Hqrow Hrowmask]]]].
    + left. split; [exact Hqempty |].
      intros row Hrow_range Hrowmask.
      destruct (Z_lt_ge_dec row i) as [Hrow_old | Hrow_new].
      * apply (Hnone row); [lia | exact Hrowmask].
      * assert (row = i) by lia. subst row.
        pose proof (row_mask_complete_unique__representative_update
          rows threshold i width q mask Hwidth Hrowmask Hrow) as Heq.
        contradiction.
    + right. exists row. split; [lia |]. split; assumption.
Qed.
Lemma representative_skip__representative_update :
  forall rows threshold width i reps mask,
    0 <= width ->
    0 <= mask < 2 ^ width ->
    RepresentativePrefix rows threshold width i reps ->
    0 <= Znth mask reps (-1) ->
    RowMaskPrefix rows threshold i width mask ->
    RepresentativePrefix rows threshold width (i + 1) reps.
Proof.
  intros rows threshold width i reps mask Hwidth Hmask Hrep Hpresent Hrow.
  unfold RepresentativePrefix in *.
  intros q Hq.
  specialize (Hrep q Hq).
  destruct Hrep as [[Hqempty Hnone] | [row [Hrow_range [Hqrow Hrowmask]]]].
  - left. split; [exact Hqempty |].
    intros row Hrow_range Hrowmask.
    destruct (Z_lt_ge_dec row i) as [Hrow_old | Hrow_new].
    + apply (Hnone row); [lia | exact Hrowmask].
    + assert (row = i) by lia. subst row.
      pose proof (row_mask_complete_unique__representative_update
        rows threshold i width q mask Hwidth Hrowmask Hrow) as Heq.
      subst q. lia.
  - right. exists row. split; [lia |]. split; assumption.
Qed.
Lemma no_cover_outer_missing__cover_search :
  forall reps full s next,
    NoCoverPrefix reps full s next ->
    (full < next \/ Znth s reps (-1) < 0) ->
    NoCoverPrefix reps full (s + 1) 0.
Proof.
  unfold NoCoverPrefix.
  intros reps full s next Hprefix Hfinished s' u Hs' Hu Hbefore Hsrep Hurep.
  destruct Hbefore as [Hfirst | [Hfirst Hu0]].
  - destruct (Z_lt_ge_dec s' s) as [Hlt | Hge].
    + eapply Hprefix; eauto.
    + assert (s' = s) by lia. subst s'.
      destruct Hfinished as [Hnext | Hmissing].
      * eapply Hprefix; eauto. right. lia.
      * lia.
  - lia.
Qed.
Lemma no_cover_inner_missing__cover_search :
  forall reps full s u,
    NoCoverPrefix reps full s u ->
    Znth u reps (-1) < 0 ->
    NoCoverPrefix reps full s (u + 1).
Proof.
  unfold NoCoverPrefix.
  intros reps full s u Hprefix Hmissing s' u' Hs' Hu' Hbefore Hsrep Hurep.
  destruct Hbefore as [Hfirst | [Hfirst Hsecond]].
  - eapply Hprefix; eauto.
  - subst s'.
    destruct (Z_lt_ge_dec u' u) as [Hlt | Hge].
    + eapply Hprefix; eauto.
    + assert (u' = u) by lia. subst u'. lia.
Qed.
Lemma no_cover_inner_noncover__cover_search :
  forall reps full s u,
    NoCoverPrefix reps full s u ->
    Z.lor s u <> full ->
    NoCoverPrefix reps full s (u + 1).
Proof.
  unfold NoCoverPrefix.
  intros reps full s u Hprefix Hnoncover s' u' Hs' Hu' Hbefore Hsrep Hurep.
  destruct Hbefore as [Hfirst | [Hfirst Hsecond]].
  - eapply Hprefix; eauto.
  - subst s'.
    destruct (Z_lt_ge_dec u' u) as [Hlt | Hge].
    + eapply Hprefix; eauto.
    + assert (u' = u) by lia. subst u'. exact Hnoncover.
Qed.
Lemma row_mask_prefix_exists__feasible_outcomes :
  forall rows threshold row cols,
    0 <= cols ->
    exists mask, RowMaskPrefix rows threshold row cols mask.
Proof.
  intros rows threshold row cols Hcols.
  remember (Z.to_nat cols) as n eqn:Hn.
  assert (Hcols_nat : cols = Z.of_nat n).
  { subst n. rewrite Z2Nat.id by exact Hcols. reflexivity. }
  subst cols.
  clear Hcols Hn.
  induction n as [|n IH].
  - exists 0.
    unfold RowMaskPrefix.
    split.
    + cbn. lia.
    + intros c Hc. lia.
  - destruct IH as [mask [Hrange Hbits]].
    rewrite Nat2Z.inj_succ.
    set (k := Z.of_nat n) in *.
    destruct (Z_le_dec threshold (Znth k (Znth row rows []) 0)) as [Hentry | Hentry].
    + exists (Z.setbit mask k).
      unfold RowMaskPrefix.
      split.
      * split.
        -- rewrite Z.setbit_spec'.
           apply (proj2 (Z.lor_nonneg mask (2 ^ k))).
           split; [lia | apply Z.pow_nonneg; lia].
        -- rewrite Z.setbit_spec'.
           pose proof (Z.add_lor_land mask (2 ^ k)) as Hsum.
           assert (0 <= Z.land mask (2 ^ k)).
           { apply (proj2 (Z.land_nonneg mask (2 ^ k))). left. lia. }
           rewrite Z.pow_succ_r by lia.
           lia.
      * intros c Hc.
        destruct (Z.eq_dec c k) as [-> | Hne].
        -- rewrite Z.setbit_eq by lia. tauto.
        -- rewrite Z.setbit_neq by lia.
           apply Hbits. lia.
    + exists mask.
      unfold RowMaskPrefix.
      split.
      * split; [lia |].
        rewrite Z.pow_succ_r by lia.
        assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
        lia.
      * intros c Hc.
        destruct (Z.eq_dec c k) as [-> | Hne].
        -- assert (Hbit : Z.testbit mask k = false).
           { rewrite <- (Z.mod_small mask (2 ^ k)) by exact Hrange.
             apply Z.mod_pow2_bits_high. lia. }
           rewrite Hbit.
           split; [discriminate |].
           intro Hcontra. contradiction.
        -- apply Hbits. lia.
Qed.
Lemma row_masks_lor_full__feasible_outcomes :
  forall rows threshold width i j left right,
    0 <= width ->
    width = Zlength (Znth 0 rows []) ->
    PairAtLeast rows threshold i j ->
    RowMaskPrefix rows threshold i width left ->
    RowMaskPrefix rows threshold j width right ->
    Z.lor left right = Z.shiftl 1 width - 1.
Proof.
  intros rows threshold width i j left right Hwidth Hwidth_eq
    Hpair Hleft Hright.
  destruct Hpair as [Hi [Hj Hcover]].
  destruct Hleft as [Hleft_range Hleft_bits].
  destruct Hright as [Hright_range Hright_bits].
  apply Z.bits_inj.
  intro c.
  destruct (Z_lt_ge_dec c 0) as [Hcneg | Hcnonneg].
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
  - destruct (Z_lt_ge_dec c width) as [Hclt | Hchigh].
    + rewrite Z.lor_spec.
      replace (Z.shiftl 1 width - 1) with (Z.ones width).
      2: { rewrite Z.shiftl_1_l, Z.ones_equiv. lia. }
      rewrite Z.testbit_ones_nonneg by lia.
      replace (c <? width) with true by (symmetry; apply Z.ltb_lt; lia).
      apply Bool.orb_true_iff.
      specialize (Hcover c).
      rewrite <- Hwidth_eq in Hcover.
      specialize (Hcover ltac:(lia)).
      unfold CombinedEntry in Hcover.
      assert (threshold <= Znth c (Znth i rows []) 0 \/
              threshold <= Znth c (Znth j rows []) 0) by lia.
      destruct H as [H | H].
      * left. apply (proj2 (Hleft_bits c ltac:(lia))). exact H.
      * right. apply (proj2 (Hright_bits c ltac:(lia))). exact H.
    + rewrite Z.lor_spec.
      assert (Hlb : Z.testbit left c = false).
      { rewrite <- (Z.mod_small left (2 ^ width)) by exact Hleft_range.
        apply Z.mod_pow2_bits_high. lia. }
      assert (Hrb : Z.testbit right c = false).
      { rewrite <- (Z.mod_small right (2 ^ width)) by exact Hright_range.
        apply Z.mod_pow2_bits_high. lia. }
      rewrite Hlb, Hrb.
      replace (Z.shiftl 1 width - 1) with (Z.ones width).
      2: { rewrite Z.shiftl_1_l, Z.ones_equiv. lia. }
      rewrite Z.testbit_ones_nonneg by lia.
      replace (c <? width) with false by (symmetry; apply Z.ltb_ge; lia).
      reflexivity.
Qed.
Lemma row_masks_cover_pair__feasible_outcomes :
  forall rows threshold width i j left right,
    width = Zlength (Znth 0 rows []) ->
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    RowMaskPrefix rows threshold i width left ->
    RowMaskPrefix rows threshold j width right ->
    Z.lor left right = Z.shiftl 1 width - 1 ->
    PairAtLeast rows threshold i j.
Proof.
  intros rows threshold width i j left right Hwidth Hi Hj
    Hleft Hright Hlor.
  unfold PairAtLeast, CombinedEntry.
  split; [exact Hi |].
  split; [exact Hj |].
  intros c Hc.
  destruct Hleft as [_ Hleft_bits].
  destruct Hright as [_ Hright_bits].
  assert (Hfullbit : Z.testbit (Z.shiftl 1 width - 1) c = true).
  { replace (Z.shiftl 1 width - 1) with (Z.ones width).
    2: { rewrite Z.shiftl_1_l, Z.ones_equiv. lia. }
    rewrite Z.testbit_ones_nonneg by lia.
    apply Z.ltb_lt. lia. }
  rewrite <- Hlor, Z.lor_spec in Hfullbit.
  apply Bool.orb_true_iff in Hfullbit.
  destruct Hfullbit as [Hleftbit | Hrightbit].
  - apply (proj1 (Hleft_bits c ltac:(lia))) in Hleftbit.
    lia.
  - apply (proj1 (Hright_bits c ltac:(lia))) in Hrightbit.
    lia.
Qed.
Lemma completed_no_cover_excludes_feasible__feasible_outcomes :
  forall rows threshold width processed reps first full,
    0 <= width ->
    processed = Zlength rows ->
    width = Zlength (Znth 0 rows []) ->
    full = Z.shiftl 1 width - 1 ->
    RepresentativePrefix rows threshold width processed reps ->
    NoCoverPrefix reps full first 0 ->
    first > full ->
    ~ FeasibleAtThreshold rows threshold.
Proof.
  intros rows threshold width processed reps first full Hwidth Hprocessed
    Hwidth_eq Hfull Hrepresent Hnocover Hfirst.
  intros (i & j & Hpair).
  destruct (row_mask_prefix_exists__feasible_outcomes rows threshold i width Hwidth)
    as (left & Hleft).
  destruct (row_mask_prefix_exists__feasible_outcomes rows threshold j width Hwidth)
    as (right & Hright).
  assert (Hlor : Z.lor left right = full).
  { rewrite Hfull.
    eapply row_masks_lor_full__feasible_outcomes; eauto. }
  destruct Hleft as [Hleft_range Hleft_bits].
  destruct Hright as [Hright_range Hright_bits].
  assert (Hleft_full : 0 <= left <= full).
  { rewrite Hfull, Z.shiftl_1_l. lia. }
  assert (Hright_full : 0 <= right <= full).
  { rewrite Hfull, Z.shiftl_1_l. lia. }
  destruct (Hrepresent left Hleft_range) as
    [[_ Habsent] | (left_row & Hleft_row & Hleft_rep & Hleft_prefix)].
  - apply (Habsent i).
    + unfold PairAtLeast in Hpair. rewrite Hprocessed. tauto.
    + split; assumption.
  - destruct (Hrepresent right Hright_range) as
      [[_ Habsent] | (right_row & Hright_row & Hright_rep & Hright_prefix)].
    + apply (Habsent j).
      * unfold PairAtLeast in Hpair. rewrite Hprocessed. tauto.
      * split; assumption.
    + specialize (Hnocover left right Hleft_full Hright_full ltac:(lia)
        ltac:(rewrite Hleft_rep; lia) ltac:(rewrite Hright_rep; lia)).
      contradiction.
Qed.
Lemma quot_nonnegative__solver_semantics :
  forall a b, 0 <= a -> 0 <= b -> 0 <= a ÷ b.
Proof. intros. apply Z_quot_pos; auto. Qed.
Lemma half_positive__solver_semantics :
  forall a, 2 <= a -> 1 <= a ÷ 2.
Proof. intros. apply Zquot_le_lower_bound; lia. Qed.
Lemma half_less_than_input__solver_semantics :
  forall a, 0 < a -> a ÷ 2 < a.
Proof. intros. apply Z_quot_lt; lia. Qed.
Lemma Znth_concat_uniform__solver_semantics :
  forall (rows : list (list Z)) m (d : list Z) i j,
    0 <= i < Zlength rows ->
    (forall r, 0 <= r < Zlength rows -> Zlength (Znth r rows d) = m) ->
    0 <= j < m ->
    Znth (i * m + j) (concat rows) 0 = Znth j (Znth i rows d) 0.
Proof.
  induction rows as [|row rows IH]; intros m d i j Hi Hlen Hj.
  - rewrite Zlength_nil in Hi. lia.
  - assert (Hrow : Zlength row = m).
    { specialize (Hlen 0). rewrite Znth0_cons in Hlen. apply Hlen.
      rewrite Zlength_cons in Hi |- *. lia. }
    destruct (Z.eq_dec i 0) as [-> | Hine].
    + simpl concat. rewrite Znth0_cons.
      rewrite app_Znth1; [reflexivity |]. rewrite Hrow. lia.
    + simpl concat. rewrite app_Znth2 by (rewrite Hrow; nia).
      replace (i * m + j - Zlength row) with ((i - 1) * m + j)
        by (rewrite Hrow; ring).
      rewrite Znth_cons by lia.
      apply IH.
      * rewrite Zlength_cons in Hi. lia.
      * intros r Hr. specialize (Hlen (r + 1)).
        rewrite Znth_cons in Hlen by lia.
        replace (r + 1 - 1) with r in Hlen by lia. apply Hlen.
        rewrite Zlength_cons. lia.
      * exact Hj.
Qed.
Lemma matrix_entries_bounded_from_flat__solver_semantics :
  forall rows n m (d : list Z),
    Pre rows ->
    0 < n ->
    n = Zlength rows ->
    m = Zlength (Znth 0 rows d) ->
    (forall q, 0 <= q < n * m ->
       0 <= Znth q (concat rows) 0 <= 1000000000) ->
    MatrixEntriesBounded rows.
Proof.
  intros rows n m d Hpre Hn Hrows Hm Hflat.
  destruct Hpre as [width [Hwidth Hrow_lengths]].
  assert (Hlen : forall r, 0 <= r < Zlength rows ->
      Zlength (Znth r rows d) = width).
  { intros r Hr.
    exact ((proj1 (Forall_Znth _ d rows)) Hrow_lengths r Hr). }
  assert (Hrow0 : Zlength (Znth 0 rows d) = width).
  { apply Hlen. lia. }
  assert (Hmwidth : m = width) by lia.
  unfold MatrixEntriesBounded.
  apply (proj2 (Forall_Znth _ d rows)).
  intros r Hr.
  apply (proj2 (Forall_Znth _ 0 (Znth r rows d))).
  intros c Hc.
  assert (Hrowlen : Zlength (Znth r rows d) = width) by
    (apply Hlen; exact Hr).
  rewrite <- (Znth_concat_uniform__solver_semantics
    rows width d r c Hr Hlen ltac:(rewrite <- Hrowlen; exact Hc)).
  apply Hflat.
  split; nia.
Qed.
Lemma matrix_entry_bounds__solver_semantics :
  forall rows r c,
    MatrixEntriesBounded rows ->
    0 <= r < Zlength rows ->
    0 <= c < Zlength (Znth r rows []) ->
    0 <= Znth c (Znth r rows []) 0 <= 1000000000.
Proof.
  intros rows r c Hentries Hr Hc.
  pose proof ((proj1 (Forall_Znth _ [] rows)) Hentries r Hr) as Hrow.
  exact ((proj1 (Forall_Znth _ 0 (Znth r rows []))) Hrow c Hc).
Qed.
Lemma combined_entry_bounds__solver_semantics :
  forall rows i j c,
    Pre rows ->
    MatrixEntriesBounded rows ->
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    0 <= c < Zlength (Znth i rows []) ->
    0 <= CombinedEntry rows i j c <= 1000000000.
Proof.
  intros rows i j c Hpre Hentries Hi Hj Hc.
  destruct Hpre as [m [Hm Hwidth]].
  assert (Hpre : Pre rows).
  { exists m. split; assumption. }
  assert (Hwi : Zlength (Znth i rows []) = m).
  { exact ((proj1 (Forall_Znth _ [] rows)) Hwidth i Hi). }
  assert (Hwj : Zlength (Znth j rows []) = m).
  { exact ((proj1 (Forall_Znth _ [] rows)) Hwidth j Hj). }
  assert (Hcj : 0 <= c < Zlength (Znth j rows [])) by lia.
  assert (Hai : 0 <= Znth c (Znth i rows []) 0 <= 1000000000).
  { eapply matrix_entry_bounds__solver_semantics; eauto. }
  assert (Haj : 0 <= Znth c (Znth j rows []) 0 <= 1000000000).
  { eapply matrix_entry_bounds__solver_semantics; eauto. }
  unfold CombinedEntry.
  split.
  - eapply Z.le_trans; [exact (proj1 Hai) | apply Z.le_max_l].
  - apply Z.max_lub; lia.
Qed.
Lemma pair_score_bounds__solver_semantics :
  forall rows i j score,
    Pre rows -> MatrixEntriesBounded rows -> PairScore rows i j score ->
    0 <= score <= 1000000000.
Proof.
  intros rows i j score Hpre Hentries [Hi [Hj Hscore]].
  destruct Hscore as [v [[[c [Hc Hv]] Hleast] Hid]].
  unfold id in Hid; subst v.
  subst score.
  eapply combined_entry_bounds__solver_semantics; eauto.
Qed.
Lemma pair_at_least_score_lower_bound__solver_semantics :
  forall rows threshold i j,
    Pre rows -> MatrixEntriesBounded rows ->
    PairAtLeast rows threshold i j ->
    exists score, PairScore rows i j score /\ threshold <= score.
Proof.
  intros rows threshold i j Hpre Hentries Hatleast.
  destruct Hatleast as [Hi [Hj Hthreshold]].
  destruct Hpre as [m [Hm Hwidth]].
  assert (Hpre : Pre rows).
  { exists m. split; assumption. }
  assert (Hw0 : Zlength (Znth 0 rows []) = m).
  { exact ((proj1 (Forall_Znth _ [] rows)) Hwidth 0 ltac:(lia)). }
  assert (Hwi : Zlength (Znth i rows []) = m).
  { exact ((proj1 (Forall_Znth _ [] rows)) Hwidth i Hi). }
  set (Q := fun v : Z =>
    exists c, 0 <= c < Zlength (Znth i rows []) /\
      v = CombinedEntry rows i j c).
  assert (HQexists : exists v, 0 <= v <= 1000000000 /\ Q v).
  { exists (CombinedEntry rows i j 0).
    split.
    - eapply combined_entry_bounds__solver_semantics; eauto; lia.
    - exists 0. split; [lia | reflexivity]. }
  destruct (min_n_in_range Q 1000000000 ltac:(lia) HQexists)
    as [score [HQscore [[Hscore0 Hscore1] Hleast]]].
  exists score. split.
  - unfold PairScore. split; [exact Hi |]. split; [exact Hj |].
    unfold min_value_of_subset.
    exists score. split.
    + split; [exact HQscore |].
      intros v Hv. apply Hleast; auto.
      destruct Hv as [c [Hc ->]].
      eapply combined_entry_bounds__solver_semantics; eauto.
    + reflexivity.
  - destruct HQscore as [c [Hc ->]].
    apply Hthreshold.
    lia.
Qed.
Lemma pair_score_implies_pair_at_least__solver_semantics :
  forall rows threshold i j score,
    Pre rows -> PairScore rows i j score -> threshold <= score ->
    PairAtLeast rows threshold i j.
Proof.
  intros rows threshold i j score Hpre [Hi [Hj Hscore]] Hthreshold.
  destruct Hpre as [m [Hm Hwidth]].
  assert (Hpre : Pre rows).
  { exists m. split; assumption. }
  assert (Hw0 : Zlength (Znth 0 rows []) = m).
  { exact ((proj1 (Forall_Znth _ [] rows)) Hwidth 0 ltac:(lia)). }
  assert (Hwi : Zlength (Znth i rows []) = m).
  { exact ((proj1 (Forall_Znth _ [] rows)) Hwidth i Hi). }
  destruct Hscore as [v [[Hv Hminimum] Hid]].
  unfold id in Hid; subst v.
  unfold PairAtLeast. split; [exact Hi |]. split; [exact Hj |].
  intros c Hc.
  eapply Z.le_trans; [exact Hthreshold |].
  apply Hminimum.
  exists c. split; [lia | reflexivity].
Qed.
Lemma pair_at_least_zero__solver_semantics :
  forall rows,
    Pre rows -> MatrixEntriesBounded rows ->
    0 < Zlength rows -> PairAtLeast rows 0 0 0.
Proof.
  intros rows Hpre Hentries Hrows.
  destruct Hpre as [m [Hm Hwidth]].
  assert (Hpre : Pre rows).
  { exists m. split; assumption. }
  assert (Hw0 : Zlength (Znth 0 rows []) = m).
  { exact ((proj1 (Forall_Znth _ [] rows)) Hwidth 0 ltac:(lia)). }
  unfold PairAtLeast. split; [lia |]. split; [lia |].
  intros c Hc.
  pose proof (combined_entry_bounds__solver_semantics
    rows 0 0 c Hpre Hentries ltac:(lia) ltac:(lia) ltac:(lia)).
  lia.
Qed.
Lemma optimal_pair_score_exists__solver_semantics :
  forall rows,
    Pre rows -> MatrixEntriesBounded rows -> 0 < Zlength rows ->
    exists best, OptimalPairScore rows best.
Proof.
  intros rows Hpre Hentries Hrows.
  pose proof (pair_at_least_zero__solver_semantics
    rows Hpre Hentries Hrows) as Hpair0.
  destruct (pair_at_least_score_lower_bound__solver_semantics
    rows 0 0 0 Hpre Hentries Hpair0) as [score0 [Hscore0 Hnonneg]].
  set (Q := fun score : Z => exists i j, PairScore rows i j score).
  assert (HQexists : exists score, 0 <= score <= 1000000000 /\ Q score).
  { exists score0. split.
    - eapply pair_score_bounds__solver_semantics; eauto.
    - exists 0, 0. exact Hscore0. }
  destruct (max_n_in_range Q 1000000000 ltac:(lia) HQexists)
    as [best [HQbest [[Hbest0 Hbest1] Hgreatest]]].
  exists best.
  unfold OptimalPairScore, max_value_of_subset.
  exists best. split.
  - split; [exact HQbest |].
    intros score Hscore.
    apply Hgreatest; auto.
    destruct Hscore as [i [j Hscore]].
    eapply pair_score_bounds__solver_semantics; eauto.
  - reflexivity.
Qed.
Lemma optimal_pair_score_bounds__solver_semantics :
  forall rows best,
    Pre rows -> MatrixEntriesBounded rows -> OptimalPairScore rows best ->
    0 <= best <= 1000000000.
Proof.
  intros rows best Hpre Hentries [score [[[i [j Hpair]] Hgreatest] Hid]].
  unfold id in Hid; subst score.
  eapply pair_score_bounds__solver_semantics; eauto.
Qed.
Lemma feasible_threshold_optimal_bound__solver_semantics :
  forall rows best threshold,
    Pre rows -> MatrixEntriesBounded rows -> OptimalPairScore rows best ->
    (FeasibleAtThreshold rows threshold -> threshold <= best) /\
    (~ FeasibleAtThreshold rows threshold -> best < threshold).
Proof.
  intros rows best threshold Hpre Hentries Hoptimal.
  split.
  - intros [i [j Hatleast]].
    destruct (pair_at_least_score_lower_bound__solver_semantics
      rows threshold i j Hpre Hentries Hatleast) as [score [Hscore Hlower]].
    destruct Hoptimal as [w [[[wi [wj Hwscore]] Hgreatest] Hid]].
    unfold id in Hid; subst w.
    specialize (Hgreatest score ltac:(exists i, j; exact Hscore)).
    lia.
  - intros Hnot.
    destruct Hoptimal as [w [[[i [j Hscore]] Hgreatest] Hid]].
    unfold id in Hid; subst w.
    destruct (Z_lt_le_dec best threshold); auto.
    exfalso. apply Hnot.
    exists i, j.
    eapply pair_score_implies_pair_at_least__solver_semantics; eauto.
Qed.
Lemma optimal_pair_to_spec__solver_semantics :
  forall rows best i j,
    Pre rows -> MatrixEntriesBounded rows ->
    OptimalPairScore rows best -> PairAtLeast rows best i j ->
    Spec rows (i + 1, j + 1).
Proof.
  intros rows best i j Hpre Hentries Hoptimal Hatleast.
  destruct (pair_at_least_score_lower_bound__solver_semantics
    rows best i j Hpre Hentries Hatleast) as [score [Hscore Hbestscore]].
  assert (Hscorebest : score <= best).
  { destruct Hoptimal as [w [[Hw Hgreatest] Hid]].
    unfold id in Hid; subst w.
    apply Hgreatest. exists i, j. exact Hscore. }
  assert (score = best) by lia. subst score.
  exists best. split.
  - cbn. replace (i + 1 - 1) with i by lia.
    replace (j + 1 - 1) with j by lia.
    exact Hscore.
  - exact Hoptimal.
Qed.
