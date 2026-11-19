Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib.
From MonadLib Require Export MonadLib.

From SimpleC.EE.stdlib.musl.monad Require Import two_way_rel_lib.
From SimpleC.EE.stdlib.musl.monad Require Import two_way_list_lemmas.
From SimpleC.EE.stdlib.musl.monad Require Import two_way_critical_factorization_theorem.
From SimpleC.EE.stdlib.musl.monad Require Import two_way_match.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope monad.

(* The original theorem omitted the byte-range premise and is false over the
   unrestricted list-Z model. Concrete counterexample: `patn = [1]`,
   `text = [300]`, and the correctly built 256-entry table. Lookup at index
   300 returns the default shift 0 although the last character does not match.
   The pointwise range premise below is the minimal semantic repair and follows
   from the `UCharArray.full` byte-range invariant at the C/refinement boundary.

   This theorem is the bad-character table correctness fact for the
   long-needle preprocessing table. It says that a table built from the whole
   pattern is sound for the abstract bad-character skip used by the Monad
   refinement. This is an algorithm-correctness fact, not a separation-logic
   VC fact, and should be proved later from the two-way long-needle
   bad-character shift argument.

   Affected witness: two_way_long_needle_entail_wit_7.
   2026-08-31 semantic round: original statement refuted in audit round 1;
   strengthened statement proved in proof round 1.

   2026-07-10 progress note: symbolic execution has been refreshed several
   times after long-needle annotation repairs. The generated refinement proof
   currently relies on this placeholder for table soundness, while the manual
   proof work has moved past the initial table-build witnesses. This fact still
   needs a real proof from `shift_table_build_prefix patn (Zlength patn) table`
   to the abstract `shift_table_sound` predicate. Future work should check the
   `last_occ_before` cases, the zero-shift/match-cond branch, and the positive
   valid-skip branch against the two-way bad-character argument.
 *)
Theorem shift_table_build_prefix_sound :
  forall (text patn table : list Z),
    0 < Zlength patn ->
    (forall i, 0 <= i < Zlength text -> 0 <= Znth i text 0 < 256) ->
    shift_table_build_prefix patn (Zlength patn) table ->
    shift_table_sound text patn table.
Proof.
  intros text patn table Hpatn Htext_range Hbuild.
  unfold shift_table_sound.
  split; [exact Hbuild |].
  intros pos shift [Hpos Hwindow] Hshift.
  destruct Hbuild as [_ [_ Htable]].
  set (m := Zlength patn) in *.
  set (c := Znth (pos + m - 1) text 0) in *.
  assert (Hc : 0 <= c < 256).
  { apply Htext_range. lia. }
  specialize (Htable c Hc).
  destruct Htable as [[idx [[Hidx [Hidx_char Hlast]] Htable]] |
                       [Habsent Htable]].
  - rewrite Htable in Hshift.
    subst shift.
    destruct (Z.eq_dec idx (m - 1)) as [Heq | Hneq].
    + left. split; [lia |].
      unfold match_cond.
      subst idx.
      rewrite Hidx_char.
      unfold c.
      f_equal. lia.
    + right.
      unfold valid_skip.
      repeat split; try lia.
      intros k Hk.
      unfold no_match_at.
      intro Hmatch.
      set (q := pos + m - 1 - k).
      assert (Hq : idx < q < m) by (unfold q; lia).
      specialize (Hlast q Hq).
      apply Hlast.
      assert (Hz := f_equal (fun xs => Znth q xs 0) Hmatch).
      change (Znth q (sublist k (k + m) text) 0 = Znth q patn 0) in Hz.
      rewrite Znth_sublist in Hz; try (unfold q; lia).
      rewrite <- Hz.
      unfold q, c.
      f_equal. lia.
  - rewrite Htable in Hshift.
    subst shift.
    right.
    unfold valid_skip.
    repeat split; try lia.
    intros k Hk.
    unfold no_match_at.
    intro Hmatch.
    set (q := pos + m - 1 - k).
    assert (Hq : 0 <= q < m) by (unfold q; lia).
    specialize (Habsent q Hq).
    apply Habsent.
    assert (Hz := f_equal (fun xs => Znth q xs 0) Hmatch).
    change (Znth q (sublist k (k + m) text) 0 = Znth q patn 0) in Hz.
    rewrite Znth_sublist in Hz; try (unfold q; lia).
    rewrite <- Hz.
    unfold q, c.
    f_equal. lia.
Qed.

(* This theorem is the periodic long-needle skip fact used when the
   periodic matcher has nonzero memory and the bad-character shift is smaller
   than the period. The generated VC only needs the abstract consequence
   `valid_skip text patn j (Zlength patn - mp)`, while the proof belongs to
   the deferred periodic long-needle correctness development.

   Affected witness: two_way_long_needle_entail_wit_10_1.
   2026-08-31 semantic round: bounded audit found no counterexample; proof
   round 1 established the early-shift region, and proof round 2 closed the
   remaining region by applying table soundness at a hypothetical occurrence.

   2026-07-10 progress note: `wit_10_1` was repaired in scratch and then
   integrated into the manual proof. The proof uses this placeholder with
   `suffix` instantiated to 0 and discharges range/length side conditions from
   `UCharArray.full_Zlength`. The byte-range premise is discharged at the C
   boundary by `UCharArray_full_all_Znth_range`:
   it must justify that the periodic-memory skip `Zlength patn - mp` is a valid
   skip when memory is nonzero and the bad-character shift is positive but less
   than `mp`. Future work should check the relationship between `memory`,
   `suffix`, `mp`, and the periodic split proof; in particular it should prove
   that every skipped candidate satisfies `no_match_at`.
 *)
Theorem long_needle_periodic_memory_skip_valid :
  forall (text patn : list Z) (j suffix mp memory : Z) (table : list Z),
    0 < Zlength patn ->
    0 <= j ->
    j + Zlength patn <= Zlength text ->
    0 < mp <= Zlength patn ->
    0 <= suffix < Zlength patn ->
    mp + suffix <= Zlength patn ->
    0 <= memory < Zlength patn ->
    repetitive_split patn suffix mp ->
    periodic_memory_match text patn j mp memory ->
    memory <> 0 ->
    shift_table_sound text patn table ->
    0 < Znth (Znth (j + Zlength patn - 1) text 0) table 0 < mp ->
    valid_skip text patn j (Zlength patn - mp).
Proof.
  intros text patn j suffix mp memory table
    Hpatn Hj Hwindow Hmp Hsuffix Hsuffix_mp Hmemory Hrep
    Hperiodic Hmemory_nz Hsound Hshift_range.
  destruct Hperiodic as [Hperiod [[Hmemory_zero | Hmemory_eq] Hprefix]].
  - contradiction.
  - subst memory.
    destruct Hperiod as [Hmp_pos Hperiod].
    destruct Hsound as [Hbuild Hsound].
    destruct Hshift_range as [Hshift_pos Hshift_lt].
    set (m := Zlength patn) in *.
    set (n := m - mp) in *.
    set (shift := Znth (Znth (j + m - 1) text 0) table 0) in *.
    assert (Hn_pos : 0 < n) by (unfold n in *; lia).
    assert (Hskip : valid_skip text patn j shift).
    { specialize (Hsound j shift ltac:(split; lia) eq_refl).
      destruct Hsound as [[Hzero _] | Hvalid]; [lia | exact Hvalid]. }
    unfold valid_skip in *.
    destruct Hskip as [Hskip_pos [Hskip_bound Hskip_no_match]].
    repeat split; try lia.
    intros k Hk.
    destruct (Z_lt_ge_dec k (j + shift)) as [Hearly | Hlate].
    { apply Hskip_no_match. lia. }
    unfold no_match_at.
    intro Hmatch.
    assert (Hk_nonneg : 0 <= k) by lia.
    assert (Hk_fit : k + m <= Zlength text).
    { destruct (Z_le_gt_dec (k + m) (Zlength text)) as [Hfit | Hover];
        [exact Hfit |].
      rewrite Zsublist_overflow_iff_Zsublist_Zlength in Hmatch; try lia.
      apply (f_equal (@Zlength Z)) in Hmatch.
      rewrite Zlength_sublist in Hmatch; try lia. }
    set (d := k - j).
    assert (Hd : 0 <= d < n) by (unfold d; lia).
    assert (Hprefix_char :
      Znth (n - 1) patn 0 = Znth (j + n - 1) text 0).
    { apply (f_equal (fun xs => Znth (n - 1) xs 0)) in Hprefix.
      change
        (Znth (n - 1) (sublist 0 n patn) 0 =
         Znth (n - 1) (sublist j (j + n) text) 0) in Hprefix.
      rewrite Znth_sublist0 in Hprefix by lia.
      rewrite Znth_sublist in Hprefix by lia.
      replace (n - 1 + 0) with (n - 1) in Hprefix by lia.
      replace (n - 1 + j) with (j + n - 1) in Hprefix by lia.
      exact Hprefix. }
    assert (Hcandidate_prefix :
      Znth (j + n - 1) text 0 = Znth (n - 1 - d) patn 0).
    { apply (f_equal (fun xs => Znth (n - 1 - d) xs 0)) in Hmatch.
      change
        (Znth (n - 1 - d) (sublist k (k + m) text) 0 =
         Znth (n - 1 - d) patn 0) in Hmatch.
      rewrite Znth_sublist in Hmatch; try lia.
      replace (n - 1 - d + k) with (j + n - 1) in Hmatch
        by (unfold d; lia).
      exact Hmatch. }
    assert (Hcandidate_last :
      Znth (j + m - 1) text 0 = Znth (m - 1 - d) patn 0).
    { apply (f_equal (fun xs => Znth (m - 1 - d) xs 0)) in Hmatch.
      change
        (Znth (m - 1 - d) (sublist k (k + m) text) 0 =
         Znth (m - 1 - d) patn 0) in Hmatch.
      rewrite Znth_sublist in Hmatch; try lia.
      replace (m - 1 - d + k) with (j + m - 1) in Hmatch
        by (unfold d; lia).
      exact Hmatch. }
    assert (Hperiod_hi : Znth (n - 1) patn 0 = Znth (m - 1) patn 0).
    { specialize (Hperiod (n - 1) ltac:(lia) ltac:(unfold n; lia)).
      replace (n - 1 + mp) with (m - 1) in Hperiod by (unfold n; lia).
      exact Hperiod. }
    assert (Hperiod_lo :
      Znth (n - 1 - d) patn 0 = Znth (m - 1 - d) patn 0).
    { specialize (Hperiod (n - 1 - d) ltac:(lia)
        ltac:(unfold n; lia)).
      replace (n - 1 - d + mp) with (m - 1 - d) in Hperiod
        by (unfold n; lia).
      exact Hperiod. }
    assert (Hlast_match :
      Znth (j + m - 1) text 0 = Znth (m - 1) patn 0).
    { rewrite Hcandidate_last, <- Hperiod_lo, <- Hcandidate_prefix,
        <- Hprefix_char, Hperiod_hi.
      reflexivity. }
    assert (Hcandidate_window_last :
      Znth (k + m - 1) text 0 = Znth (m - 1) patn 0).
    { apply (f_equal (fun xs => Znth (m - 1) xs 0)) in Hmatch.
      change
        (Znth (m - 1) (sublist k (k + m) text) 0 =
         Znth (m - 1) patn 0) in Hmatch.
      rewrite Znth_sublist in Hmatch; try lia.
      replace (m - 1 + k) with (k + m - 1) in Hmatch by lia.
      exact Hmatch. }
    assert (Hsame_lookup :
      Znth (Znth (k + m - 1) text 0) table 0 = shift).
    { unfold shift.
      rewrite Hcandidate_window_last, Hlast_match.
      reflexivity. }
    specialize (Hsound k shift ltac:(split; lia) (eq_sym Hsame_lookup)).
    destruct Hsound as [[Hzero _] | [_ [_ Hno_match]]].
    + lia.
    + apply (Hno_match k ltac:(lia)).
      exact Hmatch.
Qed.

Lemma no_occur_valid_skip :
  forall (text patn : list Z) (pos n : Z),
    no_occur text patn pos ->
    valid_skip text patn pos n ->
    no_occur text patn (pos + n).
Proof.
  intros text patn pos n Hno [Hn_pos [Hbound Hskip]].
  unfold no_occur in *.
  intros k Hk.
  destruct (Z_lt_ge_dec k pos) as [Hlt | Hge].
  - apply Hno. lia.
  - apply Hskip. lia.
Qed.

Lemma no_occur_overflow :
  forall (text patn : list Z) (pos : Z),
    0 <= pos ->
    no_occur text patn pos ->
    pos + Zlength patn > Zlength text ->
    no_occur text patn (Zlength text).
Proof.
  intros text patn pos Hpos Hno Hover.
  unfold no_occur in *.
  intros k Hk Hmatch.
  destruct (Z_lt_ge_dec k pos) as [Hlt | Hge].
  - exact (Hno k ltac:(lia) Hmatch).
  - assert (k + Zlength patn > Zlength text) by lia.
    rewrite Zsublist_overflow_iff_Zsublist_Zlength in Hmatch; try lia.
    apply (f_equal (@Zlength Z)) in Hmatch.
    rewrite Zlength_sublist in Hmatch; try lia.
Qed.

Lemma match_right_last_prop :
  forall (text patn : list Z) (l p pos : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    match_inv text patn pos ->
    pos + Zlength patn <= Zlength text ->
    Hoare
      (fun _ => True)
      (match_right_last text patn pos l)
      (fun j _ =>
         l <= j <= Zlength patn - 1 /\
         sublist l j patn = sublist (pos + l) (pos + j) text /\
         (j >= Zlength patn - 1 \/
          Znth j patn 0 <> Znth (pos + j) text 0)).
Proof.
  intros text patn l p pos Hne Hcf Hinv Hwindow.
  destruct (critical_factorization_bounds patn Hne l p Hcf) as [Hl _].
  destruct Hcf as [[mp [Hmp [Hlmp [[Hp _] Hlocal]]]]].
  pose proof (minimal_period_le_Zlength 0 patn mp Hne Hmp) as Hmp_len.
  unfold match_right_last.
  eapply Hoare_conseq with
    (P2 := fun _ =>
       match_right_inv text patn l pos l /\ l <= Zlength patn - 1).
  - intros st _. split; [constructor; [lia |] | lia].
    repeat rewrite Zsublist_nil; try lia. reflexivity.
  - intros j st Hpost. exact Hpost.
  - eapply (@Hoare_repeat_break'
              unit Z Z
              (match_right_last_f text patn pos)
              (fun j _ =>
                 match_right_inv text patn l pos j /\
                 j <= Zlength patn - 1)
              (fun j _ =>
                 l <= j <= Zlength patn - 1 /\
                 sublist l j patn = sublist (pos + l) (pos + j) text /\
                 (j >= Zlength patn - 1 \/
                  Znth j patn 0 <> Znth (pos + j) text 0))).
    + intros j.
      unfold match_right_last_f.
      hoare_auto.
      destruct H as [Hrange Hcond].
      destruct H0 as [[Hjrange Hpartial] Hj_upper].
      split; [constructor; [lia |] | lia].
      unfold match_cond in Hcond.
      replace (pos + (j + 1)) with (pos + j + 1) by lia.
      eapply (Zsublist_hi_plus_1 0 patn text l j (pos + l) (pos + j));
        try lia; auto.
      destruct Hinv as [Hpos _].
      lia.
    + intros j.
      unfold match_right_last_f.
      hoare_auto.
      destruct H0 as [[Hjrange Hpartial] Hj_upper].
      repeat split; try lia; auto.
Qed.

Lemma match_right_last_prop_from :
  forall (text patn : list Z) (l p pos start : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    match_inv text patn pos ->
    pos + Zlength patn <= Zlength text ->
    l <= start <= Zlength patn - 1 ->
    sublist l start patn = sublist (pos + l) (pos + start) text ->
    Hoare
      (fun _ => True)
      (match_right_last text patn pos start)
      (fun j _ =>
         l <= j <= Zlength patn - 1 /\
         sublist l j patn = sublist (pos + l) (pos + j) text /\
         (j >= Zlength patn - 1 \/
          Znth j patn 0 <> Znth (pos + j) text 0)).
Proof.
  intros text patn l p pos start Hne Hcf Hinv Hwindow Hstart Hpartial.
  destruct (critical_factorization_bounds patn Hne l p Hcf) as [Hl _].
  unfold match_right_last.
  eapply Hoare_conseq with
    (P2 := fun _ =>
       match_right_inv text patn l pos start /\
       start <= Zlength patn - 1).
  - intros st _. split.
    + constructor; [lia | exact Hpartial].
    + lia.
  - intros j st Hpost. exact Hpost.
  - eapply (@Hoare_repeat_break'
              unit Z Z
              (match_right_last_f text patn pos)
              (fun j _ =>
                 match_right_inv text patn l pos j /\
                 j <= Zlength patn - 1)
              (fun j _ =>
                 l <= j <= Zlength patn - 1 /\
                 sublist l j patn = sublist (pos + l) (pos + j) text /\
                 (j >= Zlength patn - 1 \/
                  Znth j patn 0 <> Znth (pos + j) text 0))).
    + intros j.
      unfold match_right_last_f.
      hoare_auto.
      destruct H as [Hrange Hcond].
      destruct H0 as [[Hjrange Hjpartial] Hj_upper].
      split; [constructor; [lia |] | lia].
      unfold match_cond in Hcond.
      replace (pos + (j + 1)) with (pos + j + 1) by lia.
      eapply (Zsublist_hi_plus_1 0 patn text l j (pos + l) (pos + j));
        try lia; auto.
      destruct Hinv as [Hpos _].
      lia.
    + intros j.
      unfold match_right_last_f.
      hoare_auto.
      destruct H0 as [[Hjrange Hjpartial] Hj_upper].
      repeat split; try lia; auto.
Qed.

Lemma match_right_last_to_standard :
  forall (text patn : list Z) (l pos j : Z),
    0 <= l ->
    0 <= pos ->
    pos + Zlength patn <= Zlength text ->
    match_cond text patn pos (Zlength patn - 1) ->
    (l <= j <= Zlength patn - 1 /\
     sublist l j patn = sublist (pos + l) (pos + j) text /\
     (j >= Zlength patn - 1 \/
      Znth j patn 0 <> Znth (pos + j) text 0)) ->
    (j = Zlength patn - 1 /\
     match_right_post text patn l pos (Zlength patn)) \/
    (j < Zlength patn - 1 /\ match_right_post text patn l pos j).
Proof.
  intros text patn l pos j Hl Hpos Hwindow Hlast
    [Hrange [Hpartial Hstop]].
  destruct (Z.eq_dec j (Zlength patn - 1)) as [Heq | Hneq].
  - left. split; [exact Heq |].
    subst j.
    constructor; [lia | | left; lia].
    unfold match_cond in Hlast.
    replace (pos + Zlength patn) with
      (pos + (Zlength patn - 1) + 1) at 1 by lia.
    replace (Zlength patn) with (Zlength patn - 1 + 1) at 1 by lia.
    eapply (Zsublist_hi_plus_1 0 patn text l (Zlength patn - 1)
      (pos + l) (pos + (Zlength patn - 1))); try lia; auto.
  - right. split; [lia |].
    constructor; try lia; auto.
Qed.

Lemma long_standard_matching_correct :
  forall (text patn : list Z) (l p pos : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    pos + Zlength patn <= Zlength text ->
    Hoare
      (fun _ => match_inv text patn pos /\
                match_cond text patn pos (Zlength patn - 1))
      (long_needle_match_from_right text patn l p pos l)
      (fun res _ =>
         match res with
         | by_continue pos' => match_inv text patn pos'
         | by_break out => match_post text patn out
         end).
Proof.
  intros text patn l p pos Hne Hcf Hwindow.
  assert (Hleft_prog : forall Hinv : match_inv text patn pos,
    Hoare
      (fun _ => match_right_post text patn l pos (Zlength patn))
      (long_needle_match_from_left text patn p pos 0 (l - 1))
      (fun res _ =>
         match res with
         | by_continue pos' => match_inv text patn pos'
         | by_break out => match_post text patn out
         end)).
  { intros Hinv.
    unfold long_needle_match_from_left.
    eapply Hoare_bind.
    - apply (match_left_prop_pre_keep text patn Hne l p pos); auto.
    - intros j.
      unfold long_needle_after_left.
      hoare_auto; simpl.
      + destruct H0 as [Hright' Hleft].
        apply (first_occur_break text patn Hne l p pos j); auto.
      + destruct H0 as [Hright' Hleft].
        apply (match_inv_continue_left text patn Hne l p pos j); auto. }
  unfold long_needle_match_from_right.
  eapply Hoare_bind with
    (Q := fun j _ =>
      match_inv text patn pos /\
      match_cond text patn pos (Zlength patn - 1) /\
      (l <= j <= Zlength patn - 1 /\
       sublist l j patn = sublist (pos + l) (pos + j) text /\
       (j >= Zlength patn - 1 \/
        Znth j patn 0 <> Znth (pos + j) text 0))).
  - unfold Hoare. split.
    + intros j st1 st2 [Hinv Hlast] Hnrm.
      split; [exact Hinv |].
      split; [exact Hlast |].
      pose proof (match_right_last_prop text patn l p pos Hne Hcf Hinv Hwindow)
        as Hr.
      unfold Hoare in Hr. destruct Hr as [Hr _].
      eapply Hr; eauto.
    + intros st [Hinv Hlast] Herr.
      pose proof (match_right_last_prop text patn l p pos Hne Hcf Hinv Hwindow)
        as Hr.
      unfold Hoare in Hr. destruct Hr as [_ Hr].
      eapply Hr; eauto.
  - intros r.
    unfold long_needle_after_right.
    hoare_auto.
    + unfold Hoare. split.
      * intros out st1 st2 [Hinv [Hlast Hright_last]] Hnrm.
        destruct (critical_factorization_bounds patn Hne l p Hcf) as [[Hl _] _].
        destruct (match_right_last_to_standard text patn l pos r Hl
          (match_inv_pos text patn pos Hinv) Hwindow Hlast Hright_last)
          as [[Hr Hright] | [Hr Hright]]; try lia.
        pose proof (Hleft_prog Hinv) as Hprog.
        unfold Hoare in Hprog. destruct Hprog as [Hprog _].
        eapply Hprog; eauto.
      * intros st [Hinv [Hlast Hright_last]] Herr.
        destruct (critical_factorization_bounds patn Hne l p Hcf) as [[Hl _] _].
        destruct (match_right_last_to_standard text patn l pos r Hl
          (match_inv_pos text patn pos Hinv) Hwindow Hlast Hright_last)
          as [[Hr Hright] | [Hr Hright]]; try lia.
        pose proof (Hleft_prog Hinv) as Hprog.
        unfold Hoare in Hprog. destruct Hprog as [_ Hprog].
        eapply Hprog; eauto.
    + destruct H0 as [Hinv [Hlast Hright_last]].
      destruct (critical_factorization_bounds patn Hne l p Hcf) as [[Hl _] _].
      destruct (match_right_last_to_standard text patn l pos r Hl
        (match_inv_pos text patn pos Hinv) Hwindow Hlast Hright_last)
        as [[Hr Hright] | [Hr Hright]]; try lia.
      simpl.
      apply (match_inv_continue_right text patn l p pos r); auto.
      lia.
Qed.

Lemma long_standard_body_correct :
  forall (text patn : list Z) (l p pos : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    Hoare
      (fun _ => match_inv text patn pos)
      (long_needle_match_loop_body text patn l p pos)
      (fun res _ =>
         match res with
         | by_continue pos' => match_inv text patn pos'
         | by_break out => match_post text patn out
         end).
Proof.
  intros text patn l p pos Hne Hcf.
  unfold long_needle_match_loop_body.
  hoare_auto; simpl.
  - eapply Hoare_bind.
    + apply Hoare_any.
    + intros n.
      hoare_auto; simpl.
      destruct H1 as [Hpos Hno].
      assert (Hn : 0 < n) by (destruct H0 as [Hn _]; exact Hn).
      constructor; [lia |].
      eapply no_occur_valid_skip; eauto.
  - eapply Hoare_conseq with
      (P2 := fun _ =>
         match_inv text patn pos /\
         match_cond text patn pos (Zlength patn - 1)).
    + intros st Hinv. split; [exact Hinv | exact H0].
    + intros res st Hpost. exact Hpost.
    + eapply long_standard_matching_correct; eauto.
  - destruct H0 as [Hpos Hno].
    unfold match_post.
    eapply no_occur_overflow; eauto.
Qed.

Lemma long_standard_body_continue :
  forall (text patn : list Z) (l p pos : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    Hoare
      (fun _ => match_inv text patn pos)
      (long_needle_match_loop_body text patn l p pos)
      (fun res _ =>
         match res with
         | by_continue pos' => match_inv text patn pos'
         | by_break _ => True
         end).
Proof.
  intros text patn l p pos Hne Hcf.
  eapply Hoare_conseq with
    (P2 := fun _ => match_inv text patn pos)
    (Q2 := fun res _ =>
       match res with
       | by_continue pos' => match_inv text patn pos'
       | by_break out => match_post text patn out
       end).
  - intros; eassumption.
  - intros [pos' | out] st Hpost; simpl in *; auto.
  - apply long_standard_body_correct; auto.
Qed.

Lemma long_standard_body_break :
  forall (text patn : list Z) (l p pos : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    Hoare
      (fun _ => match_inv text patn pos)
      (long_needle_match_loop_body text patn l p pos)
      (fun res _ =>
         match res with
         | by_continue _ => True
         | by_break out => match_post text patn out
         end).
Proof.
  intros text patn l p pos Hne Hcf.
  eapply Hoare_conseq with
    (P2 := fun _ => match_inv text patn pos)
    (Q2 := fun res _ =>
       match res with
       | by_continue pos' => match_inv text patn pos'
       | by_break out => match_post text patn out
       end).
  - intros; eassumption.
  - intros [pos' | out] st Hpost; simpl in *; auto.
  - apply long_standard_body_correct; auto.
Qed.

Lemma long_needle_match_from_correct :
  forall (text patn : list Z) (l p pos : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    match_inv text patn pos ->
    Hoare
      (fun _ => True)
      (long_needle_match_from text patn l p pos)
      (fun out _ => match_post text patn out).
Proof.
  intros text patn l p pos Hne Hcf Hinv.
  unfold long_needle_match_from.
  eapply Hoare_conseq with
    (P2 := fun _ => match_inv text patn pos).
  - intros st _. exact Hinv.
  - intros out st Hpost. exact Hpost.
  - eapply (@Hoare_repeat_break'
              unit Z (option Z)
              (long_needle_match_loop_body text patn l p)
              (fun pos _ => match_inv text patn pos)
              (fun out _ => match_post text patn out)).
    + intros pos'.
      eapply Hoare_bind.
      * apply long_standard_body_continue; auto.
      * intros [pos'' | out]; simpl; hoare_auto.
    + intros pos'.
      eapply Hoare_bind.
      * apply long_standard_body_break; auto.
      * intros [pos'' | out]; simpl; hoare_auto.
Qed.

Lemma long_periodic_matching_correct :
  forall (text patn : list Z) (l p pos memory : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    repetitive_split patn l p ->
    pos + Zlength patn <= Zlength text ->
    Hoare
      (fun _ =>
         periodic_match_inv text patn l p pos memory /\
         (memory = 0 \/ memory = Zlength patn - p) /\
         match_cond text patn pos (Zlength patn - 1))
      (long_needle_match_periodic_from_right
        text patn l p pos memory (Z.max l memory))
      (fun res _ =>
         match res with
         | by_continue (pos', memory') =>
             periodic_match_inv text patn l p pos' memory' /\
             (memory' = 0 \/ memory' = Zlength patn - p)
         | by_break out => match_post text patn out
         end).
Proof.
  intros text patn l p pos memory Hne Hcf Hrep Hwindow.
  assert (Hleft_prog : forall Hpinv :
      periodic_match_inv text patn l p pos memory,
    Hoare
      (fun _ => match_right_post text patn l pos (Zlength patn))
      (match_periodic_from_left text patn l p pos memory (l - 1))
      (fun res _ =>
         match res with
         | by_continue (pos', memory') =>
             periodic_match_inv text patn l p pos' memory' /\
             (memory' = 0 \/ memory' = Zlength patn - p)
         | by_break out => match_post text patn out
         end)).
  { intros Hpinv.
    pose proof Hpinv as Hpinv0.
    destruct Hpinv as [Hbase [Hmemlo Hmemhi] Hprefix].
    unfold match_periodic_from_left.
    eapply Hoare_bind.
    - apply (match_left_prop_from_pre_keep text patn Hne l p pos memory);
        auto.
    - intros j'.
      unfold match_periodic_after_left.
      hoare_auto; simpl.
      + destruct H0 as [Hright' Hleft].
        apply (periodic_first_occur_break text patn Hne
          l p pos memory j'); auto.
      + destruct H0 as [Hright' Hleft].
        split.
        * apply (periodic_inv_continue_left text patn Hne
            l p pos memory j'); auto.
        * right. reflexivity. }
  unfold long_needle_match_periodic_from_right.
  eapply Hoare_bind with
    (Q := fun j _ =>
      periodic_match_inv text patn l p pos memory /\
      (memory = 0 \/ memory = Zlength patn - p) /\
      match_cond text patn pos (Zlength patn - 1) /\
      (l <= j <= Zlength patn - 1 /\
       sublist l j patn = sublist (pos + l) (pos + j) text /\
       (j >= Zlength patn - 1 \/
        Znth j patn 0 <> Znth (pos + j) text 0))).
  - unfold Hoare. split.
    + intros j st1 st2 [Hpinv [Hshape Hlast]] Hnrm.
      pose proof (periodic_right_start_partial text patn Hne l p pos memory
        Hcf Hpinv) as [[Hstart_lo Hstart_hi] Hpartial].
      destruct (critical_factorization_bounds patn Hne l p Hcf)
        as [[Hl_lo Hl_hi] Hp_pos].
      assert (Hstart_strict : Z.max l memory <= Zlength patn - 1).
      { destruct Hcf as [[mp [Hmp [Hlmp [[Hp_le _] Hlocal]]]]].
        pose proof (minimal_period_le_Zlength 0 patn mp Hne Hmp).
        destruct Hshape; subst memory; lia. }
      split; [exact Hpinv |].
      split; [exact Hshape |].
      split; [exact Hlast |].
      pose proof (match_right_last_prop_from text patn l p pos
        (Z.max l memory) Hne Hcf
        (periodic_match_base text patn l p pos memory Hpinv)
        Hwindow ltac:(lia) Hpartial) as Hr.
      unfold Hoare in Hr. destruct Hr as [Hr _]. eapply Hr; eauto.
    + intros st [Hpinv [Hshape Hlast]] Herr.
      pose proof (periodic_right_start_partial text patn Hne l p pos memory
        Hcf Hpinv) as [[Hstart_lo Hstart_hi] Hpartial].
      destruct (critical_factorization_bounds patn Hne l p Hcf)
        as [[Hl_lo Hl_hi] Hp_pos].
      assert (Hstart_strict : Z.max l memory <= Zlength patn - 1).
      { destruct Hcf as [[mp [Hmp [Hlmp [[Hp_le _] Hlocal]]]]].
        pose proof (minimal_period_le_Zlength 0 patn mp Hne Hmp).
        destruct Hshape; subst memory; lia. }
      pose proof (match_right_last_prop_from text patn l p pos
        (Z.max l memory) Hne Hcf
        (periodic_match_base text patn l p pos memory Hpinv)
        Hwindow ltac:(lia) Hpartial) as Hr.
      unfold Hoare in Hr. destruct Hr as [_ Hr]. eapply Hr; eauto.
  - intros r.
    unfold long_needle_match_periodic_after_right.
    hoare_auto.
    + unfold Hoare. split.
      * intros out st1 st2 [Hpinv [Hshape [Hlast Hright_last]]] Hnrm.
        destruct (critical_factorization_bounds patn Hne l p Hcf) as [[Hl _] _].
        destruct (match_right_last_to_standard text patn l pos r Hl
          (match_inv_pos text patn pos
            (periodic_match_base text patn l p pos memory Hpinv))
          Hwindow Hlast Hright_last)
          as [[Hr Hright] | [Hr Hright]]; try lia.
        pose proof (Hleft_prog Hpinv) as Hprog.
        unfold Hoare in Hprog. destruct Hprog as [Hprog _].
        eapply Hprog; eauto.
      * intros st [Hpinv [Hshape [Hlast Hright_last]]] Herr.
        destruct (critical_factorization_bounds patn Hne l p Hcf) as [[Hl _] _].
        destruct (match_right_last_to_standard text patn l pos r Hl
          (match_inv_pos text patn pos
            (periodic_match_base text patn l p pos memory Hpinv))
          Hwindow Hlast Hright_last)
          as [[Hr Hright] | [Hr Hright]]; try lia.
        pose proof (Hleft_prog Hpinv) as Hprog.
        unfold Hoare in Hprog. destruct Hprog as [_ Hprog].
        eapply Hprog; eauto.
    + destruct H0 as [Hpinv [Hshape [Hlast Hright_last]]].
      destruct (critical_factorization_bounds patn Hne l p Hcf) as [[Hl _] _].
      destruct (match_right_last_to_standard text patn l pos r Hl
        (match_inv_pos text patn pos
          (periodic_match_base text patn l p pos memory Hpinv))
        Hwindow Hlast Hright_last)
        as [[Hr Hright] | [Hr Hright]]; try lia.
      simpl. split.
      * apply (periodic_inv_continue_right text patn l p pos memory r);
          auto.
        lia.
      * left. reflexivity.
Qed.

Lemma long_periodic_body_correct :
  forall (text patn : list Z) (l p pos memory : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    repetitive_split patn l p ->
    Hoare
      (fun _ =>
         periodic_match_inv text patn l p pos memory /\
         (memory = 0 \/ memory = Zlength patn - p))
      (long_needle_match_periodic_loop_body text patn l p (pos, memory))
      (fun res _ =>
         match res with
         | by_continue (pos', memory') =>
             periodic_match_inv text patn l p pos' memory' /\
             (memory' = 0 \/ memory' = Zlength patn - p)
         | by_break out => match_post text patn out
         end).
Proof.
  intros text patn l p pos memory Hne Hcf Hrep.
  unfold long_needle_match_periodic_loop_body.
  hoare_auto; simpl.
  - eapply Hoare_bind.
    + apply Hoare_any.
    + intros n.
      hoare_auto; simpl.
      destruct H1 as [Hpinv Hshape].
      destruct Hpinv as [[Hpos Hno] [Hmemlo Hmemhi] Hprefix].
      assert (Hn : 0 < n) by (destruct H0 as [Hn _]; exact Hn).
      split.
      * constructor.
        -- constructor; [lia |].
           eapply no_occur_valid_skip; eauto.
        -- lia.
        -- repeat rewrite Zsublist_nil; try lia. reflexivity.
      * left. reflexivity.
  - eapply Hoare_conseq with
      (P2 := fun _ =>
         periodic_match_inv text patn l p pos memory /\
         (memory = 0 \/ memory = Zlength patn - p) /\
         match_cond text patn pos (Zlength patn - 1)).
    + intros st [Hpinv Hshape].
      split; [exact Hpinv |]. split; [exact Hshape | exact H0].
    + intros res st Hpost. exact Hpost.
    + eapply long_periodic_matching_correct; eauto.
  - destruct H0 as [Hpinv Hshape].
    destruct Hpinv as [[Hpos Hno] Hmemrange Hprefix].
    unfold match_post.
    eapply no_occur_overflow; eauto.
Qed.

Lemma long_periodic_body_continue :
  forall (text patn : list Z) (l p pos memory : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    repetitive_split patn l p ->
    Hoare
      (fun _ =>
         periodic_match_inv text patn l p pos memory /\
         (memory = 0 \/ memory = Zlength patn - p))
      (long_needle_match_periodic_loop_body text patn l p (pos, memory))
      (fun res _ =>
         match res with
         | by_continue (pos', memory') =>
             periodic_match_inv text patn l p pos' memory' /\
             (memory' = 0 \/ memory' = Zlength patn - p)
         | by_break _ => True
         end).
Proof.
  intros text patn l p pos memory Hne Hcf Hrep.
  eapply Hoare_conseq with
    (P2 := fun _ =>
       periodic_match_inv text patn l p pos memory /\
       (memory = 0 \/ memory = Zlength patn - p))
    (Q2 := fun res _ =>
       match res with
       | by_continue (pos', memory') =>
           periodic_match_inv text patn l p pos' memory' /\
           (memory' = 0 \/ memory' = Zlength patn - p)
       | by_break out => match_post text patn out
       end).
  - intros; eassumption.
  - intros [[pos' memory'] | out] st Hpost; simpl in *; auto.
  - apply long_periodic_body_correct; auto.
Qed.

Lemma long_periodic_body_break :
  forall (text patn : list Z) (l p pos memory : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    repetitive_split patn l p ->
    Hoare
      (fun _ =>
         periodic_match_inv text patn l p pos memory /\
         (memory = 0 \/ memory = Zlength patn - p))
      (long_needle_match_periodic_loop_body text patn l p (pos, memory))
      (fun res _ =>
         match res with
         | by_continue _ => True
         | by_break out => match_post text patn out
         end).
Proof.
  intros text patn l p pos memory Hne Hcf Hrep.
  eapply Hoare_conseq with
    (P2 := fun _ =>
       periodic_match_inv text patn l p pos memory /\
       (memory = 0 \/ memory = Zlength patn - p))
    (Q2 := fun res _ =>
       match res with
       | by_continue (pos', memory') =>
           periodic_match_inv text patn l p pos' memory' /\
           (memory' = 0 \/ memory' = Zlength patn - p)
       | by_break out => match_post text patn out
       end).
  - intros; eassumption.
  - intros [[pos' memory'] | out] st Hpost; simpl in *; auto.
  - apply long_periodic_body_correct; auto.
Qed.

Lemma long_needle_match_periodic_from_correct :
  forall (text patn : list Z) (l p pos memory : Z),
    patn <> nil ->
    critical_factorization_prop patn l p ->
    repetitive_split patn l p ->
    periodic_match_inv text patn l p pos memory ->
    (memory = 0 \/ memory = Zlength patn - p) ->
    Hoare
      (fun _ => True)
      (long_needle_match_periodic_from text patn l p pos memory)
      (fun out _ => match_post text patn out).
Proof.
  intros text patn l p pos memory Hne Hcf Hrep Hinv Hshape.
  unfold long_needle_match_periodic_from.
  eapply Hoare_conseq with
    (P2 := fun _ =>
      periodic_match_inv text patn l p pos memory /\
      (memory = 0 \/ memory = Zlength patn - p)).
  - intros st _. auto.
  - intros out st Hpost. exact Hpost.
  - refine ((@Hoare_repeat_break'
               unit match_periodic_state (option Z)
               (long_needle_match_periodic_loop_body text patn l p)
               (fun s _ =>
                  let '(pos', memory') := s in
                  periodic_match_inv text patn l p pos' memory' /\
                  (memory' = 0 \/ memory' = Zlength patn - p))
               (fun out _ => match_post text patn out))
              _ _ (pos, memory)).
    + intros [pos' memory'].
      eapply Hoare_bind.
      * apply long_periodic_body_continue; auto.
      * intros [[pos'' memory''] | out]; simpl; hoare_auto.
    + intros [pos' memory'].
      eapply Hoare_bind.
      * apply long_periodic_body_break; auto.
      * intros [[pos'' memory''] | out]; simpl; hoare_auto.
Qed.

(* Long-needle algorithm-correctness isolation file.

   This theorem states the mathematical correctness of the abstract
   long-needle Monad program. Its proof extends the
   existing two_way_match.v proof stack with long-needle bad-character skip and
   periodic skip lemmas, then proves the standard and periodic long-needle loops
   sound. The development remains isolated here and must not be moved
   into two_way_rel_lib.v or two_way_rel_proof_manual.v.

   Affected witness: two_way_long_needle_derive_high_level_spec_by_low_level_spec.

   2026-07-10 progress note: the refinement VC work is not finished. Official
   symexec succeeds and the UCharArray generated-file workaround must be
   re-applied after every refresh. Annotation was refined around the long-needle
   periodic zero-shift path to expose `shift == 0` and
   `match_cond text patn j (Zlength patn - 1)` without manufacturing a local
   `shift` heaplet.

   2026-07-16 progress note: `wit_11` through `wit_13` were integrated from
   scratch, `wit_14` was fixed manually, and focused Rocq MCP work advanced the
   official manual proof scripts through `wit_17_3`. MCP proof-state inspection
   of the old `wit_18_1` and `wit_18_2` exposed an annotation resource mismatch:
   the non-periodic long-needle loop invariant explicitly requested
   `data_at(&period, size_t, period)`, causing the refinement entailment to ask
   for a `period` heaplet that was not part of the abstract refinement frame.
   The annotation was repaired by deleting that explicit heaplet from the first
   non-periodic long-needle while invariant; `period` remains tracked as a C
   local by symbolic execution. Fresh symexec keeps the `wit_18_1/18_2/19`
   numbering stable and removes the impossible `period` heaplet from `wit_18`.
   `wit_18_2` still has the pure side condition
   `(needle_len_pre - suffix + 1) <= needle_len_pre`; the manual proof discharges
   it by deriving `1 <= suffix` from `retval <> 0` and
   `memcmp_result needle0_low_level_spec 0 mp suffix retval`, since a zero-length
   comparison would force `retval = 0`.

   2026-08-31 semantic round:
   - proof round 1 established `no_occur` preservation for abstract valid skips
     and completed the non-periodic long loop;
   - proof round 2 generalized the last-character right matcher to arbitrary
     starts and established the reachable periodic memory shape;
   - proof round 3 completed the periodic repeat loop and connected both phase
     branches to `critical_factorization_prog_match_sound`.
	 *)
Theorem two_way_long_needle_prog_sound :
  forall (text patn : list Z),
    Hoare (fun _ => patn <> nil)
          (two_way_long_needle_prog text patn)
          (fun res _ => match_post text patn res).
Proof.
  intros text patn.
  unfold two_way_long_needle_prog.
  eapply Hoare_bind
    with (Q := fun res _ =>
      patn <> nil /\
      critical_factorization_match_prop patn (fst res) (snd res)).
  - unfold Hoare. split.
    + intros res st1 st2 Hne Hnrm.
      split; [exact Hne |].
      pose proof (critical_factorization_prog_match_sound patn Hne) as Hcf.
      unfold Hoare in Hcf.
      destruct Hcf as [Hcf _].
      eapply Hcf; eauto.
    + intros st Hne Herr.
      pose proof (critical_factorization_prog_match_sound patn Hne) as Hcf.
      unfold Hoare in Hcf.
      destruct Hcf as [_ Hcf].
      eapply Hcf; eauto.
  - intros [l p].
    unfold long_needle_match_phase.
    hoare_auto.
    + unfold Hoare. split.
      * intros out st1 st2 [Hne [Hcf Hnonrep]] Hnrm.
        pose proof (long_needle_match_periodic_from_correct
          text patn l p 0 0 Hne Hcf H
          (periodic_match_inv_init text patn l p)
          (or_introl eq_refl)) as Hprog.
        unfold Hoare in Hprog. destruct Hprog as [Hprog _].
        eapply Hprog; eauto.
      * intros st [Hne [Hcf Hnonrep]] Herr.
        pose proof (long_needle_match_periodic_from_correct
          text patn l p 0 0 Hne Hcf H
          (periodic_match_inv_init text patn l p)
          (or_introl eq_refl)) as Hprog.
        unfold Hoare in Hprog. destruct Hprog as [_ Hprog].
        eapply Hprog; eauto.
    + unfold Hoare. split.
      * intros out st1 st2 [Hne [Hcf Hnonrep]] Hnrm.
        assert (Hcf' : critical_factorization_prop patn l
          (Z.max l (Zlength patn - l) + 1)) by (apply Hnonrep; exact H).
        pose proof (long_needle_match_from_correct text patn l
          (Z.max l (Zlength patn - l) + 1) 0 Hne Hcf'
          (match_inv_init text patn)) as Hprog.
        unfold Hoare in Hprog. destruct Hprog as [Hprog _].
        eapply Hprog; eauto.
      * intros st [Hne [Hcf Hnonrep]] Herr.
        assert (Hcf' : critical_factorization_prop patn l
          (Z.max l (Zlength patn - l) + 1)) by (apply Hnonrep; exact H).
        pose proof (long_needle_match_from_correct text patn l
          (Z.max l (Zlength patn - l) + 1) 0 Hne Hcf'
          (match_inv_init text patn)) as Hprog.
        unfold Hoare in Hprog. destruct Hprog as [_ Hprog].
        eapply Hprog; eauto.
Qed.
