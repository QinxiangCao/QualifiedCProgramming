Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition DecimalDigitsOf (x : Z) (digits : list Z) : Prop :=
  0 < Zlength digits /\
  Forall (fun d => 0 <= d <= 9) digits /\
  Znth 0 digits 0 <> 0 /\
  x = fold_left (fun value digit => 10 * value + digit) digits 0.

Definition DigitRecurrenceStep (x y : Z) : Prop :=
  exists digits lo hi,
    DecimalDigitsOf x digits /\
    min_value_of_subset Z.le (fun d : Z => In d digits)
      (fun d => d) lo /\
    max_value_of_subset Z.le (fun d : Z => In d digits)
      (fun d => d) hi /\
    y = x + lo * hi.

Definition Pre (a1 k : Z) : Prop :=
  1 <= a1 <= 1000000000000000000 /\
  1 <= k <= 10000000000000000.

Definition Spec (a1 k out : Z) : Prop :=
  exists values,
    Zlength values = k /\ Znth 0 values 0 = a1 /\
    Znth (k - 1) values 0 = out /\
    forall i, 0 <= i < k - 1 ->
      DigitRecurrenceStep (Znth i values 0) (Znth (i + 1) values 0).

Definition DigitExtrema (digits : list Z) (lo hi : Z) : Prop :=
  min_value_of_subset Z.le (fun d : Z => In d digits)
    (fun d => d) lo /\
  max_value_of_subset Z.le (fun d : Z => In d digits)
    (fun d => d) hi.

Definition DigitScanState
    (original remaining mn mx : Z) : Prop :=
  exists pending processed,
    DecimalDigitsOf original (pending ++ processed) /\
    remaining =
      fold_left (fun value digit => 10 * value + digit) pending 0 /\
    ((processed = nil /\ mn = 9 /\ mx = 0) \/
     (processed <> nil /\ DigitExtrema processed mn mx)).

Definition SequencePrefix (a1 count current : Z) : Prop :=
  exists values,
    Zlength values = count /\ Znth 0 values 0 = a1 /\
    Znth (count - 1) values 0 = current /\
    forall i, 0 <= i < count - 1 ->
      DigitRecurrenceStep (Znth i values 0) (Znth (i + 1) values 0).

Lemma Spec_SequencePrefix :
  forall a1 k out, Spec a1 k out <-> SequencePrefix a1 k out.
Proof.
  intros; reflexivity.
Qed.

Require Import Coq.micromega.Lia.
Lemma digit_scan_state_initial__step_initialization :
  forall x, 1 <= x -> DigitScanState x x 9 0.
Proof.
  assert (Hdecimal :
    forall n, 1 <= n -> exists digits, DecimalDigitsOf n digits).
  {
    apply (Zlt_lower_bound_ind
      (fun n => exists digits, DecimalDigitsOf n digits) 1).
    intros n IH Hn.
    destruct (Z_lt_ge_dec n 10) as [Hsmall | Hlarge].
    - exists [n].
      unfold DecimalDigitsOf.
      split.
      + rewrite Zlength_cons, Zlength_nil. lia.
      + split.
        * constructor; [lia | constructor].
        * split.
          -- rewrite Znth0_cons. lia.
          -- simpl. lia.
    - assert (Hqpos : 1 <= n / 10).
      {
        apply Z.div_le_lower_bound; lia.
      }
      assert (Hqlt : n / 10 < n).
      {
        apply Z.div_lt_upper_bound; nia.
      }
      destruct (IH (n / 10)) as [digits Hdigits].
      { lia. }
      unfold DecimalDigitsOf in Hdigits.
      destruct Hdigits as [Hlen [Hbounds [Hhead Hvalue]]].
      destruct digits as [| d digits].
      { rewrite Zlength_nil in Hlen. lia. }
      exists ((d :: digits) ++ [n mod 10]).
      unfold DecimalDigitsOf.
      repeat split.
      + rewrite Zlength_app.
        change (0 < Zlength (d :: digits) + 1). lia.
      + apply Forall_app. split; [exact Hbounds |].
        constructor.
        * pose proof (Z.mod_pos_bound n 10 ltac:(lia)) as Hmod. lia.
        * constructor.
      + rewrite Znth0_cons in Hhead. exact Hhead.
      + rewrite fold_left_app. rewrite <- Hvalue. simpl.
        exact (Z.div_mod n 10 ltac:(lia)).
  }
  intros x Hx.
  destruct (Hdecimal x Hx) as [digits Hdigits].
  unfold DigitScanState.
  exists digits, nil.
  rewrite app_nil_r.
  split; [exact Hdigits |].
  split.
  - unfold DecimalDigitsOf in Hdigits. tauto.
  - left. repeat split; reflexivity.
Qed.
Lemma signed_decimal_remainder_bounds__step_transitions :
  forall x,
    0 <= x ->
    0 <= Z.rem x 10 <= 9.
Proof.
  intros x Hx.
  pose proof (Z.rem_bound_pos x 10 Hx ltac:(lia)) as Hmod.
  lia.
Qed.
Lemma digit_extrema_singleton__step_transitions :
  forall d,
    DigitExtrema [d] d d.
Proof.
  intros d.
  unfold DigitExtrema, min_value_of_subset, min_object_of_subset,
    max_value_of_subset, max_object_of_subset.
  split.
  - exists d. split.
    + split.
      * change (In d [d]); simpl; auto.
      * intros b Hb. change (In b [d]) in Hb.
        simpl in Hb. destruct Hb as [Hb | Hb]; [subst b; lia | contradiction].
    + reflexivity.
  - exists d. split.
    + split.
      * change (In d [d]); simpl; auto.
      * intros b Hb. change (In b [d]) in Hb.
        simpl in Hb. destruct Hb as [Hb | Hb]; [subst b; lia | contradiction].
    + reflexivity.
Qed.
Lemma digit_extrema_cons__step_transitions :
  forall digits mn mx d,
    DigitExtrema digits mn mx ->
    DigitExtrema (d :: digits) (Z.min mn d) (Z.max mx d).
Proof.
  intros digits mn mx d [Hmin Hmax].
  unfold min_value_of_subset, min_object_of_subset in Hmin.
  unfold max_value_of_subset, max_object_of_subset in Hmax.
  destruct Hmin as [a [[Ha Hamin] Ha_eq]].
  destruct Hmax as [b [[Hb Hbmax] Hb_eq]].
  unfold DigitExtrema, min_value_of_subset, min_object_of_subset,
    max_value_of_subset, max_object_of_subset.
  split.
  - destruct (Z_le_dec mn d) as [Hmnd | Hdmn].
    + rewrite Z.min_l by lia.
      exists a. split.
      * split.
        -- simpl; right; exact Ha.
        -- intros c [Hcd | Hc].
           ++ subst c; lia.
           ++ specialize (Hamin c Hc); lia.
      * exact Ha_eq.
    + rewrite Z.min_r by lia.
      exists d. split.
      * split.
        -- change (In d (d :: digits)); simpl; auto.
        -- intros c [Hcd | Hc].
           ++ subst c; lia.
           ++ specialize (Hamin c Hc); lia.
      * reflexivity.
  - destruct (Z_le_dec d mx) as [Hdmx | Hmxd].
    + rewrite Z.max_l by lia.
      exists b. split.
      * split.
        -- simpl; right; exact Hb.
        -- intros c [Hcd | Hc].
           ++ subst c; lia.
           ++ specialize (Hbmax c Hc); lia.
      * exact Hb_eq.
    + rewrite Z.max_r by lia.
      exists d. split.
      * split.
        -- change (In d (d :: digits)); simpl; auto.
        -- intros c [Hcd | Hc].
           ++ subst c; lia.
           ++ specialize (Hbmax c Hc); lia.
      * reflexivity.
Qed.
Lemma digit_scan_state_advance__step_transitions :
  forall original remaining mn mx,
    DigitScanState original remaining mn mx ->
    0 <= remaining ->
    remaining <> 0 ->
    DigitScanState original (Z.quot remaining 10)
      (Z.min mn (Z.rem remaining 10))
      (Z.max mx (Z.rem remaining 10)).
Proof.
  intros original remaining mn mx Hstate Hremaining_nonnegative
    Hremaining_nonzero.
  unfold DigitScanState in Hstate |- *.
  destruct Hstate as [pending [processed [Hdigits [Hremaining Hprocessed]]]].
  assert (Hpending_nonempty : pending <> []).
  { intro Hnil. subst pending. simpl in Hremaining. contradiction. }
  apply exists_last in Hpending_nonempty.
  destruct Hpending_nonempty as [prefix [d Hpending]].
  subst pending.
  pose proof Hdigits as Hdigits_rearranged.
  unfold DecimalDigitsOf in Hdigits.
  destruct Hdigits as [Hlength [Hforall [Hleading Horiginal]]].
  apply Forall_app in Hforall as [Hforall_prefix_d Hforall_processed].
  apply Forall_app in Hforall_prefix_d as [Hforall_prefix Hforall_d].
  assert (Hd_bounds : 0 <= d <= 9).
  { inversion Hforall_d; assumption. }
  assert (Hdecimal :
    DecimalDigitsOf original (prefix ++ d :: processed)).
  { replace (prefix ++ d :: processed)
      with ((prefix ++ [d]) ++ processed) by
        (rewrite <- app_assoc; reflexivity).
    exact Hdigits_rearranged. }
  rewrite fold_left_app in Hremaining.
  simpl in Hremaining.
  change (remaining =
    10 * fold_left (fun value digit : Z => 10 * value + digit) prefix 0 + d)
    in Hremaining.
  assert (Hmod : remaining mod 10 = d).
  { symmetry. apply Z.mod_unique with
      (q := fold_left (fun value digit : Z => 10 * value + digit) prefix 0);
      lia. }
  assert (Hdiv :
    remaining / 10 =
      fold_left (fun value digit : Z => 10 * value + digit) prefix 0).
  { symmetry. apply Z.div_unique with (r := d); lia. }
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Hmod.
  exists prefix, (d :: processed).
  split; [exact Hdecimal |].
  split; [exact Hdiv |].
  right. split; [discriminate |].
  destruct Hprocessed as [[Hprocessed_nil [Hmn Hmx]] |
                            [Hprocessed_nonempty Hextrema]].
  - subst processed mn mx.
    replace (Z.min 9 d) with d by lia.
    replace (Z.max 0 d) with d by lia.
    apply digit_extrema_singleton__step_transitions.
  - apply digit_extrema_cons__step_transitions.
    exact Hextrema.
Qed.
Lemma fold_decimal_positive__step_finalization :
  forall digits acc,
    Forall (fun d : Z => 0 <= d) digits ->
    0 < acc ->
    0 < fold_left (fun value digit => 10 * value + digit) digits acc.
Proof.
  induction digits as [| digit digits IH]; intros acc Hdigits Hacc.
  - exact Hacc.
  - inversion Hdigits; subst.
    change
      (0 < fold_left (fun value digit => 10 * value + digit)
         digits (10 * acc + digit)).
    apply IH.
    + assumption.
    + lia.
Qed.
Lemma digit_scan_state_complete__step_finalization :
  forall x_pre mn mx,
    DigitScanState x_pre 0 mn mx ->
    DigitRecurrenceStep x_pre (x_pre + mn * mx).
Proof.
  intros x_pre mn mx Hscan.
  unfold DigitScanState in Hscan.
  destruct Hscan as (pending & processed & Hdigits & Hremaining & Hstate).
  destruct pending as [| digit pending].
  - simpl in Hdigits, Hremaining.
    destruct Hstate as [[Hprocessed _] | [Hprocessed Hextrema]].
    + subst processed.
      unfold DecimalDigitsOf in Hdigits.
      destruct Hdigits as (Hlength & _).
      rewrite Zlength_nil in Hlength.
      lia.
    + unfold DigitRecurrenceStep.
      exists processed, mn, mx.
      unfold DigitExtrema in Hextrema.
      tauto.
  - unfold DecimalDigitsOf in Hdigits.
    destruct Hdigits as (_ & Hbounds & Hfirst & _).
    simpl in Hbounds.
    change (digit <> 0) in Hfirst.
    change
      (0 = fold_left (fun value digit => 10 * value + digit)
         pending digit) in Hremaining.
    inversion Hbounds as [| ? ? Hdigit Htail]; subst.
    assert (Hdigit_pos : 0 < digit) by lia.
    apply Forall_app in Htail as [Hpending _].
    assert (Hpending_nonneg : Forall (fun d : Z => 0 <= d) pending).
    { eapply Forall_impl; [| exact Hpending].
      intros d Hd; exact (proj1 Hd). }
    pose proof
      (fold_decimal_positive__step_finalization
         pending digit Hpending_nonneg Hdigit_pos) as Hpositive.
    rewrite <- Hremaining in Hpositive.
    exfalso.
    exact (Z.lt_irrefl 0 Hpositive).
Qed.
Lemma Znth_app_left__solver_prefix :
  forall (l1 l2 : list Z) (d i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma Znth_app_last__solver_prefix :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ [x]) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma sequence_prefix_base__solver_prefix :
  forall a, SequencePrefix a 1 a.
Proof.
  intros a.
  unfold SequencePrefix.
  exists [a].
  repeat split; try reflexivity.
  intros i Hi.
  lia.
Qed.
Lemma sequence_prefix_extend__solver_prefix :
  forall a1 i a b,
    1 <= i ->
    SequencePrefix a1 i a ->
    DigitRecurrenceStep a b ->
    SequencePrefix a1 (i + 1) b.
Proof.
  intros a1 i a b Hi Hprefix Hstep.
  unfold SequencePrefix in *.
  destruct Hprefix as [values [Hlen [Hfirst [Hlast Hedges]]]].
  exists (values ++ [b]).
  repeat split.
  - rewrite Zlength_app, Hlen, Zlength_cons, Zlength_nil.
    lia.
  - rewrite Znth_app_left__solver_prefix.
    + exact Hfirst.
    + rewrite Hlen.
      lia.
  - replace (i + 1 - 1) with (Zlength values) by lia.
    apply Znth_app_last__solver_prefix.
  - intros j Hj.
    destruct (Z_lt_ge_dec j (i - 1)) as [Hold | Hnew].
    + rewrite Znth_app_left__solver_prefix by (rewrite Hlen; lia).
      rewrite Znth_app_left__solver_prefix by (rewrite Hlen; lia).
      apply Hedges.
      lia.
    + assert (j = i - 1) by lia.
      subst j.
      rewrite Znth_app_left__solver_prefix by (rewrite Hlen; lia).
      rewrite Hlast.
      replace (i - 1 + 1) with (Zlength values) by lia.
      rewrite Znth_app_last__solver_prefix.
      exact Hstep.
Qed.
Lemma sequence_prefix_index_spec__solver_results :
  forall a1 k out,
    SequencePrefix a1 k out -> Spec a1 k out.
Proof.
  intros a1 k out Hprefix.
  apply (proj2 (Spec_SequencePrefix a1 k out)).
  exact Hprefix.
Qed.
Lemma sequence_fixed_point_spec__solver_results :
  forall a1 i k a,
    1 <= i ->
    i <= k ->
    SequencePrefix a1 i a ->
    DigitRecurrenceStep a a ->
    Spec a1 k a.
Proof.
  intros a1 i k a Hi Hik Hprefix Hstep.
  destruct Hprefix as [values [Hlen [Hfirst [Hlast Hedges]]]].
  unfold Spec.
  exists (values ++ repeat a (Z.to_nat (k - i))).
  repeat split.
  - rewrite Zlength_app, Hlen, Zlength_correct, repeat_length, Z2Nat.id by lia.
    lia.
  - rewrite app_Znth1 by lia.
    exact Hfirst.
  - destruct (Z.eq_dec k i) as [Hki | Hki].
    + subst k.
      replace (i - i) with 0 by lia.
      simpl.
      rewrite app_nil_r.
      exact Hlast.
    + rewrite app_Znth2 by lia.
      rewrite Znth_repeat_lt.
      * reflexivity.
      * rewrite Z2Nat.id by lia.
        lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j (i - 1)) as [Hjold | Hjnew].
    + rewrite !app_Znth1 by lia.
      apply Hedges.
      lia.
    + destruct (Z.eq_dec j (i - 1)) as [Hboundary | Hsuffix].
      * subst j.
        rewrite app_Znth1 by lia.
        rewrite app_Znth2 by lia.
        rewrite Hlast.
        rewrite Znth_repeat_lt.
        -- exact Hstep.
        -- rewrite Z2Nat.id by lia.
           lia.
      * rewrite !app_Znth2 by lia.
        rewrite !Znth_repeat_lt.
        -- exact Hstep.
        -- rewrite Z2Nat.id by lia.
           lia.
        -- rewrite Z2Nat.id by lia.
           lia.
Qed.
