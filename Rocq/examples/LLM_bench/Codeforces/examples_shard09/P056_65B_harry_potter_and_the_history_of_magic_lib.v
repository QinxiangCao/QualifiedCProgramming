Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition FourDigits (x : Z) (d : list Z) : Prop :=
  Zlength d = 4 /\ Forall (fun z => 0 <= z <= 9) d /\ Znth 0 d 0 <> 0 /\
  x = 1000 * Znth 0 d 0 + 100 * Znth 1 d 0 + 10 * Znth 2 d 0 + Znth 3 d 0.
Definition AtMostOneDigit (x y : Z) : Prop :=
  exists a b, FourDigits x a /\ FourDigits y b /\ (#(fun i : Z => 0 <= i < Zlength a /\ Znth i a 0 <> Znth i b 0)) <= 1.
Definition ValidYears (src out : list Z) : Prop :=
  Zlength out = Zlength src /\ mono_nondec out /\ Forall (fun y => 1000 <= y <= 2011) out /\
  forall i, 0 <= i < Zlength src -> AtMostOneDigit (Znth i src 0) (Znth i out 0).
Definition Pre (years : list Z) : Prop :=
  (* Stated explicitly in the P056 solver Require, so dropped here:
       1 <= Zlength years <= 1000 /\
       Forall (fun y => 1000 <= y <= 9999) years  *)
  True.

Definition Spec (years : list Z) (out : option (list Z)) : Prop :=
  (out = None /\ ~exists y, ValidYears years y) \/ (exists y, out = Some y /\ ValidYears years y).

(** The ordinary decimal digits of a four-digit input year. *)
Definition YearDigits (y : Z) : list Z :=
  [y / 1000; y / 100 mod 10; y / 10 mod 10; y mod 10].

Definition DigitsValue (d : list Z) : Z :=
  1000 * Znth 0 d 0 + 100 * Znth 1 d 0 +
  10 * Znth 2 d 0 + Znth 3 d 0.

Definition DigitLower (pos : Z) : Z :=
  if Z.eq_dec pos 0 then 1 else 0.

(** The year obtained by choosing [v] for digit [pos].  This is a finite
    mathematical candidate description, not an execution model of the C
    loops. *)
Definition CandidateValue (y pos v : Z) : Z :=
  DigitsValue (replace_Znth pos v (YearDigits y)).

Definition LegalNext (y prev cand : Z) : Prop :=
  1000 <= cand <= 2011 /\ prev <= cand /\ AtMostOneDigit y cand.

Definition CursorCandidate (y pos next cand : Z) : Prop :=
  exists p v,
    0 <= p < 4 /\ DigitLower p <= v <= 9 /\
    (p < pos \/ (p = pos /\ v < next)) /\
    cand = CandidateValue y p v.

(** [best] is the minimum legal candidate in the finite part of the digit
    search selected by [(pos,next)], or [-1] when that part is empty. *)
Definition BestScanned (y prev pos next best : Z) : Prop :=
  (best = -1 /\
   forall cand, CursorCandidate y pos next cand -> ~ LegalNext y prev cand) \/
  (CursorCandidate y pos next best /\ LegalNext y prev best /\
   forall cand, CursorCandidate y pos next cand ->
                LegalNext y prev cand -> best <= cand).

Definition MinimalNext (y prev best : Z) : Prop :=
  LegalNext y prev best /\
  forall cand, LegalNext y prev cand -> best <= cand.

Definition NextYearResult (y prev result : Z) : Prop :=
  (result = -1 /\ forall cand, ~ LegalNext y prev cand) \/
  MinimalNext y prev result.

Definition PreviousYear (out : list Z) : Z :=
  if Z.eq_dec (Zlength out) 0 then 1000
  else Znth (Zlength out - 1) out 1000.

(** Each constructed prefix entry is the least legal year after its
    predecessor.  The source list may be longer than the constructed prefix. *)
Definition GreedyPrefix (years out : list Z) : Prop :=
  Zlength out <= Zlength years /\
  forall i, 0 <= i < Zlength out ->
    MinimalNext
      (Znth i years 0)
      (if Z.eq_dec i 0 then 1000 else Znth (i - 1) out 1000)
      (Znth i out 0).

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zwf.
Lemma Zlength_replace_Znth__candidate_scan :
  forall {A : Type} (l : list A) i (x : A),
    Zlength (replace_Znth i x l) = Zlength l.
Proof.
  intros A l i x. rewrite !Zlength_correct. f_equal. unfold replace_Znth.
  remember (Z.to_nat i) as n. clear Heqn i. revert n.
  induction l as [|a xs IH]; intros [|n]; simpl; auto.
Qed.
Lemma four_digits_year_digits__candidate_scan :
  forall y, 1000 <= y <= 9999 -> FourDigits y (YearDigits y).
Proof.
  intros y Hy. unfold FourDigits, YearDigits. split; [reflexivity |]. split.
  - constructor.
    + split.
      * apply Z.div_pos; lia.
      * assert (y / 1000 < 10) by (apply Z.div_lt_upper_bound; lia). lia.
    + constructor.
      * split; pose proof (Z.mod_pos_bound (y / 100) 10 ltac:(lia)); lia.
      * constructor.
        -- split; pose proof (Z.mod_pos_bound (y / 10) 10 ltac:(lia)); lia.
        -- constructor.
           ++ split; pose proof (Z.mod_pos_bound y 10 ltac:(lia)); lia.
           ++ constructor.
  - split.
    + change (y / 1000 <> 0).
      assert (1 <= y / 1000) by (apply Zdiv_le_lower_bound; lia). lia.
    + change (y = 1000 * (y / 1000) + 100 * ((y / 100) mod 10) +
                  10 * ((y / 10) mod 10) + y mod 10).
      pose proof (Z.div_mod y 10 ltac:(lia)) as H0.
      pose proof (Z.div_mod (y / 10) 10 ltac:(lia)) as H1.
      pose proof (Z.div_mod (y / 100) 10 ltac:(lia)) as H2.
      rewrite Z.div_div in H1 by lia. rewrite Z.div_div in H2 by lia.
      replace (10 * 10) with 100 in H1 by lia.
      replace (100 * 10) with 1000 in H2 by lia. lia.
Qed.
Lemma cursor_candidate_step__candidate_scan :
  forall y pos v cand,
    0 <= pos < 4 -> DigitLower pos <= v <= 9 ->
    (CursorCandidate y pos (v + 1) cand <->
     CursorCandidate y pos v cand \/ cand = CandidateValue y pos v).
Proof.
  intros y pos v cand Hpos Hv. unfold CursorCandidate. split.
  - intros [p [w [Hp [Hw [Hbefore ->]]]]].
    destruct Hbefore as [Hlt | [Heq Hwv]].
    + left. exists p, w. split; [exact Hp |]. split; [exact Hw |].
      split; [left; exact Hlt | reflexivity].
    + subst p. assert (w < v \/ w = v) by lia. destruct H as [Hlt | ->].
      * left. exists pos, w. split; [exact Hpos |]. split; [exact Hw |].
        split; [right; split; [reflexivity | exact Hlt] | reflexivity].
      * right. reflexivity.
  - intros [[p [w [Hp [Hw [Hbefore ->]]]]] | ->].
    + exists p, w. split; [exact Hp |]. split; [exact Hw |].
      split; [destruct Hbefore; [left | right]; lia | reflexivity].
    + exists pos, v. split; [exact Hpos |]. split; [exact Hv |].
      split; [right; lia | reflexivity].
Qed.
Lemma best_scanned_accept_candidate__candidate_scan :
  forall y prev pos v old cand,
    0 <= pos < 4 -> DigitLower pos <= v <= 9 ->
    BestScanned y prev pos v old -> cand = CandidateValue y pos v ->
    LegalNext y prev cand -> (old = -1 \/ cand < old) ->
    BestScanned y prev pos (v + 1) cand.
Proof.
  intros y prev pos v old cand Hpos Hv Hold Hcand Hlegal Hbetter.
  unfold BestScanned in Hold |- *. destruct Hold as [[Hold Hnone] | [Hcursor [Holdlegal Hmin]]].
  - right. split.
    + apply (proj2 (cursor_candidate_step__candidate_scan y pos v cand Hpos Hv)). right. exact Hcand.
    + split; [exact Hlegal |]. intros other Hother Hotherlegal.
      apply (proj1 (cursor_candidate_step__candidate_scan y pos v other Hpos Hv)) in Hother.
      destruct Hother as [Hprevious | ->].
      * exfalso. exact (Hnone _ Hprevious Hotherlegal).
      * lia.
  - right. split.
    + apply (proj2 (cursor_candidate_step__candidate_scan y pos v cand Hpos Hv)). right. exact Hcand.
    + split; [exact Hlegal |]. intros other Hother Hotherlegal.
      apply (proj1 (cursor_candidate_step__candidate_scan y pos v other Hpos Hv)) in Hother.
      destruct Hother as [Hprevious | ->].
      * specialize (Hmin _ Hprevious Hotherlegal).
        destruct Hbetter as [Heq | Hlt]; [subst old; unfold LegalNext in Holdlegal; lia | lia].
      * lia.
Qed.
Lemma best_scanned_reject_candidate__candidate_scan :
  forall y prev pos v old cand,
    0 <= pos < 4 -> DigitLower pos <= v <= 9 ->
    BestScanned y prev pos v old -> cand = CandidateValue y pos v ->
    (~ LegalNext y prev cand \/ (old <> -1 /\ old <= cand)) ->
    BestScanned y prev pos (v + 1) old.
Proof.
  intros y prev pos v old cand Hpos Hv Hold Hcand Hreject.
  unfold BestScanned in Hold |- *. destruct Hold as [[Hold Hnone] | [Hcursor [Holdlegal Hmin]]].
  - left. split; [exact Hold |]. intros other Hother Hotherlegal.
    apply (proj1 (cursor_candidate_step__candidate_scan y pos v other Hpos Hv)) in Hother.
    destruct Hother as [Hprevious | Heq].
    + exact (Hnone _ Hprevious Hotherlegal).
    + subst other. destruct Hreject as [Hillegal | [Hne _]].
      * apply Hillegal. rewrite Hcand. exact Hotherlegal.
      * exact (Hne Hold).
  - right. split.
    + apply (proj2 (cursor_candidate_step__candidate_scan y pos v old Hpos Hv)). left. exact Hcursor.
    + split; [exact Holdlegal |]. intros other Hother Hotherlegal.
      apply (proj1 (cursor_candidate_step__candidate_scan y pos v other Hpos Hv)) in Hother.
      destruct Hother as [Hprevious | Heq].
      * exact (Hmin _ Hprevious Hotherlegal).
      * subst other. destruct Hreject as [Hillegal | [_ Hle]].
        -- exfalso. apply Hillegal. rewrite Hcand. exact Hotherlegal.
        -- rewrite <- Hcand. exact Hle.
Qed.
Lemma set_card_at_most_singleton__candidate_scan :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x,
    (forall y, P y -> y = x) -> @set_card A P FP <= 1.
Proof.
  intros A P FP x Honly. unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|a [|b l]] eqn:Henum; simpl; try lia.
  exfalso.
  assert (Ha : P a).
  { apply (proj2 (@enum_ok A P FP a)). rewrite Henum. simpl. auto. }
  assert (Hb : P b).
  { apply (proj2 (@enum_ok A P FP b)). rewrite Henum. simpl. auto. }
  pose proof (@enum_nodup A P FP) as Hnd. rewrite Henum in Hnd. inversion Hnd; subst.
  apply H1. left. rewrite (Honly _ Ha), (Honly _ Hb). reflexivity.
Qed.
Lemma replace_Znth_preserves_digit_bounds__candidate_scan :
  forall d pos v,
    Zlength d = 4 -> Forall (fun z => 0 <= z <= 9) d ->
    0 <= pos < 4 -> 0 <= v <= 9 ->
    Forall (fun z => 0 <= z <= 9) (replace_Znth pos v d).
Proof.
  intros d pos v Hlen Hd Hpos Hv.
  apply (proj2 (Forall_Znth (fun z => 0 <= z <= 9) 0 _)). intros i Hi.
  rewrite Zlength_replace_Znth__candidate_scan in Hi. destruct (Z.eq_dec i pos) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia). exact Hv.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
    apply (proj1 (Forall_Znth (fun z => 0 <= z <= 9) 0 d) Hd i). lia.
Qed.
Lemma replace_Znth_overwrite__candidate_scan :
  forall {A : Type} (i : Z) (x y : A) l,
    replace_Znth i x (replace_Znth i y l) = replace_Znth i x l.
Proof.
  intros A i x y l. unfold replace_Znth.
  set (n := Z.to_nat i). clearbody n. clear i.
  revert n. induction l as [|a l IH]; intros [|n]; simpl; auto.
  rewrite IH. reflexivity.
Qed.
Lemma four_digits_candidate_value__candidate_scan :
  forall y pos v,
    1000 <= y <= 9999 -> 0 <= pos < 4 -> DigitLower pos <= v <= 9 ->
    FourDigits (CandidateValue y pos v) (replace_Znth pos v (YearDigits y)).
Proof.
  intros y pos v Hy Hpos Hv.
  pose proof (four_digits_year_digits__candidate_scan y Hy) as Hbase.
  unfold FourDigits in Hbase |- *. destruct Hbase as [Hlen [Hbounds [Hlead Hvalue]]].
  split.
  - rewrite Zlength_replace_Znth__candidate_scan. exact Hlen.
  - split.
    + eapply replace_Znth_preserves_digit_bounds__candidate_scan; eauto.
      unfold DigitLower in Hv. destruct (Z.eq_dec pos 0); lia.
    + split.
      * destruct (Z.eq_dec pos 0) as [-> | Hneq].
        -- rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
           unfold DigitLower in Hv. destruct (Z.eq_dec 0 0); lia.
        -- rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). exact Hlead.
      * unfold CandidateValue, DigitsValue. ring.
Qed.
Lemma at_most_one_digit_candidate__candidate_scan :
  forall y pos v,
    1000 <= y <= 9999 -> 0 <= pos < 4 -> DigitLower pos <= v <= 9 ->
    AtMostOneDigit y (CandidateValue y pos v).
Proof.
  intros y pos v Hy Hpos Hv. unfold AtMostOneDigit.
  exists (YearDigits y), (replace_Znth pos v (YearDigits y)). split.
  - apply four_digits_year_digits__candidate_scan. exact Hy.
  - split.
    + apply four_digits_candidate_value__candidate_scan; assumption.
    + apply set_card_at_most_singleton__candidate_scan with (x := pos).
      intros i [Hi Hdiff]. destruct (Z.eq_dec i pos) as [Heq | Hneq]; auto.
      exfalso. apply Hdiff. assert (Zlength (YearDigits y) = 4) as Hlen by reflexivity.
      rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). reflexivity.
Qed.
Lemma cursor_finished_position_equiv__cursor_completion :
  forall y pos cand,
    0 <= pos < 4 ->
    (CursorCandidate y pos 10 cand <->
     CursorCandidate y (pos + 1) (DigitLower (pos + 1)) cand).
Proof.
  intros y pos cand Hpos.
  unfold CursorCandidate.
  split.
  - intros (p & digit & Hp & Hdigit & Hcursor & Hcand).
    exists p, digit.
    split; [exact Hp|].
    split; [exact Hdigit|].
    split.
    + destruct Hcursor as [Hlt | [Heq Hdigit10]].
      * left; lia.
      * left; lia.
    + exact Hcand.
  - intros (p & digit & Hp & Hdigit & Hcursor & Hcand).
    exists p, digit.
    split; [exact Hp|].
    split; [exact Hdigit|].
    split.
    + destruct Hcursor as [Hlt | [Heq Hdigitlower]].
      * destruct (Z.eq_dec p pos) as [-> | Hne].
        -- right; split; lia.
        -- left; lia.
      * exfalso; subst p; lia.
    + exact Hcand.
Qed.
Lemma replace_Znth_restore_original__cursor_completion :
  forall (l : list Z) pos new,
    replace_Znth pos (Znth pos l 0) (replace_Znth pos new l) = l.
Proof.
  intros l pos new.
  unfold replace_Znth, Znth.
  set (n := Z.to_nat pos).
  clearbody n; clear pos.
  revert n.
  induction l as [|a l IH]; intros [|n]; simpl; auto.
  f_equal; apply IH.
Qed.
Lemma four_digits_canonical__cursor_completion :
  forall x d, FourDigits x d -> d = YearDigits x.
Proof.
  intros x d (Hlen & Hall & Hlead & Hvalue).
  rewrite Zlength_correct in Hlen.
  destruct d as [|d0 d]; simpl in Hlen; [lia|].
  destruct d as [|d1 d]; simpl in Hlen; [lia|].
  destruct d as [|d2 d]; simpl in Hlen; [lia|].
  destruct d as [|d3 d]; simpl in Hlen; [lia|].
  destruct d; simpl in Hlen; [|lia].
  inversion Hall as [|? ? Hd0 Hall1].
  inversion Hall1 as [|? ? Hd1 Hall2].
  inversion Hall2 as [|? ? Hd2 Hall3].
  inversion Hall3 as [|? ? Hd3 Hall4].
  change (d0 <> 0) in Hlead.
  change (x = 1000 * d0 + 100 * d1 + 10 * d2 + d3) in Hvalue.
  assert (Hd0eq : d0 = x / 1000).
  { apply Z.div_unique with (r := 100 * d1 + 10 * d2 + d3).
    - left; nia.
    - nia. }
  assert (Hdiv100 : 10 * d0 + d1 = x / 100).
  { apply Z.div_unique with (r := 10 * d2 + d3).
    - left; nia.
    - nia. }
  assert (Hd1eq : d1 = x / 100 mod 10).
  { apply Z.mod_unique with (q := d0).
    - left; nia.
    - nia. }
  assert (Hdiv10 : 100 * d0 + 10 * d1 + d2 = x / 10).
  { apply Z.div_unique with (r := d3).
    - left; nia.
    - nia. }
  assert (Hd2eq : d2 = x / 10 mod 10).
  { apply Z.mod_unique with (q := 10 * d0 + d1).
    - left; nia.
    - nia. }
  assert (Hd3eq : d3 = x mod 10).
  { apply Z.mod_unique with (q := 100 * d0 + 10 * d1 + d2).
    - left; nia.
    - nia. }
  unfold YearDigits.
  now rewrite <- Hd0eq, <- Hd1eq, <- Hd2eq, <- Hd3eq.
Qed.
Lemma set_card_two_members__cursor_completion :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x y,
    x <> y -> P x -> P y -> 2 <= @set_card A P FP.
Proof.
  intros A P FP x y Hxy Hx Hy.
  unfold set_card, SumLib.Sum.sum.
  assert (Hinx : In x (@enum A P FP)).
  { apply (proj1 (@enum_ok A P FP x)); exact Hx. }
  assert (Hiny : In y (@enum A P FP)).
  { apply (proj1 (@enum_ok A P FP y)); exact Hy. }
  assert (Hfold : forall l : list A,
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
    Z.of_nat (length l)).
  { intro l. induction l as [|z zs IH]; [reflexivity|].
    change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 zs =
            Z.of_nat (S (length zs))).
    rewrite IH, Nat2Z.inj_succ; lia. }
  rewrite Hfold.
  change (Z.of_nat 2 <= Z.of_nat (length (@enum A P FP))).
  apply (proj1 (Nat2Z.inj_le 2 (length (@enum A P FP)))).
  change (length [x; y] <= length (@enum A P FP))%nat.
  eapply NoDup_incl_length.
  - constructor.
    + simpl. intros [Heq | []]. apply Hxy; symmetry; exact Heq.
    + constructor; [simpl; tauto|constructor].
  - intros z [Hz | [Hz | []]]; subst; assumption.
Qed.
Lemma legal_next_is_cursor_candidate__cursor_completion :
  forall y prev cand,
    LegalNext y prev cand -> CursorCandidate y 4 (DigitLower 4) cand.
Proof.
  intros y prev cand (_ & _ & HatMost).
  destruct HatMost as (a & b & Hfoura & Hfourb & Hcard).
  pose proof (four_digits_canonical__cursor_completion y a Hfoura) as Ha.
  pose proof (four_digits_canonical__cursor_completion cand b Hfourb) as Hb.
  subst a; subst b.
  destruct Hfourb as (Hblen & Hbforall & Hblead & Hbvalue).
  assert (Hdigit : forall i, 0 <= i < 4 ->
      0 <= Znth i (YearDigits cand) 0 <= 9).
  { intros i Hi.
    apply (Forall_Znth_Zlength (fun z => 0 <= z <= 9)
             (YearDigits cand) 0 i Hbforall).
    unfold YearDigits; change (0 <= i < 4); exact Hi. }
  destruct (Z.eq_dec (Znth 0 (YearDigits y) 0)
                     (Znth 0 (YearDigits cand) 0)) as [H0 | H0].
  - destruct (Z.eq_dec (Znth 1 (YearDigits y) 0)
                       (Znth 1 (YearDigits cand) 0)) as [H1 | H1].
    + destruct (Z.eq_dec (Znth 2 (YearDigits y) 0)
                         (Znth 2 (YearDigits cand) 0)) as [H2 | H2].
      * destruct (Z.eq_dec (Znth 3 (YearDigits y) 0)
                           (Znth 3 (YearDigits cand) 0)) as [H3 | H3].
        -- exists 0, (Znth 0 (YearDigits cand) 0).
           split; [lia|].
           split.
           ++ unfold DigitLower; destruct (Z.eq_dec 0 0); [|contradiction].
              specialize (Hdigit 0 ltac:(lia)).
              destruct Hdigit as [Hlo Hhi]. split; [|exact Hhi].
              assert (Znth 0 (YearDigits cand) 0 <> 0).
              { exact Hblead. }
              lia.
           ++ split.
              ** left; lia.
              ** change (y / 1000 = cand / 1000) in H0.
                 change (y / 100 mod 10 = cand / 100 mod 10) in H1.
                 change (y / 10 mod 10 = cand / 10 mod 10) in H2.
                 change (y mod 10 = cand mod 10) in H3.
                 assert (Hlists :
                   replace_Znth 0 (Znth 0 (YearDigits cand) 0) (YearDigits y) =
                   YearDigits cand).
                 { unfold YearDigits; simpl. now rewrite H0, H1, H2, H3. }
                 unfold CandidateValue. rewrite Hlists.
                 unfold DigitsValue. exact Hbvalue.
        -- exists 3, (Znth 3 (YearDigits cand) 0).
           split; [lia|].
           split.
           ++ unfold DigitLower; destruct (Z.eq_dec 3 0); [lia|].
              apply Hdigit; lia.
           ++ split.
              ** left; lia.
              ** change (y / 1000 = cand / 1000) in H0.
                 change (y / 100 mod 10 = cand / 100 mod 10) in H1.
                 change (y / 10 mod 10 = cand / 10 mod 10) in H2.
                 assert (Hlists :
                   replace_Znth 3 (Znth 3 (YearDigits cand) 0) (YearDigits y) =
                   YearDigits cand).
                 { unfold YearDigits; simpl. now rewrite H0, H1, H2. }
                 unfold CandidateValue. rewrite Hlists.
                 unfold DigitsValue. exact Hbvalue.
      * assert (H3 : Znth 3 (YearDigits y) 0 = Znth 3 (YearDigits cand) 0).
        { destruct (Z.eq_dec (Znth 3 (YearDigits y) 0)
                             (Znth 3 (YearDigits cand) 0)) as [Heq | Hneq]; [exact Heq|].
          exfalso.
          pose proof (@set_card_two_members__cursor_completion Z
            (fun i : Z => 0 <= i < Zlength (YearDigits y) /\
               Znth i (YearDigits y) 0 <> Znth i (YearDigits cand) 0)
            _ 2 3 ltac:(lia)
            ltac:(split; [unfold YearDigits; change (0 <= 2 < 4); lia|exact H2])
            ltac:(split; [unfold YearDigits; change (0 <= 3 < 4); lia|exact Hneq])).
          lia. }
        exists 2, (Znth 2 (YearDigits cand) 0).
        split; [lia|].
        split.
        -- unfold DigitLower; destruct (Z.eq_dec 2 0); [lia|].
           apply Hdigit; lia.
        -- split.
           ++ left; lia.
           ++ change (y / 1000 = cand / 1000) in H0.
              change (y / 100 mod 10 = cand / 100 mod 10) in H1.
              change (y mod 10 = cand mod 10) in H3.
              assert (Hlists :
                replace_Znth 2 (Znth 2 (YearDigits cand) 0) (YearDigits y) =
                YearDigits cand).
              { unfold YearDigits; simpl. now rewrite H0, H1, H3. }
              unfold CandidateValue. rewrite Hlists.
              unfold DigitsValue. exact Hbvalue.
    + assert (H2 : Znth 2 (YearDigits y) 0 = Znth 2 (YearDigits cand) 0).
      { destruct (Z.eq_dec (Znth 2 (YearDigits y) 0)
                           (Znth 2 (YearDigits cand) 0)) as [Heq | Hneq]; [exact Heq|].
        exfalso.
        pose proof (@set_card_two_members__cursor_completion Z
          (fun i : Z => 0 <= i < Zlength (YearDigits y) /\
             Znth i (YearDigits y) 0 <> Znth i (YearDigits cand) 0)
          _ 1 2 ltac:(lia)
          ltac:(split; [unfold YearDigits; change (0 <= 1 < 4); lia|exact H1])
          ltac:(split; [unfold YearDigits; change (0 <= 2 < 4); lia|exact Hneq])).
        lia. }
      assert (H3 : Znth 3 (YearDigits y) 0 = Znth 3 (YearDigits cand) 0).
      { destruct (Z.eq_dec (Znth 3 (YearDigits y) 0)
                           (Znth 3 (YearDigits cand) 0)) as [Heq | Hneq]; [exact Heq|].
        exfalso.
        pose proof (@set_card_two_members__cursor_completion Z
          (fun i : Z => 0 <= i < Zlength (YearDigits y) /\
             Znth i (YearDigits y) 0 <> Znth i (YearDigits cand) 0)
          _ 1 3 ltac:(lia)
          ltac:(split; [unfold YearDigits; change (0 <= 1 < 4); lia|exact H1])
          ltac:(split; [unfold YearDigits; change (0 <= 3 < 4); lia|exact Hneq])).
        lia. }
      exists 1, (Znth 1 (YearDigits cand) 0).
      split; [lia|].
      split.
      * unfold DigitLower; destruct (Z.eq_dec 1 0); [lia|].
        apply Hdigit; lia.
      * split.
        -- left; lia.
        -- change (y / 1000 = cand / 1000) in H0.
           change (y / 10 mod 10 = cand / 10 mod 10) in H2.
           change (y mod 10 = cand mod 10) in H3.
           assert (Hlists :
             replace_Znth 1 (Znth 1 (YearDigits cand) 0) (YearDigits y) =
             YearDigits cand).
           { unfold YearDigits; simpl. now rewrite H0, H2, H3. }
           unfold CandidateValue. rewrite Hlists.
           unfold DigitsValue. exact Hbvalue.
  - assert (H1 : Znth 1 (YearDigits y) 0 = Znth 1 (YearDigits cand) 0).
    { destruct (Z.eq_dec (Znth 1 (YearDigits y) 0)
                         (Znth 1 (YearDigits cand) 0)) as [Heq | Hneq]; [exact Heq|].
      exfalso.
      pose proof (@set_card_two_members__cursor_completion Z
        (fun i : Z => 0 <= i < Zlength (YearDigits y) /\
           Znth i (YearDigits y) 0 <> Znth i (YearDigits cand) 0)
        _ 0 1 ltac:(lia)
        ltac:(split; [unfold YearDigits; change (0 <= 0 < 4); lia|exact H0])
        ltac:(split; [unfold YearDigits; change (0 <= 1 < 4); lia|exact Hneq])).
      lia. }
    assert (H2 : Znth 2 (YearDigits y) 0 = Znth 2 (YearDigits cand) 0).
    { destruct (Z.eq_dec (Znth 2 (YearDigits y) 0)
                         (Znth 2 (YearDigits cand) 0)) as [Heq | Hneq]; [exact Heq|].
      exfalso.
      pose proof (@set_card_two_members__cursor_completion Z
        (fun i : Z => 0 <= i < Zlength (YearDigits y) /\
           Znth i (YearDigits y) 0 <> Znth i (YearDigits cand) 0)
        _ 0 2 ltac:(lia)
        ltac:(split; [unfold YearDigits; change (0 <= 0 < 4); lia|exact H0])
        ltac:(split; [unfold YearDigits; change (0 <= 2 < 4); lia|exact Hneq])).
      lia. }
    assert (H3 : Znth 3 (YearDigits y) 0 = Znth 3 (YearDigits cand) 0).
    { destruct (Z.eq_dec (Znth 3 (YearDigits y) 0)
                         (Znth 3 (YearDigits cand) 0)) as [Heq | Hneq]; [exact Heq|].
      exfalso.
      pose proof (@set_card_two_members__cursor_completion Z
        (fun i : Z => 0 <= i < Zlength (YearDigits y) /\
           Znth i (YearDigits y) 0 <> Znth i (YearDigits cand) 0)
        _ 0 3 ltac:(lia)
        ltac:(split; [unfold YearDigits; change (0 <= 0 < 4); lia|exact H0])
        ltac:(split; [unfold YearDigits; change (0 <= 3 < 4); lia|exact Hneq])).
      lia. }
    exists 0, (Znth 0 (YearDigits cand) 0).
    split; [lia|].
    split.
    + unfold DigitLower; destruct (Z.eq_dec 0 0); [|contradiction].
      specialize (Hdigit 0 ltac:(lia)).
      destruct Hdigit as [Hlo Hhi]. split; [|exact Hhi].
      assert (Znth 0 (YearDigits cand) 0 <> 0) by exact Hblead.
      lia.
    + split.
      * left; lia.
      * change (y / 100 mod 10 = cand / 100 mod 10) in H1.
        change (y / 10 mod 10 = cand / 10 mod 10) in H2.
        change (y mod 10 = cand mod 10) in H3.
        assert (Hlists :
          replace_Znth 0 (Znth 0 (YearDigits cand) 0) (YearDigits y) =
          YearDigits cand).
        { unfold YearDigits; simpl. now rewrite H1, H2, H3. }
        unfold CandidateValue. rewrite Hlists.
        unfold DigitsValue. exact Hbvalue.
Qed.
Lemma best_scanned_full_cursor_result__cursor_completion :
  forall y prev best,
    BestScanned y prev 4 (DigitLower 4) best ->
    NextYearResult y prev best.
Proof.
  intros y prev best Hbest.
  unfold BestScanned in Hbest.
  unfold NextYearResult, MinimalNext.
  destruct Hbest as [[Heq Hnone] | [Hcursor [Hlegal Hmin]]].
  - left; split; [exact Heq|].
    intros cand Hlegal.
    apply (Hnone cand
      (legal_next_is_cursor_candidate__cursor_completion y prev cand Hlegal)).
    exact Hlegal.
  - right; split; [exact Hlegal|].
    intros cand Hlegalcand.
    apply Hmin; [|exact Hlegalcand].
    apply legal_next_is_cursor_candidate__cursor_completion with (prev := prev).
    exact Hlegalcand.
Qed.
Lemma greedy_prefix_previous_year_bounds__solver_setup :
  forall years done,
    GreedyPrefix years done ->
    1000 <= PreviousYear done <= 2011.
Proof.
  intros years done Hprefix.
  destruct done as [| first rest].
  - unfold PreviousYear.
    simpl.
    lia.
  - unfold PreviousYear.
    destruct (Z.eq_dec (Zlength (first :: rest)) 0) as [Hzero | Hnonzero].
    + rewrite Zlength_cons in Hzero.
      pose proof (Zlength_nonneg rest).
      lia.
    + destruct Hprefix as [_ Hprefix].
      specialize (Hprefix (Zlength (first :: rest) - 1)).
      assert (Hlast : 0 <= Zlength (first :: rest) - 1 < Zlength (first :: rest)).
      {
        rewrite Zlength_cons.
        pose proof (Zlength_nonneg rest).
        lia.
      }
      specialize (Hprefix Hlast).
      unfold MinimalNext, LegalNext in Hprefix.
      destruct Hprefix as [[[Hlower Hupper] _] _].
      rewrite (Znth_indep (first :: rest)
                          (Zlength (first :: rest) - 1) 1000 0) by exact Hlast.
      exact (conj Hlower Hupper).
Qed.
Lemma replace_Znth_at_snoc_slot__solver_prefix_extension :
  forall (done : list Z) old value,
    replace_Znth (Zlength done) value (done ++ [old]) = done ++ [value].
Proof.
  intros done old value.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (Zlength done - Zlength done) with 0 by lia.
  reflexivity.
Qed.
Lemma previous_year_snoc__solver_prefix_extension :
  forall (done : list Z) x,
    PreviousYear (done ++ [x]) = x.
Proof.
  intros done x.
  unfold PreviousYear.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  pose proof (Zlength_nonneg done).
  match goal with
  | |- context [if ?d then _ else _] => destruct d as [Hz | Hz]
  end; [lia |].
  rewrite app_Znth2 by lia.
  assert (Zlength done + Z.succ 0 - 1 - Zlength done = 0) as Hidx by lia.
  rewrite Hidx.
  reflexivity.
Qed.
Lemma greedy_prefix_snoc__solver_prefix_extension :
  forall (years done : list Z) x,
    Zlength done < Zlength years ->
    GreedyPrefix years done ->
    MinimalNext (Znth (Zlength done) years 0) (PreviousYear done) x ->
    GreedyPrefix years (done ++ [x]).
Proof.
  intros years done x Hlen [Hprefix_len Hprefix] Hnext.
  unfold GreedyPrefix.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros j Hj.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hj.
    destruct (Z_lt_ge_dec j (Zlength done)) as [Hold | Hnew].
    + specialize (Hprefix j ltac:(lia)).
      destruct (Z.eq_dec j 0) as [Hj0 | Hj0].
      * rewrite Hj0 in *.
        rewrite (app_Znth1 0 done [x] 0) by lia.
        exact Hprefix.
      * rewrite (app_Znth1 0 done [x] j) by lia.
        rewrite (app_Znth1 1000 done [x] (j - 1)) by lia.
        exact Hprefix.
    + assert (j = Zlength done) by lia.
      subst j.
      rewrite (app_Znth2 0 done [x] (Zlength done)) by lia.
      replace (Zlength done - Zlength done) with 0 by lia.
      simpl.
      destruct (Z.eq_dec (Zlength done) 0) as [Hempty | Hnonempty].
      * unfold PreviousYear in Hnext.
        destruct (Z.eq_dec (Zlength done) 0); [exact Hnext | congruence].
      * unfold PreviousYear in Hnext.
        destruct (Z.eq_dec (Zlength done) 0); [congruence |].
        rewrite (app_Znth1 1000 done [x] (Zlength done - 1)) by lia.
        exact Hnext.
Qed.
Lemma greedy_prefix_full_valid_years__solver_results :
  forall years done,
    GreedyPrefix years done ->
    Zlength done = Zlength years ->
    ValidYears years done.
Proof.
  intros years done [Hprefix_len Hminimal] Hlen.
  unfold ValidYears.
  repeat split.
  - exact Hlen.
  - apply (proj2 (mono_nondec_iff_adjacent done)).
    intros j Hj Hjsucc.
    specialize (Hminimal (j + 1) ltac:(lia)).
    unfold MinimalNext, LegalNext in Hminimal.
    destruct Hminimal as [[_ [Hprev _]] _].
    destruct (Z.eq_dec (j + 1) 0); [lia |].
    replace (j + 1 - 1) with j in Hprev by lia.
    rewrite (Znth_indep done j 1000 0) in Hprev by lia.
    exact Hprev.
  - apply (proj2 (Forall_Znth (fun y => 1000 <= y <= 2011) 0 done)).
    intros j Hj.
    specialize (Hminimal j Hj).
    unfold MinimalNext, LegalNext in Hminimal.
    tauto.
  - intros j Hj.
    specialize (Hminimal j ltac:(lia)).
    unfold MinimalNext, LegalNext in Hminimal.
    tauto.
Qed.
Lemma greedy_prefix_le_valid_years__solver_results :
  forall years done out k,
    GreedyPrefix years done ->
    ValidYears years out ->
    0 <= k < Zlength done ->
    Znth k done 0 <= Znth k out 0.
Proof.
  intros years done out k [Hprefix_len Hminimal]
    [Hout_len [Hout_mono [Hout_range Hout_digits]]] Hk.
  induction k as [k IH] using (well_founded_induction (Zwf_well_founded 0)).
  specialize (Hminimal k Hk).
  destruct Hminimal as [Hdone_legal Hleast].
  apply Hleast.
  unfold LegalNext.
  split.
  - apply (proj1 (Forall_Znth (fun y => 1000 <= y <= 2011) 0 out)
      Hout_range k).
    lia.
  - split.
    + destruct (Z.eq_dec k 0) as [-> | Hk0].
      * apply (proj1 (Forall_Znth (fun y => 1000 <= y <= 2011) 0 out)
          Hout_range 0).
        lia.
      * assert (Hprev_done :
          Znth (k - 1) done 0 <= Znth (k - 1) out 0).
        { apply IH.
          - unfold Zwf. lia.
          - lia. }
        rewrite (Znth_indep done (k - 1) 1000 0) by lia.
        eapply Z.le_trans; [exact Hprev_done |].
        apply Hout_mono; lia.
    + apply Hout_digits. lia.
Qed.
Lemma greedy_prefix_no_extension_blocks_valid_years__solver_results :
  forall years done i,
    GreedyPrefix years done ->
    i = Zlength done ->
    i < Zlength years ->
    (forall cand, ~ LegalNext (Znth i years 0) (PreviousYear done) cand) ->
    ~ exists out, ValidYears years out.
Proof.
  intros years done i Hprefix Hi Hbound Hnone [out Hvalid].
  subst i.
  pose proof (Zlength_nonneg done) as Hdone_nonneg.
  apply (Hnone (Znth (Zlength done) out 0)).
  destruct Hvalid as [Hout_len [Hout_mono [Hout_range Hout_digits]]].
  unfold LegalNext.
  split.
  - apply (proj1 (Forall_Znth (fun y => 1000 <= y <= 2011) 0 out)
      Hout_range (Zlength done)).
    lia.
  - split.
    + unfold PreviousYear.
      destruct (Z.eq_dec (Zlength done) 0) as [Hempty | Hnonempty].
      * apply (proj1 (Forall_Znth (fun y => 1000 <= y <= 2011) 0 out)
          Hout_range (Zlength done)).
        lia.
      * assert (Hcmp :
          Znth (Zlength done - 1) done 0 <=
          Znth (Zlength done - 1) out 0).
        { eapply greedy_prefix_le_valid_years__solver_results.
          - exact Hprefix.
          - repeat split; eauto.
          - lia. }
        rewrite (Znth_indep done (Zlength done - 1) 1000 0) by lia.
        eapply Z.le_trans; [exact Hcmp |].
        apply Hout_mono; lia.
    + apply Hout_digits. lia.
Qed.
