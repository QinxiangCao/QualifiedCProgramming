Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Definition ExplainsCandyReports (l r a : list Z) : Prop :=
  Zlength a = Zlength l /\ Forall (fun x => 1 <= x <= Zlength a) a /\
  forall i, 0 <= i < Zlength a ->
    Znth i l 0 = Zlength (filter (fun j => Znth i a 0 <? Znth j a 0) (Zrange 0 i)) /\
    Znth i r 0 = Zlength (filter (fun j => Znth i a 0 <? Znth j a 0) (Zrange (i+1) (Zlength a))).
Definition Pre (l r : list Z) : Prop :=
  1 <= Zlength l <= 1000 /\ Zlength r = Zlength l /\
  Forall (fun x => 0 <= x <= Zlength l) l /\ Forall (fun x => 0 <= x <= Zlength l) r.
Definition Spec (l r : list Z) (out : option (list Z)) : Prop :=
  (exists a, out = Some a /\ ExplainsCandyReports l r a) \/
  (out = None /\ forall a, ~ ExplainsCandyReports l r a).

Definition CandyCandidateAt (n : Z) (l r : list Z) (i : Z) : Z :=
  n - Znth i l 0 - Znth i r 0.

Definition CandyCandidatePrefix
    (n : Z) (l r : list Z) (k : Z) (a : list Z) : Prop :=
  Zlength a = k /\
  forall i, 0 <= i < k -> Znth i a 0 = CandyCandidateAt n l r i.

Definition CandyLeftCount
    (a : list Z) (i j count : Z) : Prop :=
  count = Zlength
    (filter (fun k => Znth i a 0 <? Znth k a 0) (Zrange 0 j)).

Definition CandyRightCount
    (a : list Z) (i j count : Z) : Prop :=
  count = Zlength
    (filter (fun k => Znth i a 0 <? Znth k a 0) (Zrange (i + 1) j)).

Definition CandyCheckedPrefix
    (l r a : list Z) (k : Z) : Prop :=
  forall i, 0 <= i < k ->
    1 <= Znth i a 0 <= Zlength a /\
    Znth i l 0 = Zlength
      (filter (fun j => Znth i a 0 <? Znth j a 0) (Zrange 0 i)) /\
    Znth i r 0 = Zlength
      (filter (fun j => Znth i a 0 <? Znth j a 0)
        (Zrange (i + 1) (Zlength a))).

Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Lemma candy_candidate_prefix_nil__candidate_construction :
  forall n l r,
    CandyCandidatePrefix n l r 0 nil.
Proof.
  intros n l r.
  unfold CandyCandidatePrefix.
  split.
  - rewrite Zlength_nil. reflexivity.
  - intros i Hi. lia.
Qed.
Lemma candy_candidate_prefix_snoc__candidate_construction :
  forall n l r i prefix,
    CandyCandidatePrefix n l r i prefix ->
    0 <= i < n ->
    CandyCandidatePrefix n l r (i + 1)
      (prefix ++ CandyCandidateAt n l r i :: nil).
Proof.
  intros n l r i prefix Hprefix Hi.
  unfold CandyCandidatePrefix in *.
  destruct Hprefix as [Hlen Hprefix].
  split.
  - rewrite Zlength_app, Hlen, Zlength_cons, Zlength_nil. lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + unfold Znth at 1.
      rewrite app_nth1.
      * apply Hprefix. lia.
      * rewrite Zlength_correct in Hlen. lia.
    + assert (j = i) by lia. subst j.
      unfold Znth at 1.
      rewrite app_nth2.
      * rewrite Zlength_correct in Hlen.
        replace (Z.to_nat i - length prefix)%nat with 0%nat by lia.
        reflexivity.
      * rewrite Zlength_correct in Hlen. lia.
Qed.
Lemma candy_left_count_zero__checking_entry :
  forall (a : list Z) (i : Z), CandyLeftCount a i 0 0.
Proof.
  intros a i.
  unfold CandyLeftCount.
  simpl.
  reflexivity.
Qed.
Lemma candy_left_count_step_false__left_scan :
  forall a i j cl,
    0 <= j ->
    Znth j a 0 <= Znth i a 0 ->
    CandyLeftCount a i j cl ->
    CandyLeftCount a i (j + 1) (cl + 0).
Proof.
  intros a i j cl Hj Hcmp Hcount.
  assert (Hrange : Zrange 0 (j + 1) = Zrange 0 j ++ (j :: nil)).
  {
    unfold Zrange.
    replace (Z.to_nat (j + 1 - 0)) with
      (Z.to_nat (j - 0) + 1)%nat by lia.
    rewrite Zrange_aux_app. simpl.
    replace (j - 0) with j by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  }
  unfold CandyLeftCount in *.
  rewrite Hrange, filter_app.
  assert (Htest : (Znth i a 0 <? Znth j a 0) = false).
  { apply Z.ltb_ge. lia. }
  cbn. rewrite Htest. simpl.
  rewrite app_nil_r. lia.
Qed.
Lemma candy_left_count_step_true__left_scan :
  forall a i j cl,
    0 <= j ->
    Znth j a 0 > Znth i a 0 ->
    CandyLeftCount a i j cl ->
    CandyLeftCount a i (j + 1) (cl + 1).
Proof.
  intros a i j cl Hj Hcmp Hcount.
  assert (Hrange : Zrange 0 (j + 1) = Zrange 0 j ++ (j :: nil)).
  {
    unfold Zrange.
    replace (Z.to_nat (j + 1 - 0)) with
      (Z.to_nat (j - 0) + 1)%nat by lia.
    rewrite Zrange_aux_app. simpl.
    replace (j - 0) with j by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  }
  unfold CandyLeftCount in *.
  rewrite Hrange, filter_app.
  assert (Htest : (Znth i a 0 <? Znth j a 0) = true).
  { apply Z.ltb_lt. lia. }
  cbn. rewrite Htest. simpl.
  rewrite Zlength_app_cons. lia.
Qed.
Lemma candy_right_count_empty__left_scan :
  forall a i, CandyRightCount a i (i + 1) 0.
Proof.
  intros a i.
  unfold CandyRightCount, Zrange.
  replace (i + 1 - (i + 1)) with 0 by lia.
  reflexivity.
Qed.
Lemma candy_right_count_step_false__right_scan_commit :
  forall a i j cr,
    i + 1 <= j ->
    Znth j a 0 <= Znth i a 0 ->
    CandyRightCount a i j cr ->
    CandyRightCount a i (j + 1) cr.
Proof.
  intros a i j cr Hij Hfalse Hcount.
  unfold CandyRightCount in *.
  rewrite Hcount.
  unfold Zrange.
  replace (Z.to_nat (j + 1 - (i + 1)))
    with (Z.to_nat (j - (i + 1)) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  replace (i + 1 + Z.of_nat (Z.to_nat (j - (i + 1)))) with j by lia.
  rewrite filter_app.
  simpl.
  destruct (Znth i a 0 <? Znth j a 0) eqn:Hcmp; simpl.
  - apply Z.ltb_lt in Hcmp. lia.
  - rewrite app_nil_r. reflexivity.
Qed.
Lemma candy_right_count_step_true__right_scan_commit :
  forall a i j cr,
    i + 1 <= j ->
    Znth i a 0 < Znth j a 0 ->
    CandyRightCount a i j cr ->
    CandyRightCount a i (j + 1) (cr + 1).
Proof.
  intros a i j cr Hij Htrue Hcount.
  unfold CandyRightCount in *.
  rewrite Hcount.
  unfold Zrange.
  replace (Z.to_nat (j + 1 - (i + 1)))
    with (Z.to_nat (j - (i + 1)) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  replace (i + 1 + Z.of_nat (Z.to_nat (j - (i + 1)))) with j by lia.
  rewrite filter_app.
  simpl.
  destruct (Znth i a 0 <? Znth j a 0) eqn:Hcmp; simpl.
  - rewrite Zlength_app. simpl. reflexivity.
  - apply Z.ltb_ge in Hcmp. lia.
Qed.
Lemma candy_checked_prefix_succ__right_scan_commit :
  forall n l r a i j cl cr,
    CandyCheckedPrefix l r a i ->
    CandyCandidatePrefix n l r n a ->
    0 <= i < n ->
    1 <= Znth i a 0 ->
    0 <= cl ->
    0 <= cr ->
    cl = Znth i l 0 ->
    cr = Znth i r 0 ->
    CandyLeftCount a i i cl ->
    CandyRightCount a i j cr ->
    n <= j ->
    j <= n ->
    CandyCheckedPrefix l r a (i + 1).
Proof.
  intros n l r a i j cl cr Hchecked Hcandidate Hi Hapos
    Hcl Hcr Hcleq Hcreq Hleft Hright Hnj Hjn.
  unfold CandyCheckedPrefix in *.
  intros k Hk.
  destruct (Z_lt_ge_dec k i) as [Hki | Hik].
  - apply Hchecked. lia.
  - assert (Hkeq : k = i) by lia.
    subst k.
    unfold CandyCandidatePrefix in Hcandidate.
    destruct Hcandidate as [Halen Hcandidate].
    specialize (Hcandidate i Hi).
    unfold CandyCandidateAt in Hcandidate.
    unfold CandyLeftCount in Hleft.
    unfold CandyRightCount in Hright.
    assert (Hjeq : j = n) by lia.
    subst j.
    rewrite Halen.
    rewrite <- Hleft, <- Hright.
    rewrite <- Hcleq, <- Hcreq in Hcandidate.
    rewrite Hcandidate.
    lia.
Qed.
Lemma candy_checked_complete_explains__successful_return :
  forall n l r candidate,
    n = Zlength l ->
    Zlength r = n ->
    CandyCandidatePrefix n l r n candidate ->
    CandyCheckedPrefix l r candidate n ->
    ExplainsCandyReports l r candidate.
Proof.
  intros n l r candidate Hn _ Hcandidate Hchecked.
  destruct Hcandidate as [Hcandidate_length _].
  assert (Hlength : Zlength candidate = Zlength l) by lia.
  unfold ExplainsCandyReports.
  split; [exact Hlength |].
  split.
  - apply (proj2
      (Forall_Znth (fun x : Z => 1 <= x <= Zlength candidate)
        0 candidate)).
    intros index Hindex.
    apply Hchecked.
    rewrite Hcandidate_length in Hindex.
    exact Hindex.
  - intros index Hindex.
    destruct (Hchecked index) as [_ Hreports].
    + rewrite Hcandidate_length in Hindex.
      exact Hindex.
    + exact Hreports.
Qed.
Lemma Zlength_Zrange_aux__rejected_return : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IHm. lia.
Qed.
Lemma Zlength_Zrange__rejected_return : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle.
  unfold Zrange.
  rewrite Zlength_Zrange_aux__rejected_return.
  lia.
Qed.
Lemma Zrange_split_index__rejected_return : forall n i,
  0 <= i < n ->
  Zrange 0 n = Zrange 0 i ++ i :: Zrange (i + 1) n.
Proof.
  intros n i Hi.
  unfold Zrange.
  replace (Z.to_nat (n - 0)) with
      (Z.to_nat (i - 0) + S (Z.to_nat (n - (i + 1))))%nat by lia.
  rewrite Zrange_aux_app.
  replace (0 + Z.of_nat (Z.to_nat (i - 0))) with i by lia.
  simpl.
  reflexivity.
Qed.
Lemma nodup_strict_incl_Zlength__rejected_return :
  forall (xs ys : list Z),
    NoDup xs -> NoDup ys -> incl xs ys ->
    (exists z, In z ys /\ ~ In z xs) ->
    Zlength xs < Zlength ys.
Proof.
  intros xs ys Hxs Hys Hincl [z [Hzy Hznx]].
  assert (Hlen : (length xs <= length ys)%nat).
  { apply NoDup_incl_length; assumption. }
  assert (Hneq : length xs <> length ys).
  {
    intro Heq.
    assert (Hperm : Permutation xs ys).
    {
      apply NoDup_Permutation_bis; try assumption.
      lia.
    }
    apply Hznx.
    eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hzy.
  }
  assert (Hlt : (length xs < length ys)%nat) by lia.
  rewrite !Zlength_correct.
  apply Nat2Z.inj_lt. exact Hlt.
Qed.
Lemma upper_filter_strict_length__rejected_return :
  forall (a : list Z) n i j,
    0 <= i < n -> 0 <= j < n ->
    Znth i a 0 < Znth j a 0 ->
    Zlength
      (filter (fun k => Znth j a 0 <? Znth k a 0) (Zrange 0 n)) <
    Zlength
      (filter (fun k => Znth i a 0 <? Znth k a 0) (Zrange 0 n)).
Proof.
  intros a n i j Hi Hj Hij.
  apply nodup_strict_incl_Zlength__rejected_return.
  - apply NoDup_filter. apply NoDup_Zrange.
  - apply NoDup_filter. apply NoDup_Zrange.
  - intros k Hk.
    apply filter_In in Hk as [Hkr Hcmp].
    apply filter_In. split; [exact Hkr |].
    apply Z.ltb_lt in Hcmp.
    apply Z.ltb_lt.
    lia.
  - exists j. split.
    + apply filter_In. split.
      * apply In_Zrange. exact Hj.
      * apply Z.ltb_lt. exact Hij.
    + intro Hbad.
      apply filter_In in Hbad as [_ Hbad].
      rewrite Z.ltb_irrefl in Hbad.
      discriminate.
Qed.
Lemma upper_filter_rank_iff__rejected_return :
  forall (a : list Z) n i j,
    0 <= i < n -> 0 <= j < n ->
    (Zlength
       (filter (fun k => Znth j a 0 <? Znth k a 0) (Zrange 0 n)) <
     Zlength
       (filter (fun k => Znth i a 0 <? Znth k a 0) (Zrange 0 n))
     <-> Znth i a 0 < Znth j a 0).
Proof.
  intros a n i j Hi Hj. split.
  - intro Hlen.
    destruct (Z_lt_le_dec (Znth i a 0) (Znth j a 0)); [assumption |].
    destruct (Z.eq_dec (Znth i a 0) (Znth j a 0)) as [Heq | Hneq].
    + rewrite Heq in Hlen. lia.
    + assert (Hji : Znth j a 0 < Znth i a 0) by lia.
      pose proof
        (upper_filter_strict_length__rejected_return a n j i Hj Hi Hji).
      lia.
  - apply upper_filter_strict_length__rejected_return; assumption.
Qed.
Lemma candy_reports_total_upper__rejected_return :
  forall l r a i,
    ExplainsCandyReports l r a ->
    0 <= i < Zlength a ->
    Znth i l 0 + Znth i r 0 =
    Zlength
      (filter (fun k => Znth i a 0 <? Znth k a 0)
        (Zrange 0 (Zlength a))).
Proof.
  intros l r a i [_ [_ Hreports]] Hi.
  specialize (Hreports i Hi) as [Hl Hr].
  rewrite (Zrange_split_index__rejected_return (Zlength a) i Hi).
  rewrite filter_app. simpl.
  rewrite Z.ltb_irrefl.
  rewrite Zlength_app.
  lia.
Qed.
Lemma candy_upper_count_bound__rejected_return :
  forall (a : list Z) i,
    0 <= i < Zlength a ->
    0 <=
      Zlength
        (filter (fun k => Znth i a 0 <? Znth k a 0)
          (Zrange 0 (Zlength a))) <
      Zlength a.
Proof.
  intros a i Hi. split.
  - apply Zlength_nonneg.
  - assert (Hrlen : Zlength (Zrange 0 (Zlength a)) = Zlength a).
    {
      rewrite Zlength_Zrange__rejected_return
        by (pose proof (Zlength_nonneg a); lia).
      lia.
    }
    rewrite <- Hrlen at 2.
    apply nodup_strict_incl_Zlength__rejected_return.
    + apply NoDup_filter. apply NoDup_Zrange.
    + apply NoDup_Zrange.
    + intros k Hk. apply filter_In in Hk. tauto.
    + exists i. split.
      * apply In_Zrange. exact Hi.
      * intro Hbad. apply filter_In in Hbad as [_ Hbad].
        rewrite Z.ltb_irrefl in Hbad. discriminate.
Qed.
Lemma candy_candidate_rank_order_iff__rejected_return :
  forall n l r a candidate i j,
    n = Zlength l ->
    ExplainsCandyReports l r a ->
    CandyCandidatePrefix n l r n candidate ->
    0 <= i < n -> 0 <= j < n ->
    (Znth i candidate 0 < Znth j candidate 0 <->
     Znth i a 0 < Znth j a 0).
Proof.
  intros n l r a candidate i j Hn Hexpl Hcandidate Hi Hj.
  destruct Hexpl as [Halen [Habounds Hreports]].
  destruct Hcandidate as [Hclen Hcandidate].
  rewrite (Hcandidate i Hi), (Hcandidate j Hj).
  unfold CandyCandidateAt.
  assert (Hai : 0 <= i < Zlength a) by lia.
  assert (Haj : 0 <= j < Zlength a) by lia.
  pose proof
    (candy_reports_total_upper__rejected_return l r a i
      (conj Halen (conj Habounds Hreports)) Hai) as Htot_i.
  pose proof
    (candy_reports_total_upper__rejected_return l r a j
      (conj Halen (conj Habounds Hreports)) Haj) as Htot_j.
  pose proof (upper_filter_rank_iff__rejected_return
    a (Zlength a) i j Hai Haj) as Hrank.
  lia.
Qed.
Lemma candy_candidate_canonical_explains__rejected_return :
  forall n l r a candidate,
    n = Zlength l ->
    ExplainsCandyReports l r a ->
    CandyCandidatePrefix n l r n candidate ->
    ExplainsCandyReports l r candidate.
Proof.
  intros n l r a candidate Hn Hexpl Hcandidate.
  destruct Hexpl as [Halen [Habounds Hreports]].
  destruct Hcandidate as [Hclen Hcandidate].
  split; [lia |]. split.
  - apply (proj2 (Forall_Znth
      (fun x : Z => 1 <= x <= Zlength candidate) 0 candidate)).
    intros i Hi.
    rewrite Hclen in Hi.
    rewrite Hcandidate by exact Hi.
    unfold CandyCandidateAt.
    assert (Hai : 0 <= i < Zlength a) by lia.
    pose proof
      (candy_reports_total_upper__rejected_return l r a i
        (conj Halen (conj Habounds Hreports)) Hai) as Htot.
    pose proof (candy_upper_count_bound__rejected_return a i Hai) as Hbound.
    lia.
  - intros i Hi.
    assert (Hai : 0 <= i < Zlength a) by lia.
    assert (Hi' : 0 <= i < n) by lia.
    assert (Hcalen : Zlength candidate = Zlength a) by lia.
    pose proof (Hreports i Hai) as [Hl Hr].
    split.
    + rewrite Hl. f_equal.
      apply filter_ext_in. intros k Hk.
      apply (proj2 (In_Zrange 0 i k)) in Hk.
      assert (Hk' : 0 <= k < n) by lia.
      pose proof (candy_candidate_rank_order_iff__rejected_return
        n l r a candidate i k Hn
        (conj Halen (conj Habounds Hreports))
        (conj Hclen Hcandidate) Hi' Hk') as Hrank.
      destruct (Znth i candidate 0 <? Znth k candidate 0) eqn:Hc,
               (Znth i a 0 <? Znth k a 0) eqn:Ha; try reflexivity.
      * apply Z.ltb_lt in Hc. apply Z.ltb_ge in Ha. apply Hrank in Hc. lia.
      * apply Z.ltb_ge in Hc. apply Z.ltb_lt in Ha.
        apply Hrank in Ha. lia.
    + rewrite Hcalen. rewrite Hr. f_equal.
      apply filter_ext_in. intros k Hk.
      apply (proj2 (In_Zrange (i + 1) (Zlength a) k)) in Hk.
      assert (Hk' : 0 <= k < n) by lia.
      pose proof (candy_candidate_rank_order_iff__rejected_return
        n l r a candidate i k Hn
        (conj Halen (conj Habounds Hreports))
        (conj Hclen Hcandidate) Hi' Hk') as Hrank.
      destruct (Znth i candidate 0 <? Znth k candidate 0) eqn:Hc,
               (Znth i a 0 <? Znth k a 0) eqn:Ha; try reflexivity.
      * apply Z.ltb_lt in Hc. apply Z.ltb_ge in Ha. apply Hrank in Hc. lia.
      * apply Z.ltb_ge in Hc. apply Z.ltb_lt in Ha.
        apply Hrank in Ha. lia.
Qed.
Lemma candy_explains_value_bound__rejected_return :
  forall l r a i,
    ExplainsCandyReports l r a ->
    0 <= i < Zlength a ->
    1 <= Znth i a 0 <= Zlength a.
Proof.
  intros l r a i [_ [Hbounds _]] Hi.
  exact ((proj1 (Forall_Znth
    (fun x : Z => 1 <= x <= Zlength a) 0 a)) Hbounds i Hi).
Qed.
