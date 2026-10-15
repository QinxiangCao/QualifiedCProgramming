Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition ShirtSelection (score place : Z) : Prop :=
  exists values,
    Zlength values = 26 /\ Znth 0 values 0 = (score / 50) mod 475 /\
    (forall i, 0 <= i < 25 ->
       Znth (i + 1) values 0 = (Znth i values 0 * 96 + 42) mod 475) /\
    exists i, 1 <= i <= 25 /\ place = 26 + Znth i values 0.

Definition GoalWithHacks (p x y successful : Z) : Prop :=
  exists unsuccessful,
    0 <= unsuccessful /\
    y <= x + 100 * successful - 50 * unsuccessful /\
    ShirtSelection (x + 100 * successful - 50 * unsuccessful) p.

Definition Pre (p x y : Z) : Prop :=
  26 <= p <= 500 /\ 1 <= y <= x /\ x <= 20000 /\
  exists successful, 0 <= successful /\ GoalWithHacks p x y successful.

Definition Spec (p x y out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun successful : Z => 0 <= successful /\ GoalWithHacks p x y successful)
    (fun successful => successful) out.

Definition ShirtTrace (score : Z) (values : list Z) : Prop :=
  Zlength values = 26 /\
  Znth 0 values 0 = (score / 50) mod 475 /\
  forall i, 0 <= i < 25 ->
    Znth (i + 1) values 0 = (Znth i values 0 * 96 + 42) mod 475.

Definition NoShirtSelection (score place : Z) : Prop :=
  ~ ShirtSelection score place.

Definition ShirtScanState
    (score place scanned current : Z) : Prop :=
  exists values,
    ShirtTrace score values /\
    0 <= scanned <= 25 /\
    current = Znth scanned values 0 /\
    (forall i, 1 <= i <= scanned -> place <> 26 + Znth i values 0).

Definition AlignmentSearch (x y score : Z) : Prop :=
  y <= score /\
  forall candidate,
    y <= candidate < score -> (candidate - x) mod 50 <> 0.

Definition CandidateSearch (place x y score : Z) : Prop :=
  y <= score /\
  (score - x) mod 50 = 0 /\
  forall candidate,
    y <= candidate < score ->
    (candidate - x) mod 50 = 0 ->
    NoShirtSelection candidate place.

Definition FirstWinningCandidate (place x y score : Z) : Prop :=
  CandidateSearch place x y score /\ ShirtSelection score place.

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.ZArith.Zquot.
Lemma shirt_trace_prefix_exists__wins_scan :
  forall (score : Z) (n : nat),
    exists values,
      Zlength values = Z.of_nat n + 1 /\
      Znth 0 values 0 = (score / 50) mod 475 /\
      forall i, 0 <= i < Z.of_nat n ->
        Znth (i + 1) values 0 =
          (Znth i values 0 * 96 + 42) mod 475.
Proof.
  intros score n.
  induction n as [|n [values [Hlen [Hseed Hstep]]]].
  - exists (((score / 50) mod 475) :: nil).
    repeat split; try reflexivity.
    intros i Hi. lia.
  - exists (values ++
      (((Znth (Z.of_nat n) values 0 * 96 + 42) mod 475) :: nil)).
    split.
    + rewrite Zlength_app_cons, Hlen. lia.
    + split.
      * rewrite app_Znth1 by (rewrite Hlen; lia).
        exact Hseed.
      * intros i Hi.
        destruct (Z_lt_ge_dec i (Z.of_nat n)) as [Hlt | Hge].
        -- rewrite !app_Znth1 by (rewrite Hlen; lia).
           apply Hstep. lia.
        -- assert (i = Z.of_nat n) by lia.
           subst i.
           rewrite app_Znth2 by (rewrite Hlen; lia).
           rewrite Hlen.
           replace (Z.of_nat n + 1 - (Z.of_nat n + 1)) with 0 by lia.
           rewrite app_Znth1 by (rewrite Hlen; lia).
           reflexivity.
Qed.
Lemma shirt_trace_exists__wins_scan :
  forall score, exists values, ShirtTrace score values.
Proof.
  intros score.
  destruct (shirt_trace_prefix_exists__wins_scan score 25%nat)
    as [values [Hlen [Hseed Hstep]]].
  exists values.
  unfold ShirtTrace.
  repeat split; try exact Hseed; try exact Hstep.
  simpl in Hlen. lia.
Qed.
Lemma shirt_trace_unique_prefix__wins_scan :
  forall score values1 values2,
    ShirtTrace score values1 ->
    ShirtTrace score values2 ->
    forall i, 0 <= i <= 25 ->
      Znth i values1 0 = Znth i values2 0.
Proof.
  intros score values1 values2
    [_ [Hseed1 Hstep1]] [_ [Hseed2 Hstep2]].
  assert (Hnat : forall n : nat, Z.of_nat n <= 25 ->
      Znth (Z.of_nat n) values1 0 = Znth (Z.of_nat n) values2 0).
  {
    intros n.
    induction n as [|n IH]; intros Hbound.
    - simpl. congruence.
    - specialize (IH ltac:(lia)).
      specialize (Hstep1 (Z.of_nat n) ltac:(lia)).
      specialize (Hstep2 (Z.of_nat n) ltac:(lia)).
      replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      rewrite Hstep1, Hstep2, IH.
      reflexivity.
  }
  intros i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by (rewrite Z2Nat.id; lia).
  apply Hnat. lia.
Qed.
Lemma shirt_scan_state_step__wins_scan :
  forall score place i z,
    i < 25 ->
    ShirtScanState score place i z ->
    place <> 26 + ((z * 96 + 42) mod 475) ->
    ShirtScanState score place (i + 1) ((z * 96 + 42) mod 475).
Proof.
  intros score place i z Hi
    [values [Htrace [[Hilo Hihi] [Hz Hnomatch]]]] Hnext.
  exists values.
  split; [exact Htrace |].
  split; [lia |].
  split.
  - destruct Htrace as [_ [_ Hstep]].
    rewrite Hstep by lia.
    rewrite Hz.
    reflexivity.
  - intros j Hj.
    destruct (Z.eq_dec j (i + 1)) as [-> | Hne].
    + destruct Htrace as [_ [_ Hstep]].
      rewrite Hstep by lia.
      rewrite <- Hz.
      exact Hnext.
    + apply Hnomatch. lia.
Qed.
Lemma alignment_search_extend__alignment_search :
  forall x y score,
    AlignmentSearch x y score ->
    Z.rem (score - x) 50 <> 0 ->
    AlignmentSearch x y (score + 1).
Proof.
  intros x y score [Hyscore Hsearch] Hscore_rem.
  assert (Hscore : (score - x) mod 50 <> 0).
  {
    intro Hmod.
    apply Hscore_rem.
    apply (proj2 (Zrem_Zmod_zero (score - x) 50 ltac:(lia))).
    exact Hmod.
  }
  split.
  - lia.
  - intros candidate Hcandidate.
    destruct (Z.lt_ge_cases candidate score) as [Hlt | Hge].
    + apply Hsearch. lia.
    + assert (candidate = score) by lia.
      subst candidate.
      exact Hscore.
Qed.
Lemma alignment_search_full_window__alignment_search :
  forall x y score,
    y <= x ->
    0 <= score - y <= 49 ->
    AlignmentSearch x y score ->
    Z.rem (score - x) 50 <> 0 ->
    score - y < 49.
Proof.
  intros x y score _ Hwindow [Hyscore Hsearch] Hscore_rem.
  assert (Hscore : (score - x) mod 50 <> 0).
  {
    intro Hmod.
    apply Hscore_rem.
    apply (proj2 (Zrem_Zmod_zero (score - x) 50 ltac:(lia))).
    exact Hmod.
  }
  destruct Hwindow as [Hwindow0 Hwindow49].
  destruct (Z.lt_ge_cases (score - y) 49) as [Hlt | Hge].
  - exact Hlt.
  - assert (Hwindoweq : score - y = 49) by lia.
  set (candidate := y + (x - y) mod 50).
  assert (Hmodbound : 0 <= (x - y) mod 50 < 50).
  { apply Z.mod_pos_bound. lia. }
  assert (Hcandidate_mod : (candidate - x) mod 50 = 0).
  {
    unfold candidate.
    replace (y + (x - y) mod 50 - x) with
        ((x - y) mod 50 - (x - y)) by ring.
    rewrite Zminus_mod_idemp_l.
    replace (x - y - (x - y)) with 0 by ring.
    reflexivity.
  }
  assert (Hcandidate_le : candidate <= score).
  { unfold candidate. lia. }
  assert (Hcandidate_ne : candidate <> score).
  {
    intro Heq.
    apply Hscore.
    rewrite <- Heq.
    exact Hcandidate_mod.
  }
  assert (Hcandidate_range : y <= candidate < score).
  { unfold candidate in *. lia. }
  specialize (Hsearch candidate Hcandidate_range).
  contradiction.
Qed.
Lemma alignment_to_candidate_search__alignment_search :
  forall place x y score,
    Z.rem (score - x) 50 = 0 ->
    AlignmentSearch x y score ->
    CandidateSearch place x y score.
Proof.
  intros place x y score Hscore_rem [Hyscore Hsearch].
  assert (Hscore : (score - x) mod 50 = 0).
  {
    apply (proj1 (Zrem_Zmod_zero (score - x) 50 ltac:(lia))).
    exact Hscore_rem.
  }
  unfold CandidateSearch.
  split; [exact Hyscore |].
  split; [exact Hscore |].
  intros candidate Hrange Haligned.
  unfold NoShirtSelection.
  intro Hselection.
  apply (Hsearch candidate Hrange).
  exact Haligned.
Qed.
Lemma shirt_selection_period__candidate_capacity :
  forall score place k,
    ShirtSelection score place ->
    ShirtSelection (score + 50 * 475 * k) place.
Proof.
  intros score place k Hselection.
  unfold ShirtSelection in *.
  destruct Hselection as
      (values & Hlength & Hinitial & Htrace & i & Hi & Hplace).
  exists values.
  split; [exact Hlength |].
  split.
  - rewrite Hinitial.
    replace (score + 50 * 475 * k) with (score + (475 * k) * 50) by ring.
    rewrite Z.div_add by lia.
    replace (score / 50 + 475 * k) with (score / 50 + k * 475) by ring.
    rewrite Z.mod_add by lia.
    reflexivity.
  - split; [exact Htrace |].
    exists i.
    split; assumption.
Qed.
Lemma candidate_search_room__candidate_capacity :
  forall place x y score,
    Pre place x y ->
    NoShirtSelection score place ->
    CandidateSearch place x y score ->
    score <= x + 50 * 475 ->
    score < x + 50 * 475.
Proof.
  intros place x y score Hpre Hcurrent Hsearch Hbound.
  destruct (Z_lt_ge_dec score (x + 50 * 475)) as [Hlt | Hge];
    [exact Hlt |].
  assert (Hscore : score = x + 50 * 475) by lia.
  unfold Pre in Hpre.
  destruct Hpre as
      (Hplace_bounds & Hy_bounds & Hx_upper &
       successful & Hsuccessful & Hgoal).
  destruct Hy_bounds as (Hy_lower & Hyx).
  unfold GoalWithHacks in Hgoal.
  destruct Hgoal as (unsuccessful & Hunsuccessful & Hwinning & Hselection).
  set (turns := 2 * successful - unsuccessful).
  set (candidate := x + 50 * (turns mod 475)).
  assert (Hturns :
      x + 100 * successful - 50 * unsuccessful = x + 50 * turns).
  { unfold turns. ring. }
  rewrite Hturns in Hselection.
  pose proof
    (shirt_selection_period__candidate_capacity
       (x + 50 * turns) place (-(turns / 475)) Hselection)
    as Hnormalized.
  assert (Hnormalize :
      x + 50 * turns + 50 * 475 * (-(turns / 475)) = candidate).
  { unfold candidate.
    pose proof (Z.div_mod turns 475 ltac:(lia)) as Hdivmod.
    lia. }
  rewrite Hnormalize in Hnormalized.
  pose proof (Z.mod_pos_bound turns 475 ltac:(lia)) as Hmod_bounds.
  destruct Hsearch as (Hsearch_lower & Hsearch_aligned & Hsearch_none).
  assert (Hcandidate_bounds : y <= candidate < score).
  { unfold candidate. rewrite Hscore. lia. }
  assert (Hcandidate_aligned : (candidate - x) mod 50 = 0).
  { unfold candidate.
    replace (x + 50 * (turns mod 475) - x)
      with ((turns mod 475) * 50) by ring.
    apply Z.mod_mul.
    lia. }
  specialize (Hsearch_none candidate Hcandidate_bounds Hcandidate_aligned).
  unfold NoShirtSelection in Hsearch_none.
  contradiction.
Qed.
Lemma candidate_search_step__candidate_transitions :
  forall place x y score,
    CandidateSearch place x y score ->
    NoShirtSelection score place ->
    CandidateSearch place x y (score + 50).
Proof.
  intros place x y score Hsearch Hnone.
  unfold CandidateSearch in *.
  destruct Hsearch as [Hy [Hscore Hprior]].
  repeat split.
  - lia.
  - replace (score + 50 - x) with ((score - x) + 50) by ring.
    rewrite Z.add_mod by lia.
    rewrite Hscore.
    reflexivity.
  - intros candidate Hrange Haligned.
    destruct (Z_lt_ge_dec candidate score) as [Hlt | Hge].
    + apply Hprior; lia.
    + assert (Hdiff : (candidate - score) mod 50 = 0).
      {
        replace (candidate - score)
          with ((candidate - x) - (score - x)) by ring.
        rewrite Zminus_mod by lia.
        rewrite Haligned, Hscore.
        reflexivity.
      }
      rewrite Z.mod_small in Hdiff by lia.
      assert (candidate = score) by lia.
      subst candidate.
      exact Hnone.
Qed.
Lemma aligned_gap_at_least_fifty__candidate_transitions :
  forall x lower upper,
    (lower - x) mod 50 = 0 ->
    (upper - x) mod 50 = 0 ->
    lower < upper ->
    lower + 50 <= upper.
Proof.
  intros x lower upper Hlower Hupper Hlt.
  assert (Hdiff : (upper - lower) mod 50 = 0).
  {
    replace (upper - lower) with ((upper - x) - (lower - x)) by ring.
    rewrite Zminus_mod by lia.
    rewrite Hupper, Hlower.
    reflexivity.
  }
  destruct (Z_le_gt_dec 50 (upper - lower)) as [Hlarge | Hsmall].
  - lia.
  - rewrite Z.mod_small in Hdiff by lia.
    lia.
Qed.
Lemma aligned_ceiling_decomposition__final_result :
  forall d : Z,
    0 < d ->
    d mod 50 = 0 ->
    exists unsuccessful,
      0 <= unsuccessful /\
      d = 100 * ((d + 99) / 100) - 50 * unsuccessful /\
      forall successful,
        d <= 100 * successful ->
        (d + 99) / 100 <= successful.
Proof.
  intros d Hd Hmod.
  pose proof (Z.div_mod d 50 ltac:(lia)) as Hd_div.
  pose proof (Z.div_mod (d + 99) 100 ltac:(lia)) as Hceil_div.
  pose proof (Z.mod_pos_bound (d + 99) 100 ltac:(lia)) as Hceil_mod.
  exists (2 * ((d + 99) / 100) - d / 50).
  rewrite Hmod, Z.add_0_r in Hd_div.
  repeat split.
  - nia.
  - nia.
  - intros successful Hsuccessful.
    nia.
Qed.
Lemma first_winning_goal_lower_bound__final_result :
  forall place x y score successful,
    x < score ->
    FirstWinningCandidate place x y score ->
    0 <= successful ->
    GoalWithHacks place x y successful ->
    (score - x + 99) / 100 <= successful.
Proof.
  intros place x y score successful Hpositive Hfirst Hsuccessful Hgoal.
  destruct Hfirst as [[Hy_score [Hscore_mod Hfirst]] Hscore_selection].
  destruct Hgoal as [unsuccessful [Hunsuccessful [Hy_candidate Hcandidate_selection]]].
  assert (Hcandidate_mod :
    (x + 100 * successful - 50 * unsuccessful - x) mod 50 = 0).
  {
    apply Z.mod_divide; [lia |].
    exists (2 * successful - unsuccessful).
    ring.
  }
  assert (Hscore_le : score <= x + 100 * successful - 50 * unsuccessful).
  {
    destruct (Z_lt_ge_dec (x + 100 * successful - 50 * unsuccessful) score)
      as [Hlt | Hge]; [| lia].
    specialize (Hfirst (x + 100 * successful - 50 * unsuccessful)
      ltac:(lia) Hcandidate_mod).
    contradiction.
  }
  destruct (aligned_ceiling_decomposition__final_result
    (score - x) ltac:(lia) Hscore_mod)
    as [unused [_ [_ Hleast]]].
  apply Hleast.
  nia.
Qed.
Lemma zero_success_is_spec__final_result :
  forall place x y score,
    score <= x ->
    y <= score ->
    FirstWinningCandidate place x y score ->
    Spec place x y 0.
Proof.
  intros place x y score Hscore_x Hy_score Hfirst_winning.
  unfold Spec, min_value_of_subset, min_object_of_subset.
  destruct Hfirst_winning as [[_ [Hscore_mod _]] Hselection].
  apply (proj1 (Z.mod_divide (score - x) 50 ltac:(lia))) in Hscore_mod.
  destruct Hscore_mod as [q Hq].
  exists 0.
  split.
  - split.
    + split; [lia |].
      unfold GoalWithHacks.
      exists ((x - score) / 50).
      replace (x - score) with (50 * (-q)) by lia.
      rewrite Z.mul_comm, Z.div_mul by lia.
      repeat split; try lia.
      replace (x + 100 * 0 - 50 * - q) with score by lia.
      exact Hselection.
    + intros successful Hfeasible.
      destruct Hfeasible as [Hnonnegative Hgoal].
      lia.
  - reflexivity.
Qed.
Lemma first_winning_is_spec__final_result :
  forall place x y score,
    x < score ->
    FirstWinningCandidate place x y score ->
    Spec place x y ((score - x + 99) / 100).
Proof.
  intros place x y score Hpositive Hfirst_winning.
  pose proof Hfirst_winning as Hfirst_copy.
  destruct Hfirst_winning as [[Hy_score [Hscore_mod Hfirst]] Hselection].
  destruct (aligned_ceiling_decomposition__final_result
    (score - x) ltac:(lia) Hscore_mod)
    as [unsuccessful [Hunsuccessful [Hdecomposition Hleast]]].
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists ((score - x + 99) / 100).
  split.
  - split.
    + split.
      * apply Z.div_pos; lia.
      * unfold GoalWithHacks.
        exists unsuccessful.
        repeat split; try lia.
        replace
          (x + 100 * ((score - x + 99) / 100) - 50 * unsuccessful)
          with score by lia.
        exact Hselection.
    + intros successful Hfeasible.
      destruct Hfeasible as [Hnonnegative Hgoal].
      eapply first_winning_goal_lower_bound__final_result; eauto.
  - reflexivity.
Qed.
