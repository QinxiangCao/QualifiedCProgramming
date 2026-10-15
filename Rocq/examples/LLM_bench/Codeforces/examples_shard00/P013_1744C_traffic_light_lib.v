Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition WaitsUntilGreen (s : list Z) (start wait : Z) : Prop :=
  0 <= start < Zlength s /\
  min_value_of_subset Z.le
    (fun candidate : Z =>
      0 <= candidate < Zlength s /\
      Znth ((start + candidate) mod Zlength s) s 0 = 103)
    (fun candidate => candidate) wait.

Definition Pre (current : Z) (s : list Z) : Prop :=
  1 <= Zlength s <= 200000 /\
  (current = 114 \/ current = 121 \/ current = 103) /\
  Forall (fun c => c = 114 \/ c = 121 \/ c = 103) s /\
  In 103 s /\ In current s.

Definition Spec (current : Z) (s : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : Z * Z =>
      Znth (fst candidate) s 0 = current /\
      WaitsUntilGreen s (fst candidate) (snd candidate))
    snd out.

(** The character observed at an index of the doubled, cyclic scan. *)
Definition DoubledTrafficChar (s : list Z) (index : Z) : Z :=
  Znth (index mod Zlength s) s 0.

(** [next] is the first green strictly after [i] in the part of the
    conceptual doubled string that has already been scanned.  The [-1]
    case describes the initial empty suffix. *)
Definition FirstProcessedGreen (s : list Z) (i next : Z) : Prop :=
  (next = -1 /\
   forall j,
     i < j < 2 * Zlength s ->
     DoubledTrafficChar s j <> 103) \/
  (i < next < 2 * Zlength s /\
   DoubledTrafficChar s next = 103 /\
   forall j,
     i < j < next ->
     DoubledTrafficChar s j <> 103).

(** [ans] is the greatest circular wait among original-string positions
    already covered by the descending scan.  The default makes the empty
    processed set at loop initialization have value zero. *)
Definition ProcessedTrafficMaximum
    (current : Z) (s : list Z) (i ans : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate : Z * Z =>
      i < fst candidate /\
      Znth (fst candidate) s 0 = current /\
      WaitsUntilGreen s (fst candidate) (snd candidate))
    snd 0 ans.

Definition TrafficScanState
    (current : Z) (s : list Z) (i ans next : Z) : Prop :=
  FirstProcessedGreen s i next /\
  ProcessedTrafficMaximum current s i ans.

Require Import Coq.micromega.Lia.
Lemma traffic_scan_state_initial__initialization :
  forall (current : Z) (lights : list Z),
    1 <= Zlength lights ->
    TrafficScanState current lights (2 * Zlength lights - 1) 0 (-1).
Proof.
  intros current lights Hlength.
  unfold TrafficScanState.
  split.
  - unfold FirstProcessedGreen.
    left.
    split.
    + reflexivity.
    + intros j Hj.
      exfalso.
      lia.
  - unfold ProcessedTrafficMaximum.
    apply max_default_default.
    intros [start wait] Hcandidate.
    destruct Hcandidate as [Hprocessed [_ Hwait]].
    unfold WaitsUntilGreen in Hwait.
    destruct Hwait as [[_ Hstart] _].
    simpl in Hprocessed, Hstart.
    exfalso.
    apply (Z.lt_irrefl start).
    eapply Z.lt_le_trans.
    + exact Hstart.
    + eapply (Z.le_trans _ (2 * Zlength lights - 1) _).
      * lia.
      * apply Z.lt_le_incl.
        exact Hprocessed.
Qed.
Lemma traffic_scan_step_current_raise__current_max_update :
  forall current s i ans next,
    Pre current s ->
    0 <= i < Zlength s ->
    current <> 103 ->
    DoubledTrafficChar s i = current ->
    TrafficScanState current s i ans next ->
    0 <= ans ->
    next - i > ans ->
    TrafficScanState current s (i - 1) (next - i) next /\
    next - i <= Zlength s.
Proof.
  intros current s i ans next Hpre Hi Hcurrent Hchar Hstate Hans Hraise.
  destruct Hpre as [Hlen [_ [_ [Hgreen _]]]].
  destruct Hstate as [Hfirst Hmaximum].
  assert (Hnext_after : i < next).
  {
    destruct Hfirst as [[Hnext _] | [[Hnext _] _]].
    - subst next; lia.
    - exact Hnext.
  }
  assert (Hnext_green : DoubledTrafficChar s next = 103).
  {
    destruct Hfirst as [[Hnext _] | [_ [Hnext_green _]]].
    - subst next; lia.
    - exact Hnext_green.
  }
  assert (Hnext_limit : next < 2 * Zlength s).
  {
    destruct Hfirst as [[Hnext _] | [[_ Hnext_limit] _]].
    - subst next; lia.
    - exact Hnext_limit.
  }
  assert (Hno_green : forall j,
             i < j < next -> DoubledTrafficChar s j <> 103).
  {
    destruct Hfirst as [[Hnext _] | [_ [_ Hno_green]]].
    - subst next; lia.
    - exact Hno_green.
  }
  assert (Hcurrent_at : Znth i s 0 = current).
  {
    unfold DoubledTrafficChar in Hchar.
    rewrite Z.mod_small in Hchar by lia.
    exact Hchar.
  }
  assert (Hdistance_bound : next - i < Zlength s).
  {
    apply In_nth_error in Hgreen.
    destruct Hgreen as [k_nat Hk_nat].
    set (k := Z.of_nat k_nat).
    assert (Hk : 0 <= k < Zlength s).
    {
      assert (Hk_nat_bound : (k_nat < length s)%nat).
      {
        apply nth_error_Some.
        rewrite Hk_nat.
        discriminate.
      }
      unfold k.
      rewrite Zlength_correct.
      lia.
    }
    assert (Hk_green : Znth k s 0 = 103).
    {
      unfold k, Znth.
      rewrite Nat2Z.id.
      apply nth_error_nth with (d := 0) in Hk_nat.
      exact Hk_nat.
    }
    destruct (Z_lt_ge_dec i k) as [Hik | Hki].
    - assert (Hdouble_k : DoubledTrafficChar s k = 103).
      {
        unfold DoubledTrafficChar.
        rewrite Z.mod_small by lia.
        exact Hk_green.
      }
      assert (next <= k).
      {
        destruct (Z_le_gt_dec next k); auto.
        exfalso.
        apply (Hno_green k); [lia | exact Hdouble_k].
      }
      lia.
    - assert (Hki_strict : k < i).
      {
        assert (k <> i).
        {
          intro Hki_eq.
          rewrite Hki_eq in Hk_green.
          rewrite Hcurrent_at in Hk_green.
          contradiction.
        }
        lia.
      }
      assert (Hdouble_kn :
                DoubledTrafficChar s (k + Zlength s) = 103).
      {
        unfold DoubledTrafficChar.
        replace (k + Zlength s) with
          (k + 1 * Zlength s) by lia.
        rewrite Z.mod_add by lia.
        rewrite Z.mod_small by lia.
        exact Hk_green.
      }
      assert (next <= k + Zlength s).
      {
        destruct (Z_le_gt_dec next (k + Zlength s)); auto.
        exfalso.
        apply (Hno_green (k + Zlength s)); [lia | exact Hdouble_kn].
      }
      lia.
  }
  assert (Hwait : WaitsUntilGreen s i (next - i)).
  {
    unfold WaitsUntilGreen.
    split; [exact Hi |].
    unfold min_value_of_subset, min_object_of_subset.
    exists (next - i).
    split.
    - split.
      + split; [lia |].
        replace (i + (next - i)) with next by lia.
        exact Hnext_green.
      + intros candidate [Hcandidate Hcandidate_green].
        destruct (Z_le_gt_dec (next - i) candidate); auto.
        exfalso.
        destruct (Z.eq_dec candidate 0) as [-> | Hcandidate_nonzero].
        * replace (i + 0) with i in Hcandidate_green by lia.
          unfold DoubledTrafficChar in Hchar.
          rewrite Hchar in Hcandidate_green.
          contradiction.
        * apply (Hno_green (i + candidate)); [lia |].
          unfold DoubledTrafficChar.
          exact Hcandidate_green.
    - reflexivity.
  }
  assert (Hfirst_new : FirstProcessedGreen s (i - 1) next).
  {
    right.
    split; [lia |].
    split; [exact Hnext_green |].
    intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hji].
    - rewrite Hchar.
      exact Hcurrent.
    - apply Hno_green.
      lia.
  }
  assert (Hmaximum_new :
            ProcessedTrafficMaximum current s (i - 1) (next - i)).
  {
    unfold ProcessedTrafficMaximum in *.
    replace (next - i) with (le_max Z.le ans (next - i)).
    2:{ rewrite (max_r Z.le) by lia; reflexivity. }
    eapply (max_default_union_1_right Z.le ans (next - i)
              (i, next - i) snd).
    - exact Hmaximum.
    - reflexivity.
    - intros [position wait].
      simpl.
      split.
      + intros [Hposition [Hposition_current Hposition_wait]].
        destruct (Z.eq_dec position i) as [-> | Hposition_neq].
        * right.
          assert (wait = next - i).
          {
            destruct Hposition_wait as [_ Hposition_min].
            destruct Hwait as [_ Hwait_min].
            eapply (min_unique Z.le); eauto.
          }
          subst wait; reflexivity.
        * left.
          split; [lia |].
          split; assumption.
      + intros [[Hposition [Hposition_current Hposition_wait]] | Heq].
        * split; [lia |].
          split; assumption.
        * inversion Heq; subst position wait.
          split; [lia |].
          split; assumption.
  }
  split.
  - split; assumption.
  - lia.
Qed.
Lemma traffic_scan_step_green_noncurrent__green_transition :
  forall (current : Z) (s : list Z) (i ans next : Z),
    0 <= i < Zlength s ->
    DoubledTrafficChar s i = 103 ->
    Znth i s 0 <> current ->
    TrafficScanState current s i ans next ->
    TrafficScanState current s (i - 1) ans i.
Proof.
  intros current s i ans next Hi Hgreen Hnoncurrent Hstate.
  destruct Hstate as [Hfirst Hmaximum].
  split.
  - unfold FirstProcessedGreen.
    right.
    repeat split; try assumption; try lia.
  - unfold ProcessedTrafficMaximum in *.
    eapply (@max_default_eq_forward Z Z.le Zle_TotalOrder (Z * Z)).
    + exact Hmaximum.
    + intros [start wait] Hcandidate.
      exists (start, wait).
      simpl in *.
      destruct Hcandidate as [Hstart [Hchar Hwait]].
      split.
      * split; [lia | split; assumption].
      * lia.
    + intros [start wait] Hcandidate.
      exists (start, wait).
      simpl in *.
      destruct Hcandidate as [Hstart [Hchar Hwait]].
      split.
      * split.
        --
        destruct (Z.eq_dec start i) as [Heq | Hneq].
        ++ subst start. contradiction.
        ++ lia.
        -- split; assumption.
      * lia.
Qed.
Lemma traffic_scan_step_green_outside_original__green_transition :
  forall (current : Z) (s : list Z) (i ans next : Z),
    Zlength s <= i < 2 * Zlength s ->
    DoubledTrafficChar s i = 103 ->
    TrafficScanState current s i ans next ->
    TrafficScanState current s (i - 1) ans i.
Proof.
  intros current s i ans next Hi Hgreen Hstate.
  destruct Hstate as [Hfirst Hmaximum].
  split.
  - unfold FirstProcessedGreen.
    right.
    repeat split; try assumption; try lia.
  - unfold ProcessedTrafficMaximum in *.
    eapply (@max_default_eq_forward Z Z.le Zle_TotalOrder (Z * Z)).
    + exact Hmaximum.
    + intros [start wait] Hcandidate.
      exists (start, wait).
      simpl in *.
      destruct Hcandidate as [Hstart [Hchar Hwait]].
      split.
      * split; [lia | split; assumption].
      * lia.
    + intros [start wait] Hcandidate.
      exists (start, wait).
      simpl in *.
      destruct Hcandidate as [Hstart [Hchar Hwait]].
      split.
      * split.
        -- unfold WaitsUntilGreen in Hwait.
           destruct Hwait as [Hwait_bounds Hwait_min].
           lia.
        -- split; assumption.
      * lia.
Qed.
Lemma first_processed_green_step_nongreen__stable_transition :
  forall s i next,
    FirstProcessedGreen s i next ->
    DoubledTrafficChar s i <> 103 ->
    FirstProcessedGreen s (i - 1) next.
Proof.
  intros s i next Hfirst Hnongreen.
  unfold FirstProcessedGreen in *.
  destruct Hfirst as [[Hnext Hall] | [[Hilt Hnextlt] [Hgreen Hall]]].
  - left. split; [exact Hnext |].
    intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hji].
    + exact Hnongreen.
    + apply Hall. lia.
  - right. split; [lia |]. split; [exact Hgreen |].
    intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hji].
    + exact Hnongreen.
    + apply Hall. lia.
Qed.
Lemma first_processed_green_wait_exact__stable_transition :
  forall s i next wait,
    0 <= i < Zlength s ->
    DoubledTrafficChar s i <> 103 ->
    FirstProcessedGreen s i next ->
    WaitsUntilGreen s i wait ->
    wait = next - i.
Proof.
  intros s i next wait Hi Hnongreen Hfirst Hwait.
  unfold WaitsUntilGreen in Hwait.
  destruct Hwait as [_ Hminimum].
  destruct Hminimum as [candidate [Hobject Hcandidate_eq]].
  destruct Hobject as [Hcandidate Hminimal].
  destruct Hcandidate as [[Hcandidate_lo Hcandidate_hi] Hgreen].
  cbn in Hcandidate_eq.
  subst wait.
  assert (Hcandidate_pos : 0 < candidate).
  { destruct (Z.eq_dec candidate 0) as [-> | Hneq]; [|lia].
    exfalso.
    apply Hnongreen.
    unfold DoubledTrafficChar.
    replace (i + 0) with i in Hgreen by lia.
    exact Hgreen. }
  unfold FirstProcessedGreen in Hfirst.
  destruct Hfirst as [[Hnext Hall] | [[Hilt Hnextlt] [Hnextgreen Hall]]].
  - subst next.
    specialize (Hall (i + candidate) ltac:(lia)).
    unfold DoubledTrafficChar in Hall.
    contradiction.
  - assert (Hnext_le : next <= i + candidate).
    { destruct (Z_lt_ge_dec (i + candidate) next) as [Hbefore | Hafter]; [|lia].
      specialize (Hall (i + candidate) ltac:(lia)).
      unfold DoubledTrafficChar in Hall.
      contradiction. }
    specialize (Hminimal (next - i)).
    assert (Hnext_candidate :
      0 <= next - i < Zlength s /\
      Znth ((i + (next - i)) mod Zlength s) s 0 = 103).
    { split; [lia |].
      replace (i + (next - i)) with next by lia.
      exact Hnextgreen. }
    specialize (Hminimal Hnext_candidate).
    lia.
Qed.
Lemma traffic_scan_step_noncurrent_nongreen__stable_transition :
  forall current s i ans next,
    0 <= i < Zlength s ->
    Znth i s 0 <> current ->
    DoubledTrafficChar s i <> 103 ->
    TrafficScanState current s i ans next ->
    TrafficScanState current s (i - 1) ans next.
Proof.
  intros current s i ans next Hi Hnoncurrent Hnongreen [Hfirst Hmaximum].
  split.
  - eapply first_processed_green_step_nongreen__stable_transition; eauto.
  - unfold ProcessedTrafficMaximum in *.
    eapply (max_default_eq_forward Z.le).
    + exact Hmaximum.
    + intros [p w] [Hip [Hpcurrent Hpwait]].
      exists (p, w). cbn in *. split.
      * split; [lia |]. split; [exact Hpcurrent | exact Hpwait].
      * lia.
    + intros [p w] [Hip [Hpcurrent Hpwait]].
      cbn in Hip, Hpcurrent, Hpwait.
      assert (Hip_old : i < p).
      { destruct (Z_lt_ge_dec i p) as [Hlt | Hge]; [exact Hlt |].
        assert (p = i) by lia. subst p. contradiction. }
      exists (p, w). cbn in *. split.
      * split; [exact Hip_old |]. split; [exact Hpcurrent | exact Hpwait].
      * lia.
Qed.
Lemma traffic_scan_step_nongreen_outside_original__stable_transition :
  forall current s i ans next,
    Zlength s <= i ->
    DoubledTrafficChar s i <> 103 ->
    TrafficScanState current s i ans next ->
    TrafficScanState current s (i - 1) ans next.
Proof.
  intros current s i ans next Hi Hnongreen [Hfirst Hmaximum].
  split.
  - eapply first_processed_green_step_nongreen__stable_transition; eauto.
  - unfold ProcessedTrafficMaximum in *.
    eapply (max_default_eq_forward Z.le).
    + exact Hmaximum.
    + intros [p w] [Hip [Hpcurrent Hpwait]].
      exists (p, w). cbn in *. split.
      * split; [lia |]. split; [exact Hpcurrent | exact Hpwait].
      * lia.
    + intros [p w] [Hip [Hpcurrent Hpwait]].
      cbn in Hip, Hpcurrent, Hpwait.
      assert (Hip_old : i < p).
      { destruct (Z_lt_ge_dec i p) as [Hlt | Hge]; [exact Hlt |].
        assert (p = i) by lia. subst p.
        unfold WaitsUntilGreen in Hpwait. lia. }
      exists (p, w). cbn in *. split.
      * split; [exact Hip_old |]. split; [exact Hpcurrent | exact Hpwait].
      * lia.
Qed.
Lemma traffic_scan_step_current_keep__stable_transition :
  forall current s i ans next,
    0 <= i < Zlength s ->
    DoubledTrafficChar s i <> 103 ->
    next - i <= ans ->
    TrafficScanState current s i ans next ->
    TrafficScanState current s (i - 1) ans next.
Proof.
  intros current s i ans next Hi Hnongreen Hbound [Hfirst Hmaximum].
  split.
  - eapply first_processed_green_step_nongreen__stable_transition; eauto.
  - unfold ProcessedTrafficMaximum in *.
    destruct Hmaximum as [[Hmaximum Hdefault] | [Hall Hdefault]].
    + left. split; [| exact Hdefault].
      destruct Hmaximum as [[p w] [Hobject Hweq]].
      destruct Hobject as [Hmember Hupper].
      destruct Hmember as [Hip [Hpcurrent Hpwait]].
      change (i < p) in Hip.
      change (Znth p s 0 = current) in Hpcurrent.
      change (WaitsUntilGreen s p w) in Hpwait.
      change (w = ans) in Hweq.
      exists (p, w). split.
      * split.
        -- change (i - 1 < p /\
                   Znth p s 0 = current /\
                   WaitsUntilGreen s p w).
           split; [lia |]. split; [exact Hpcurrent | exact Hpwait].
        -- intros [q v] [Hiq [Hqcurrent Hqwait]]. cbn in *.
           destruct (Z_lt_ge_dec i q) as [Hlt | Hge].
           ++ specialize (Hupper (q, v)). cbn in Hupper.
              apply Hupper. split; [exact Hlt |].
              split; [exact Hqcurrent | exact Hqwait].
           ++ assert (q = i) by lia. subst q.
              rewrite (first_processed_green_wait_exact__stable_transition
                         s i next v Hi Hnongreen Hfirst Hqwait).
              rewrite Hweq. exact Hbound.
      * exact Hweq.
    + right. split; [| exact Hdefault].
      intros [q v] [Hiq [Hqcurrent Hqwait]]. cbn in *.
      destruct (Z_lt_ge_dec i q) as [Hlt | Hge].
      * specialize (Hall (q, v)). cbn in Hall.
        apply Hall. split; [exact Hlt |].
        split; [exact Hqcurrent | exact Hqwait].
      * assert (q = i) by lia. subst q.
        rewrite (first_processed_green_wait_exact__stable_transition
                   s i next v Hi Hnongreen Hfirst Hqwait).
        rewrite <- Hdefault in Hbound. exact Hbound.
Qed.
Lemma in_Znth_exists__final_results :
  forall (x default : Z) (s : list Z),
    In x s ->
    exists i, 0 <= i < Zlength s /\ Znth i s default = x.
Proof.
  intros x default s.
  induction s as [| a s IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst a.
      exists 0.
      split.
      * rewrite Zlength_cons.
        pose proof (Zlength_nonneg s).
        lia.
      * apply Znth0_cons.
    + destruct (IH Hin) as [i [[Hi0 HiN] Hnth]].
      exists (i + 1).
      split.
      * rewrite Zlength_cons.
        lia.
      * rewrite Znth_cons by lia.
        replace (i + 1 - 1) with i by lia.
        exact Hnth.
Qed.
Lemma waits_until_green_exists__final_results :
  forall (s : list Z) (start : Z),
    0 <= start < Zlength s ->
    In 103 s ->
    exists wait, WaitsUntilGreen s start wait.
Proof.
  intros s start Hstart Hgreen_in.
  destruct (in_Znth_exists__final_results 103 0 s Hgreen_in)
    as [green [[Hgreen0 HgreenN] Hgreen_char]].
  assert (Hlen : 0 < Zlength s) by lia.
  set (first_wait := (green - start) mod Zlength s).
  assert (Hfirst_range : 0 <= first_wait < Zlength s).
  { unfold first_wait.
    apply Z.mod_pos_bound.
    lia. }
  assert (Hfirst_green :
    Znth ((start + first_wait) mod Zlength s) s 0 = 103).
  { unfold first_wait.
    rewrite Z.add_mod_idemp_r by lia.
    replace (start + (green - start)) with green by lia.
    rewrite Z.mod_small by lia.
    exact Hgreen_char. }
  destruct (min_n_in_range
    (fun wait => Znth ((start + wait) mod Zlength s) s 0 = 103)
    (Zlength s - 1)) as
    [wait [Hwait_green [[Hwait0 HwaitN] Hwait_min]]].
  - lia.
  - exists first_wait.
    split.
    + lia.
    + exact Hfirst_green.
  - exists wait.
    unfold WaitsUntilGreen.
    split; [exact Hstart |].
    unfold min_value_of_subset, min_object_of_subset.
    exists wait.
    split.
    + split.
      * split; [lia | exact Hwait_green].
      * intros candidate [Hcandidate_range Hcandidate_green].
        apply Hwait_min; [lia | exact Hcandidate_green].
    + reflexivity.
Qed.
Lemma waits_until_green_nonnegative__final_results :
  forall (s : list Z) (start wait : Z),
    WaitsUntilGreen s start wait ->
    0 <= wait.
Proof.
  intros s start wait Hwait.
  unfold WaitsUntilGreen, min_value_of_subset,
    min_object_of_subset in Hwait.
  destruct Hwait as
    [_ [candidate [[[[Hcandidate0 HcandidateN] Hcandidate_green]
                    Hcandidate_min] Hcandidate_eq]]].
  simpl in Hcandidate_eq.
  lia.
Qed.
Lemma waits_until_green_zero_if_start_green__final_results :
  forall (s : list Z) (start wait : Z),
    0 <= start < Zlength s ->
    Znth start s 0 = 103 ->
    WaitsUntilGreen s start wait ->
    wait = 0.
Proof.
  intros s start wait Hstart Hstart_green Hwait.
  assert (Hlen : 0 < Zlength s) by lia.
  unfold WaitsUntilGreen, min_value_of_subset,
    min_object_of_subset in Hwait.
  destruct Hwait as
    [_ [candidate [[[[Hcandidate0 HcandidateN] Hcandidate_green]
                    Hcandidate_min] Hcandidate_eq]]].
  simpl in Hcandidate_eq.
  assert (Hzero_green :
    0 <= 0 < Zlength s /\
    Znth ((start + 0) mod Zlength s) s 0 = 103).
  { split; [lia |].
    replace (start + 0) with start by lia.
    rewrite Z.mod_small by lia.
    exact Hstart_green. }
  specialize (Hcandidate_min 0 Hzero_green).
  lia.
Qed.
Lemma traffic_scan_exit_implies_spec__final_results :
  forall (current : Z) (lights : list Z) (i ans next : Z),
    -1 <= i < 0 ->
    Pre current lights ->
    TrafficScanState current lights i ans next ->
    Spec current lights ans.
Proof.
  intros current lights i ans next Hi Hpre Hstate.
  assert (Hi_eq : i = -1) by lia.
  subst i.
  unfold TrafficScanState in Hstate.
  destruct Hstate as [_ Hmaximum].
  unfold ProcessedTrafficMaximum,
    max_value_of_subset_with_default in Hmaximum.
  destruct Hmaximum as [[Hmaximum Hans_nonnegative] | [Hall Hans]].
  - unfold Spec, max_value_of_subset, max_object_of_subset in *.
    destruct Hmaximum as [candidate [[Hcandidate Hgreatest] Heq]].
    exists candidate.
    split.
    + split.
      * exact (proj2 Hcandidate).
      * intros other Hother.
        apply Hgreatest.
        destruct Hother as [Hother_char Hother_wait].
        split.
        -- pose proof (proj1 Hother_wait) as Hother_start.
           lia.
        -- split; assumption.
    + exact Heq.
  - subst ans.
    unfold Pre in Hpre.
    destruct Hpre as
      [Hlength [Hcurrent_kind [Hchars [Hgreen_in Hcurrent_in]]]].
    destruct (in_Znth_exists__final_results current 0 lights Hcurrent_in)
      as [start [[Hstart0 HstartN] Hstart_char]].
    destruct (waits_until_green_exists__final_results
      lights start (conj Hstart0 HstartN) Hgreen_in)
      as [wait Hwait].
    assert (Hwait_le : wait <= 0).
    { apply (Hall (start, wait)).
      change (-1 < start /\
        Znth start lights 0 = current /\
        WaitsUntilGreen lights start wait).
      split; [lia |].
      split; assumption. }
    assert (Hwait_nonnegative : 0 <= wait).
    { eapply waits_until_green_nonnegative__final_results.
      exact Hwait. }
    assert (Hwait_eq : wait = 0) by lia.
    unfold Spec, max_value_of_subset, max_object_of_subset.
    exists (start, wait).
    split.
    + split.
      * simpl.
        split; assumption.
      * intros other Hother.
        destruct Hother as [Hother_char Hother_wait].
        simpl in *.
        assert (Hother_le : snd other <= 0).
        { apply (Hall other).
          change (-1 < fst other /\
            Znth (fst other) lights 0 = current /\
            WaitsUntilGreen lights (fst other) (snd other)).
          split.
          - pose proof (proj1 Hother_wait) as Hother_start.
            lia.
          - split; assumption. }
        lia.
    + simpl.
      exact Hwait_eq.
Qed.
Lemma green_current_spec_zero__final_results :
  forall (lights : list Z),
    Pre 103 lights ->
    Spec 103 lights 0.
Proof.
  intros lights Hpre.
  unfold Pre in Hpre.
  destruct Hpre as
    [Hlength [Hcurrent_kind [Hchars [Hgreen_in Hcurrent_in]]]].
  destruct (in_Znth_exists__final_results 103 0 lights Hgreen_in)
    as [start [[Hstart0 HstartN] Hstart_green]].
  assert (Hzero_wait : WaitsUntilGreen lights start 0).
  { unfold WaitsUntilGreen, min_value_of_subset, min_object_of_subset.
    split; [lia |].
    exists 0.
    split.
    + split.
      * split.
        -- lia.
        -- replace (start + 0) with start by lia.
           rewrite Z.mod_small by lia.
           exact Hstart_green.
      * intros candidate [[Hcandidate0 HcandidateN] Hcandidate_green].
        lia.
    + reflexivity. }
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists (start, 0).
  split.
  - split.
    + simpl.
      split; assumption.
    + intros candidate Hcandidate.
      destruct candidate as [candidate_start candidate_wait].
      simpl in *.
      destruct Hcandidate as [Hcandidate_green Hcandidate_waits].
      pose proof
        (waits_until_green_zero_if_start_green__final_results
           lights candidate_start candidate_wait
           (proj1 Hcandidate_waits) Hcandidate_green Hcandidate_waits).
      lia.
  - reflexivity.
Qed.
