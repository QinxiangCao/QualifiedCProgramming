Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition SimplifiedExams (a : list Z) (k : Z) (result : list Z) : Prop :=
  exists chosen : Z -> Prop,
    (forall i, chosen i -> 0 <= i < Zlength a) /\
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) <= k /\
    Zlength result = Zlength a /\
    forall i, 0 <= i < Zlength a ->
      Znth i result 0 = if prop_dec (chosen i) then 0 else Znth i a 0.

Definition ExamSadness (a : list Z) (sadness : Z) : Prop :=
  sadness = #(fun i : Z =>
    0 <= i < Zlength a - 1 /\
    Z.gcd (Znth i a 0) (Znth (i+1) a 0) = 1).

Definition Pre (k : Z) (a : list Z) : Prop :=
  1 <= k <= Zlength a /\ Zlength a <= 100000 /\
  Forall (fun x => 0 <= x <= 1000000000) a.

Definition Spec (k : Z) (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      SimplifiedExams a k (fst candidate) /\
      ExamSadness (fst candidate) (snd candidate)) snd out.

Require Import Coq.Sorting.Permutation.
Import ListNotations.

Definition GcdResult (x y result : Z) : Prop :=
  result = Z.gcd x y.

Definition MinValue (x y result : Z) : Prop :=
  result = Z.min x y.

Definition AllOnePrefix (a : list Z) (hi flag : Z) : Prop :=
  (flag = 1 /\ forall j, 0 <= j < hi -> Znth j a 0 = 1) \/
  (flag = 0 /\ exists j, 0 <= j < hi /\ Znth j a 0 <> 1).

Definition AdjacentCoprime (a : list Z) (i : Z) : Prop :=
  0 <= i < Zlength a - 1 /\
  Z.gcd (Znth i a 0) (Znth (i + 1) a 0) = 1.

Definition CoprimeEdgePrefixCount
    (a : list Z) (hi count : Z) : Prop :=
  count = #(fun i : Z => 0 <= i < hi /\ AdjacentCoprime a i).

Definition NonOnePairCenter (a : list Z) (hi center : Z) : Prop :=
  1 <= center < hi - 1 /\
  Znth (center - 1) a 0 <> 1 /\
  Znth center a 0 <> 1 /\
  Znth (center + 1) a 0 <> 1 /\
  AdjacentCoprime a (center - 1) /\
  AdjacentCoprime a center.

Definition PairCenterSelection
    (a : list Z) (hi : Z) (chosen : Z -> Prop) : Prop :=
  (forall center, chosen center -> NonOnePairCenter a hi center) /\
  (forall x y, chosen x -> chosen y -> x <> y -> 2 <= Z.abs (x - y)).

Definition PairSavingsPrefix (a : list Z) (hi savings : Z) : Prop :=
  max_value_of_subset Z.le
    (fun chosen : Z -> Prop => PairCenterSelection a hi chosen)
    (fun chosen => #(fun center : Z =>
       1 <= center < hi - 1 /\ chosen center)) savings.

Definition PairSavingsScan
    (a : list Z) (hi committed pending savings : Z) : Prop :=
  savings = committed + pending / 2 /\
  0 <= pending < hi /\
  PairSavingsPrefix a hi savings.

Definition PairRunSuffix (a : list Z) (hi pending : Z) : Prop :=
  let start := hi - pending - 1 in
  0 <= start < hi /\
  (forall j, start <= j < hi -> Znth j a 0 <> 1) /\
  (forall j, start <= j < hi - 1 -> AdjacentCoprime a j) /\
  (start = 0 \/ Znth (start - 1) a 0 = 1 \/
    ~ AdjacentCoprime a (start - 1)).

Definition InteriorOneBlock (a : list Z) (lo hi : Z) : Prop :=
  0 < lo < hi /\ hi < Zlength a /\
  Znth (lo - 1) a 0 <> 1 /\ Znth hi a 0 <> 1 /\
  forall j, lo <= j < hi -> Znth j a 0 = 1.

Definition InteriorOneRunPrefix
    (a : list Z) (limit : Z) (lengths : list Z) : Prop :=
  exists starts,
    Zlength starts = Zlength lengths /\
    ListLib.increasing starts /\
    (forall q, 0 <= q < Zlength lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q lengths 0) /\
      Znth q starts 0 + Znth q lengths 0 <= limit) /\
    (forall lo hi, InteriorOneBlock a lo hi -> hi <= limit ->
      exists q, 0 <= q < Zlength lengths /\
        Znth q starts 0 = lo /\ Znth q lengths 0 = hi - lo).

Definition OneRunScanState
    (a : list Z) (lo next : Z) (lengths : list Z) : Prop :=
  InteriorOneRunPrefix a lo lengths /\
  (forall j, lo <= j < next -> Znth j a 0 = 1).

Definition GreedyBlockState
    (sorted : list Z) (next budget initial_sad remaining sadness : Z) : Prop :=
  0 <= next <= Zlength sorted /\
  remaining = budget - ListLib.sum (sublist 0 next sorted) /\
  sadness = initial_sad -
    ListLib.sum (map (fun len => len + 1) (sublist 0 next sorted)) /\
  (forall j, 0 <= j < next ->
    Znth j sorted 0 <=
      budget - ListLib.sum (sublist 0 j sorted)).

Definition FinalBudgetResult
    (remaining sadness out : Z) : Prop :=
  out = Z.max 0 (sadness - Z.min remaining sadness).

Definition ExamOptimizationSummary
    (a : list Z) (base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  ExamSadness a base_sad /\
  PairSavingsPrefix a (Zlength a) pair_savings /\
  InteriorOneRunPrefix a (Zlength a) block_lengths /\
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    Spec original_k a out.

Definition OptimizationSafetyBounds
    (base_sad pair_savings : Z) (block_lengths : list Z) : Prop :=
  0 <= pair_savings /\
  Forall (fun len => 1 <= len) block_lengths /\
  2 * pair_savings +
    ListLib.sum (map (fun len => len + 1) block_lengths) <= base_sad.

(** A concrete joint witness for the savings already discovered by the two
    structural scans.  Unlike the two independent summary predicates above,
    this predicate fixes one maximum set of pair centres and one ordered list
    of one-block starts at the same time, and records that their covered edge
    intervals are disjoint.  The numeric prefix bound is therefore a genuine
    charging invariant, not merely a later arithmetic assertion. *)
Definition JointPairBlockPrefix
    (a : list Z) (limit base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  PairSavingsPrefix a (Zlength a) pair_savings /\
  InteriorOneRunPrefix a limit block_lengths /\
  0 <= pair_savings /\
  Forall (fun len => 1 <= len) block_lengths /\
  2 * pair_savings +
    ListLib.sum (map (fun len => len + 1) block_lengths) <= base_sad /\
  exists (centres : Z -> Prop) (starts : list Z),
    PairCenterSelection a (Zlength a) centres /\
    #(fun center : Z =>
        1 <= center < Zlength a - 1 /\ centres center) = pair_savings /\
    Zlength starts = Zlength block_lengths /\
    ListLib.increasing starts /\
    (forall q, 0 <= q < Zlength block_lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q block_lengths 0) /\
      Znth q starts 0 + Znth q block_lengths 0 <= limit) /\
    (forall center q,
      centres center -> 0 <= q < Zlength block_lengths ->
      center < Znth q starts 0 - 1 \/
      Znth q starts 0 + Znth q block_lengths 0 < center).

Definition ExamOptimalityEvidence
    (a : list Z) (original_k out : Z) : Prop :=
  exists result,
    SimplifiedExams a original_k result /\
    ExamSadness result out /\
    forall other other_sadness,
      SimplifiedExams a original_k other ->
      ExamSadness other other_sadness ->
      out <= other_sadness.

(** The exchange certificate deliberately exposes both halves of optimality:
    construction of an attainable stopped-greedy value and the charging lower
    bound against every admissible simplification. *)
Definition ExamJointOptimizationCertificate
    (a : list Z) (base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  JointPairBlockPrefix a (Zlength a) base_sad pair_savings block_lengths /\
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    ExamOptimalityEvidence a original_k out.

Lemma exam_joint_optimization_certificate_projects :
  forall a base_sad pair_savings block_lengths,
    ExamSadness a base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    InteriorOneRunPrefix a (Zlength a) block_lengths ->
    ExamJointOptimizationCertificate
      a base_sad pair_savings block_lengths ->
    OptimizationSafetyBounds base_sad pair_savings block_lengths /\
    ExamOptimizationSummary a base_sad pair_savings block_lengths.
Proof.
  intros a base_sad pair_savings block_lengths
    Hsad Hpair Hblocks [Hjoint Hexchange].
  destruct Hjoint as
    [_ [_ [Hpair_nonneg [Hlengths_pos [Hbenefit_bound _]]]]].
  split.
  - repeat split; assumption.
  - repeat split; try assumption.
    intros original_k sorted use next remaining sadness out
      Hk Hperm Hinc Huse Hgreedy Hstop Hfinal.
    specialize (Hexchange original_k sorted use next remaining sadness out
      Hk Hperm Hinc Huse Hgreedy Hstop Hfinal).
    destruct Hexchange as [result [Hfeasible [Hresult_sad Hlower]]].
    unfold Spec, min_value_of_subset.
    exists (result, out).
    split.
    + unfold min_object_of_subset.
      split.
      * simpl. split; assumption.
      * intros [other other_sadness] Hother.
        simpl in *.
        destruct Hother as [Hother_feasible Hother_sad].
        eapply Hlower; eauto.
    + reflexivity.
Qed.

Require Import Coq.micromega.Lia.

(** A competitor is restricted at a scan prefix when it does not completely
    erase an interior one-block whose right boundary has not yet been reached.
    This is the stable semantic distinction made by the second structural
    scan: completed blocks are available for the extra one-edge saving, while
    every later block must still leave at least one of its one entries
    unchosen. *)
Definition RestrictedSimplifiedExams
    (a : list Z) (limit k : Z) (result : list Z) : Prop :=
  exists chosen : Z -> Prop,
    (forall i, chosen i -> 0 <= i < Zlength a) /\
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) <= k /\
    Zlength result = Zlength a /\
    (forall i, 0 <= i < Zlength a ->
      Znth i result 0 = if prop_dec (chosen i) then 0 else Znth i a 0) /\
    forall lo hi,
      InteriorOneBlock a lo hi -> limit < hi ->
      exists j, lo <= j < hi /\ ~ chosen j.

Definition ExamRestrictedOptimalityEvidence
    (a : list Z) (limit original_k out : Z) : Prop :=
  exists result,
    SimplifiedExams a original_k result /\
    ExamSadness result out /\
    forall other other_sadness,
      RestrictedSimplifiedExams a limit original_k other ->
      ExamSadness other other_sadness ->
      out <= other_sadness.

(** Universal exchange/charging state owned by the one-block scan.  The
    restriction weakens monotonically as [limit] advances and disappears at
    the full-array limit. *)
Definition ExamCompetitorChargingPrefix
    (a : list Z) (limit base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    ExamRestrictedOptimalityEvidence a limit original_k out.

Lemma simplified_exams_at_full_limit_is_restricted :
  forall a k result,
    SimplifiedExams a k result ->
    RestrictedSimplifiedExams a (Zlength a) k result.
Proof.
  intros a k result
    [chosen [Hrange [Hcard [Hlength Hvalues]]]].
  exists chosen.
  split; [exact Hrange |].
  split; [exact Hcard |].
  split; [exact Hlength |].
  split; [exact Hvalues |].
  intros lo hi Hblock Hlater.
  unfold InteriorOneBlock in Hblock.
  lia.
Qed.

(** At the end of the second structural scan the prefix restriction is empty,
    so the maintained charging state supplies precisely the universal field
    of the frozen joint certificate. *)
Lemma exam_competitor_charging_prefix_full_projects :
  forall a base_sad pair_savings block_lengths,
    JointPairBlockPrefix a (Zlength a)
      base_sad pair_savings block_lengths ->
    ExamCompetitorChargingPrefix a (Zlength a)
      base_sad pair_savings block_lengths ->
    ExamJointOptimizationCertificate
      a base_sad pair_savings block_lengths.
Proof.
  intros a base_sad pair_savings block_lengths Hjoint Hcharging.
  split; [exact Hjoint |].
  intros original_k sorted use next remaining sadness out
    Hk Hperm Hinc Huse Hgreedy Hstop Hfinal.
  specialize (Hcharging original_k sorted use next remaining sadness out
    Hk Hperm Hinc Huse Hgreedy Hstop Hfinal).
  destruct Hcharging as [result [Hresult [Hsad Hlower]]].
  exists result.
  split; [exact Hresult |].
  split; [exact Hsad |].
  intros other other_sadness Hother Hother_sadness.
  apply (Hlower other other_sadness).
  - apply simplified_exams_at_full_limit_is_restricted.
    exact Hother.
  - exact Hother_sadness.
Qed.

(** A future-aware certificate for the one-block collection phase.  Rather
    than assigning the final greedy answer to the blocks already discovered
    at a cursor (which is unsound in the presence of zero endpoints), it
    quantifies over every suffix completing the current prefix to the exact
    full interior-block profile. *)
Definition ExamBlockCollectionCertificate
    (a : list Z) (base_sad pair_savings : Z)
    (collected : list Z) : Prop :=
  forall future,
    InteriorOneRunPrefix a (Zlength a) (collected ++ future) ->
    ExamJointOptimizationCertificate
      a base_sad pair_savings (collected ++ future).

Lemma exam_block_collection_certificate_append :
  forall a base_sad pair_savings collected len,
    ExamBlockCollectionCertificate
      a base_sad pair_savings collected ->
    ExamBlockCollectionCertificate
      a base_sad pair_savings (collected ++ [len]).
Proof.
  intros a base_sad pair_savings collected len Hcert future Hprofile.
  unfold ExamBlockCollectionCertificate in Hcert.
  specialize (Hcert (len :: future)).
  rewrite <- app_assoc in Hprofile.
  simpl in Hprofile.
  specialize (Hcert Hprofile).
  rewrite <- app_assoc.
  simpl.
  exact Hcert.
Qed.

Lemma exam_block_collection_certificate_full_projects :
  forall a base_sad pair_savings collected,
    InteriorOneRunPrefix a (Zlength a) collected ->
    ExamBlockCollectionCertificate
      a base_sad pair_savings collected ->
    ExamJointOptimizationCertificate
      a base_sad pair_savings collected.
Proof.
  intros a base_sad pair_savings collected Hprofile Hcert.
  unfold ExamBlockCollectionCertificate in Hcert.
  specialize (Hcert nil).
  rewrite app_nil_r in Hcert.
  exact (Hcert Hprofile).
Qed.

(** A simplification restricted to indices strictly before [limit].  This is
    the competitor family that the one-block scan can soundly grow: the inner
    one-run loop keeps the limit at the run start, and the outer loop advances
    it only after the complete run (and its all-or-nothing bonus) is known. *)
Definition PrefixSimplifiedExams
    (a : list Z) (limit k : Z) (result : list Z) : Prop :=
  exists chosen : Z -> Prop,
    (forall i, chosen i -> 0 <= i < Zlength a) /\
    (forall i, chosen i -> i < limit) /\
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) <= k /\
    Zlength result = Zlength a /\
    forall i, 0 <= i < Zlength a ->
      Znth i result 0 =
        if prop_dec (chosen i) then 0 else Znth i a 0.

(** The scan owns only the universal lower-bound half of optimality.  Unlike
    [ExamCompetitorChargingPrefix], this state does not claim that the
    temporary value for an incomplete block profile is already attainable. *)
Definition ExamPrefixLowerBound
    (a : list Z) (limit base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  limit = 0 \/
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    forall other other_sadness,
      PrefixSimplifiedExams a limit original_k other ->
      ExamSadness other other_sadness ->
      out <= other_sadness.

(** The constructive half is deliberately requested only after the exact full
    block profile has been collected. *)
Definition ExamGreedyAttainability
    (a : list Z) (base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    exists result,
      SimplifiedExams a original_k result /\ ExamSadness result out.

Lemma prefix_simplified_exams_full :
  forall a k result,
    SimplifiedExams a k result ->
    PrefixSimplifiedExams a (Zlength a) k result.
Proof.
  intros a k result
    [chosen [Hrange [Hcard [Hlength Hvalues]]]].
  exists chosen.
  split; [exact Hrange |].
  split.
  - intros idx Hidx. specialize (Hrange idx Hidx). lia.
  - split; [exact Hcard |].
    split; assumption.
Qed.

Lemma set_card_iff__exam_bridge :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros x.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
            1 + fold_right (fun _ acc => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.

Lemma coprime_edge_full_is_exam_sadness :
  forall a count,
    CoprimeEdgePrefixCount a (Zlength a - 1) count ->
    ExamSadness a count.
Proof.
  intros a count Hcount.
  unfold CoprimeEdgePrefixCount in Hcount.
  unfold ExamSadness.
  rewrite Hcount.
  apply set_card_iff__exam_bridge.
  intros i.
  unfold AdjacentCoprime.
  tauto.
Qed.

Lemma exam_prefix_lower_bound_zero :
  forall a base_sad pair_savings,
    ExamPrefixLowerBound a 0 base_sad pair_savings nil.
Proof.
  intros a base_sad pair_savings.
  unfold ExamPrefixLowerBound.
  left. reflexivity.
Qed.

Lemma exam_prefix_completion_projects :
  forall a base_sad pair_savings block_lengths,
    0 < Zlength a ->
    ExamSadness a base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    InteriorOneRunPrefix a (Zlength a) block_lengths ->
    ExamPrefixLowerBound a (Zlength a)
      base_sad pair_savings block_lengths ->
    ExamGreedyAttainability a base_sad pair_savings block_lengths ->
    ExamOptimizationSummary a base_sad pair_savings block_lengths.
Proof.
  intros a base_sad pair_savings block_lengths
    Hlength Hbase Hpair Hblocks Hlower Hattain.
  unfold ExamPrefixLowerBound in Hlower.
  destruct Hlower as [Hzero | Hlower]; [lia |].
  repeat split; try assumption.
  intros original_k sorted use next remaining sadness out
    Hk Hperm Hinc Huse Hgreedy Hstop Hfinal.
  specialize (Hattain original_k sorted use next remaining sadness out
    Hk Hperm Hinc Huse Hgreedy Hstop Hfinal).
  destruct Hattain as [result [Hresult Hresult_sadness]].
  unfold Spec, min_value_of_subset.
  exists (result, out).
  split.
  - unfold min_object_of_subset.
    split.
    + simpl. split; assumption.
    + intros [other other_sadness] [Hother Hother_sadness].
      simpl in *.
      eapply (Hlower original_k sorted use next remaining sadness out
        Hk Hperm Hinc Huse Hgreedy Hstop Hfinal other other_sadness).
      * apply prefix_simplified_exams_full. exact Hother.
      * exact Hother_sadness.
  - reflexivity.
Qed.

(** Canonical form of the interior-one-block profile.  The legacy
    [InteriorOneRunPrefix] deliberately used nondecreasing starts; the strict
    order here records each maximal block at most once and therefore rules out
    duplicate occurrences of the same block. *)
Definition CanonicalInteriorOneRunPrefix
    (a : list Z) (limit : Z) (lengths : list Z) : Prop :=
  exists starts,
    Zlength starts = Zlength lengths /\
    mono_inc starts /\
    (forall q, 0 <= q < Zlength lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q lengths 0) /\
      Znth q starts 0 + Znth q lengths 0 <= limit) /\
    (forall lo hi, InteriorOneBlock a lo hi -> hi <= limit ->
      exists q, 0 <= q < Zlength lengths /\
        Znth q starts 0 = lo /\ Znth q lengths 0 = hi - lo).

Definition CanonicalOneRunScanState
    (a : list Z) (lo next : Z) (lengths : list Z) : Prop :=
  CanonicalInteriorOneRunPrefix a lo lengths /\
  (forall j, lo <= j < next -> Znth j a 0 = 1).

(** The future certificate ranges only over canonical full profiles.  This is
    exactly the family produced by the left-to-right maximal-run scan. *)
Definition CanonicalExamBlockCollectionCertificate
    (a : list Z) (base_sad pair_savings : Z)
    (collected : list Z) : Prop :=
  forall future,
    CanonicalInteriorOneRunPrefix
      a (Zlength a) (collected ++ future) ->
    ExamJointOptimizationCertificate
      a base_sad pair_savings (collected ++ future).

Lemma canonical_interior_one_run_prefix_projects :
  forall a limit lengths,
    CanonicalInteriorOneRunPrefix a limit lengths ->
    InteriorOneRunPrefix a limit lengths.
Proof.
  intros a limit lengths
    [starts [Hlength [Hstrict [Hblocks Hcomplete]]]].
  unfold InteriorOneRunPrefix.
  exists starts.
  split; [exact Hlength |].
  split.
  - apply (proj1 (mono_nondec_iff_increasing starts)).
    apply mono_inc_nondec.
    exact Hstrict.
  - split; assumption.
Qed.

Lemma canonical_one_run_scan_state_projects :
  forall a lo next lengths,
    CanonicalOneRunScanState a lo next lengths ->
    OneRunScanState a lo next lengths.
Proof.
  intros a lo next lengths [Hprofile Hrun].
  split.
  - apply canonical_interior_one_run_prefix_projects.
    exact Hprofile.
  - exact Hrun.
Qed.

Lemma canonical_exam_block_collection_certificate_append :
  forall a base_sad pair_savings collected len,
    CanonicalExamBlockCollectionCertificate
      a base_sad pair_savings collected ->
    CanonicalExamBlockCollectionCertificate
      a base_sad pair_savings (collected ++ [len]).
Proof.
  intros a base_sad pair_savings collected len Hcert future Hprofile.
  unfold CanonicalExamBlockCollectionCertificate in Hcert.
  specialize (Hcert (len :: future)).
  rewrite <- app_assoc in Hprofile.
  simpl in Hprofile.
  specialize (Hcert Hprofile).
  rewrite <- app_assoc.
  simpl.
  exact Hcert.
Qed.

Lemma canonical_exam_block_collection_certificate_full_projects :
  forall a base_sad pair_savings collected,
    CanonicalInteriorOneRunPrefix a (Zlength a) collected ->
    CanonicalExamBlockCollectionCertificate
      a base_sad pair_savings collected ->
    ExamJointOptimizationCertificate
      a base_sad pair_savings collected.
Proof.
  intros a base_sad pair_savings collected Hprofile Hcert.
  unfold CanonicalExamBlockCollectionCertificate in Hcert.
  specialize (Hcert nil).
  rewrite app_nil_r in Hcert.
  exact (Hcert Hprofile).
Qed.

Require Import Coq.ZArith.Zquot.
Lemma canonical_profile_pair_block_disjoint__certificate_bootstrap :
  forall a lengths starts centres,
    Zlength starts = Zlength lengths ->
    (forall q, 0 <= q < Zlength lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q lengths 0)) ->
    PairCenterSelection a (Zlength a) centres ->
    forall center q,
      centres center -> 0 <= q < Zlength lengths ->
      center < Znth q starts 0 - 1 \/
      Znth q starts 0 + Znth q lengths 0 < center.
Proof.
  intros a lengths starts centres Hlen Hblocks Hcentres center q Hcenter Hq.
  destruct Hcentres as [Hvalid Hspaced].
  specialize (Hvalid center Hcenter).
  specialize (Hblocks q Hq).
  unfold NonOnePairCenter in Hvalid.
  unfold InteriorOneBlock in Hblocks.
  destruct Hvalid as [Hcb [Hcm1 [Hc [Hcp1 Hedges]]]].
  destruct Hblocks as [Hbh [Hbnd [Hleft [Hright Hones]]]].
  destruct (Z_lt_ge_dec center (Znth q starts 0 - 1)) as [Hbefore | Hnotbefore].
  - left. exact Hbefore.
  - right.
    destruct (Z_lt_ge_dec
      (Znth q starts 0 + Znth q lengths 0) center) as [Hafter | Hnotafter].
    + exact Hafter.
    + exfalso.
      destruct (Z.eq_dec center (Znth q starts 0 - 1)) as [Heqleft | Hneqleft].
      * subst center. apply Hcp1. apply Hones. lia.
      * destruct (Z.eq_dec center
          (Znth q starts 0 + Znth q lengths 0)) as [Heqright | Hneqright].
        -- subst center. apply Hcm1. apply Hones. lia.
        -- apply Hc. apply Hones. lia.
Qed.
Lemma fold_ones_length__pair_scan_exits :
  forall {A : Type} (xs : list A),
    List.fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
      Z.of_nat (List.length xs).
Proof.
  intros A xs.
  induction xs as [|x xs IH]; [reflexivity |].
  change (1 + List.fold_right
    (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
    Z.of_nat (S (List.length xs))).
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.
Lemma set_card_as_Zlength__pair_scan_exits :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    @set_card A P FP = Z.of_nat (List.length (@enum A P FP)).
Proof.
  intros A P FP.
  unfold set_card, SumLib.Sum.sum.
  apply fold_ones_length__pair_scan_exits.
Qed.
Lemma set_card_nonnegative__pair_scan_exits :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    0 <= @set_card A P FP.
Proof.
  intros A P FP.
  rewrite set_card_as_Zlength__pair_scan_exits.
  lia.
Qed.
Lemma set_card_injection_le__pair_scan_exits :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q) (f : A -> B),
    (forall x, P x -> Q (f x)) ->
    (forall x y, P x -> P y -> f x = f y -> x = y) ->
    @set_card A P FP <= @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f Hmaps Hinj.
  rewrite !set_card_as_Zlength__pair_scan_exits.
  assert (Hlen :
    (List.length (map f (@enum A P FP)) <=
     List.length (@enum B Q FQ))%nat).
  {
    apply NoDup_incl_length.
    - assert (Hgeneral : forall xs : list A,
        NoDup xs ->
        (forall x, In x xs -> P x) ->
        NoDup (map f xs)).
      {
        intros xs Hnodup.
        induction Hnodup as [|x xs Hnotin Hnodup IH]; intros Hall; simpl.
        - constructor.
        - constructor.
          + intro Hin.
            apply in_map_iff in Hin.
            destruct Hin as [y [Hfy Hy]].
            apply Hnotin.
            assert (HPx : P x) by (apply Hall; left; reflexivity).
            assert (HPy : P y) by (apply Hall; right; exact Hy).
            assert (Hxy : x = y).
            { apply Hinj; try assumption. symmetry; exact Hfy. }
            rewrite Hxy. exact Hy.
          + apply IH.
            intros y Hy. apply Hall. right. exact Hy.
      }
      apply Hgeneral.
      + exact (@enum_nodup A P FP).
      + intros x Hx.
        apply (proj2 (@enum_ok A P FP x)); exact Hx.
    - intros y Hy.
      apply in_map_iff in Hy.
      destruct Hy as [x [<- Hx]].
      apply (proj1 (@enum_ok B Q FQ (f x))).
      apply Hmaps.
      apply (proj2 (@enum_ok A P FP x)); exact Hx.
  }
  rewrite length_map in Hlen.
  exact (proj1 (Nat2Z.inj_le _ _) Hlen).
Qed.
Lemma set_card_product__pair_scan_exits :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q),
    @set_card (A * B) (fun p => P (fst p) /\ Q (snd p))
      (@Finite_prod A B P Q FP FQ) =
    @set_card A P FP * @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ.
  rewrite !set_card_as_Zlength__pair_scan_exits.
  assert (Hprod : forall (xs : list A) (ys : list B),
    List.length (list_prod xs ys) =
      (List.length xs * List.length ys)%nat).
  {
    intros xs ys.
    induction xs as [|x xs IH]; simpl; [reflexivity |].
    rewrite length_app, length_map, IH. lia.
  }
  change (Z.of_nat (List.length
      (list_prod (@enum A P FP) (@enum B Q FQ))) =
    Z.of_nat (List.length (@enum A P FP)) *
      Z.of_nat (List.length (@enum B Q FQ))).
  rewrite Hprod, Nat2Z.inj_mul.
  reflexivity.
Qed.
Lemma Zrange_aux_length__pair_scan_exits :
  forall low m, List.length (Zrange_aux low m) = m.
Proof.
  intros low m.
  revert low.
  induction m; intros; simpl; congruence.
Qed.
Lemma set_card_Z_range__pair_scan_exits :
  forall low high, low <= high ->
    @set_card Z (fun z => low <= z < high) (finite_Z_range low high) =
      high - low.
Proof.
  intros low high Hrange.
  rewrite set_card_as_Zlength__pair_scan_exits.
  change (Z.of_nat (List.length (Zrange low high)) = high - low).
  unfold Zrange.
  rewrite Zrange_aux_length__pair_scan_exits, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma pair_savings_prefix_witness__certificate_bootstrap :
  forall a pair_savings,
    PairSavingsPrefix a (Zlength a) pair_savings ->
    exists centres,
      PairCenterSelection a (Zlength a) centres /\
      #(fun center : Z =>
        1 <= center < Zlength a - 1 /\ centres center) = pair_savings /\
      0 <= pair_savings.
Proof.
  intros a pair_savings Hpair.
  unfold PairSavingsPrefix, max_value_of_subset,
    max_object_of_subset in Hpair.
  destruct Hpair as [centres [[Hselection Hmaximum] Hcount]].
  exists centres.
  split; [exact Hselection |].
  split; [exact Hcount |].
  rewrite <- Hcount.
  apply set_card_nonnegative__pair_scan_exits.
Qed.
Lemma canonical_blocks_strictly_separated__certificate_bootstrap :
  forall a lengths starts q r,
    Zlength starts = Zlength lengths ->
    mono_inc starts ->
    (forall x, 0 <= x < Zlength lengths ->
      InteriorOneBlock a (Znth x starts 0)
        (Znth x starts 0 + Znth x lengths 0)) ->
    0 <= q < r -> r < Zlength lengths ->
    Znth q starts 0 + Znth q lengths 0 < Znth r starts 0.
Proof.
  intros a lengths starts q r Hlen Hmono Hblocks Hqr Hr.
  assert (Hq : 0 <= q < Zlength lengths) by lia.
  assert (Hstart : Znth q starts 0 < Znth r starts 0).
  { apply Hmono; lia. }
  pose proof (Hblocks q Hq) as Hblockq.
  pose proof (Hblocks r ltac:(lia)) as Hblockr.
  unfold InteriorOneBlock in Hblockq.
  destruct Hblockq as [Hqb [Hqn [Hql [Hqrgt Hqones]]]].
  unfold InteriorOneBlock in Hblockr.
  destruct Hblockr as [Hrb [Hrn [Hrl [Hrrgt Hrones]]]].
  destruct (Z_lt_ge_dec
    (Znth q starts 0 + Znth q lengths 0) (Znth r starts 0))
    as [Hsep | Hover]; [exact Hsep |].
  destruct (Z.eq_dec
    (Znth q starts 0 + Znth q lengths 0) (Znth r starts 0))
    as [Heq | Hneq].
  - exfalso. apply Hqrgt.
    apply Hrones. lia.
  - exfalso. apply Hrl.
    apply Hqones. lia.
Qed.
Lemma fold_sum_list_prod__certificate_bootstrap :
  forall {A B : Type} (xs : list A) (ys : list B) (f : A * B -> Z),
    fold_right
      (fun p acc => f p + acc) 0 (list_prod xs ys) =
    fold_right
      (fun x acc => fold_right (fun y acc => f (x, y) + acc) 0 ys + acc)
      0 xs.
Proof.
  intros A B xs.
  induction xs as [|x xs IH]; intros ys f; simpl; [reflexivity |].
  assert (Happ : forall (ps qs : list (A * B)),
    fold_right (fun p acc => f p + acc) 0 (ps ++ qs) =
    fold_right (fun p acc => f p + acc) 0 ps +
    fold_right (fun p acc => f p + acc) 0 qs).
  {
    intros ps qs. induction ps as [|p ps IHp]; simpl; [lia |].
    rewrite IHp. lia.
  }
  rewrite Happ, IH.
  assert (Hmap :
    fold_right (fun p acc => f p + acc) 0
      (map (fun y => (x, y)) ys) =
    fold_right (fun y acc => f (x, y) + acc) 0 ys).
  {
    induction ys as [|y ys IHy]; simpl; [reflexivity |].
    rewrite IHy. reflexivity.
  }
  rewrite Hmap. reflexivity.
Qed.
Lemma set_card_subset_as_sum__certificate_bootstrap :
  forall {A : Type} (base extra : A -> Prop)
    (FB : Finite base) (FS : Finite (fun x => base x /\ extra x)),
    @set_card A (fun x => base x /\ extra x) FS =
    @SumLib.Sum.sum A base FB
      (fun x => if prop_dec (extra x) then 1 else 0).
Proof.
  intros A base extra FB FS.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A (fun x => base x /\ extra x) FS)
    (filter (fun x => if prop_dec (extra x) then true else false)
      (@enum A base FB))).
  {
    apply NoDup_Permutation.
    - apply enum_nodup.
    - apply NoDup_filter_bool. apply enum_nodup.
    - intros x. rewrite filter_In.
      rewrite <- (@enum_ok A (fun x => base x /\ extra x) FS x).
      rewrite <- (@enum_ok A base FB x).
      destruct (prop_dec (extra x)) as [Hextra | Hextra]; simpl.
      + tauto.
      + split.
        * intros [_ Hbad]. contradiction.
        * intros [_ Hbad]. discriminate.
  }
  assert (Hfoldperm :
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
      (@enum A (fun x => base x /\ extra x) FS) =
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
      (filter (fun x => if prop_dec (extra x) then true else false)
        (@enum A base FB))).
  {
    induction Hperm.
    - reflexivity.
    - change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
              1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l').
      f_equal. exact IHHperm.
    - simpl. lia.
    - etransitivity; eassumption.
  }
  rewrite Hfoldperm. clear Hperm Hfoldperm FS.
  induction (@enum A base FB) as [|x xs IH]; [reflexivity |].
  destruct (prop_dec (extra x)) as [Hextra | Hextra] eqn:Hdec.
  - cbn [filter fold_right]. rewrite Hdec.
    change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
              (filter (fun y => if prop_dec (extra y) then true else false) xs) =
            1 + fold_right (fun y acc =>
              (if prop_dec (extra y) then 1 else 0) + acc) 0 xs).
    f_equal. exact IH.
  - cbn [filter fold_right]. rewrite Hdec.
    change (fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
              (filter (fun y => if prop_dec (extra y) then true else false) xs) =
            fold_right (fun y acc =>
              (if prop_dec (extra y) then 1 else 0) + acc) 0 xs).
    exact IH.
Qed.
Lemma set_card_rect_subset_as_nested_sum__certificate_bootstrap :
  forall xlo xhi ylo yhi (P : Z * Z -> Prop),
    @set_card (Z * Z)
      (fun p =>
        (xlo <= fst p < xhi /\ ylo <= snd p < yhi) /\ P p)
      (@Finite_subset (Z * Z)
        (fun p => xlo <= fst p < xhi /\ ylo <= snd p < yhi) P
        (@Finite_prod Z Z
          (fun x => xlo <= x < xhi) (fun y => ylo <= y < yhi)
          (finite_Z_range xlo xhi) (finite_Z_range ylo yhi))) =
    SumLib.Sum.sum (fun x : Z => xlo <= x < xhi)
      (fun x => SumLib.Sum.sum (fun y : Z => ylo <= y < yhi)
        (fun y => if prop_dec (P (x, y)) then 1 else 0)).
Proof.
  intros xlo xhi ylo yhi P.
  erewrite (@set_card_subset_as_sum__certificate_bootstrap (Z * Z)
    (fun p => xlo <= fst p < xhi /\ ylo <= snd p < yhi) P
    (@Finite_prod Z Z
      (fun x => xlo <= x < xhi) (fun y => ylo <= y < yhi)
      (finite_Z_range xlo xhi) (finite_Z_range ylo yhi))
    (@Finite_subset (Z * Z)
      (fun p => xlo <= fst p < xhi /\ ylo <= snd p < yhi) P
      (@Finite_prod Z Z
        (fun x => xlo <= x < xhi) (fun y => ylo <= y < yhi)
        (finite_Z_range xlo xhi) (finite_Z_range ylo yhi)))).
  unfold SumLib.Sum.sum.
  change
    (fold_right
      (fun p acc => (if prop_dec (P p) then 1 else 0) + acc) 0
      (list_prod (Zrange xlo xhi) (Zrange ylo yhi)) =
    fold_right
      (fun x acc =>
        fold_right
          (fun y acc => (if prop_dec (P (x, y)) then 1 else 0) + acc)
          0 (Zrange ylo yhi) + acc)
      0 (Zrange xlo xhi)).
  exact (@fold_sum_list_prod__certificate_bootstrap Z Z
    (Zrange xlo xhi) (Zrange ylo yhi)
    (fun p => if prop_dec (P p) then 1 else 0)).
Qed.
Lemma sum_indicator_initial_segment__certificate_bootstrap :
  forall high cut,
    0 <= cut <= high ->
    SumLib.Sum.sum (fun y : Z => 0 <= y < high)
      (fun y => if prop_dec (y < cut) then 1 else 0) = cut.
Proof.
  intros high cut Hbounds.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 cut high) by lia.
  assert (Hleft :
    SumLib.Sum.sum (fun y : Z => 0 <= y < cut)
      (fun y => if prop_dec (y < cut) then 1 else 0) = cut).
  {
    transitivity
      (SumLib.Sum.sum (fun y : Z => 0 <= y < cut) (fun _ => 1)).
    - apply SumLib.ZRange.sum_Z_range_ext.
      intros y Hy. destruct (prop_dec (y < cut)); [reflexivity | lia].
    - rewrite SumLib.ZRange.sum_Z_range_const by lia. lia.
  }
  assert (Hright :
    SumLib.Sum.sum (fun y : Z => cut <= y < high)
      (fun y => if prop_dec (y < cut) then 1 else 0) = 0).
  {
    apply SumLib.ZRange.sum_Z_range_eq_zero.
    intros y Hy. destruct (prop_dec (y < cut)); [lia | reflexivity].
  }
  lia.
Qed.
Lemma block_charge_source_cardinality__certificate_bootstrap :
  forall (lengths : list Z) high,
    (forall q, 0 <= q < Zlength lengths ->
      0 <= Znth q lengths 0 + 1 <= high) ->
    @set_card (Z * Z)
      (fun p =>
        (0 <= fst p < Zlength lengths /\ 0 <= snd p < high) /\
        snd p < Znth (fst p) lengths 0 + 1)
      (@Finite_subset (Z * Z)
        (fun p =>
          0 <= fst p < Zlength lengths /\ 0 <= snd p < high)
        (fun p => snd p < Znth (fst p) lengths 0 + 1)
        (@Finite_prod Z Z
          (fun q => 0 <= q < Zlength lengths)
          (fun t => 0 <= t < high)
          (finite_Z_range 0 (Zlength lengths))
          (finite_Z_range 0 high))) =
    ListLib.sum (map (fun len => len + 1) lengths).
Proof.
  intros lengths high Hbounds.
  rewrite set_card_rect_subset_as_nested_sum__certificate_bootstrap.
  rewrite (SumLib.ZRange.list_sum_map_as_Z_range_sum
    0 (fun len : Z => len + 1) lengths).
  apply SumLib.ZRange.sum_Z_range_ext.
  intros q Hq.
  change (SumLib.Sum.sum (fun y : Z => 0 <= y < high)
    (fun y => if prop_dec (y < Znth q lengths 0 + 1) then 1 else 0) =
    Znth q lengths 0 + 1).
  apply sum_indicator_initial_segment__certificate_bootstrap.
  apply Hbounds. exact Hq.
Qed.
Lemma set_card_Z_as_sum_exam__final_result :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma negated_center_cardinality__certificate_bootstrap :
  forall n (centres : Z -> Prop),
    (forall center, centres center -> 1 <= center < n - 1) ->
    #(fun center : Z => 1 <= center < n - 1 /\ centres center) =
    #(fun q : Z => - n <= q < 0 /\ centres (- q)).
Proof.
  intros n centres Hrange.
  apply Z.le_antisymm.
  - eapply set_card_injection_le__pair_scan_exits with
      (f := fun center => - center).
    + intros center [Hcenter Hchosen]. split; [lia |].
      replace (- - center) with center by ring. exact Hchosen.
    + intros x y Hx Hy Heq. lia.
  - eapply set_card_injection_le__pair_scan_exits with
      (f := fun q => - q).
    + intros q [Hq Hchosen]. split.
      * specialize (Hrange (- q) Hchosen). lia.
      * exact Hchosen.
    + intros x y Hx Hy Heq. lia.
Qed.
Lemma tagged_charge_source_cardinality__certificate_bootstrap :
  forall n lengths pair_savings (centres : Z -> Prop),
    1 <= n ->
    (forall center, centres center -> 1 <= center < n - 1) ->
    #(fun center : Z => 1 <= center < n - 1 /\ centres center) =
      pair_savings ->
    (forall q, 0 <= q < Zlength lengths ->
      0 <= Znth q lengths 0 + 1 <= n + 1) ->
    @set_card (Z * Z)
      (fun p =>
        (- n <= fst p < Zlength lengths /\ 0 <= snd p < n + 1) /\
        ((fst p < 0 /\ centres (- fst p) /\ snd p < 2) \/
         (0 <= fst p /\ snd p < Znth (fst p) lengths 0 + 1)))
      (@Finite_subset (Z * Z)
        (fun p =>
          - n <= fst p < Zlength lengths /\ 0 <= snd p < n + 1)
        (fun p =>
          (fst p < 0 /\ centres (- fst p) /\ snd p < 2) \/
          (0 <= fst p /\ snd p < Znth (fst p) lengths 0 + 1))
        (@Finite_prod Z Z
          (fun q => - n <= q < Zlength lengths)
          (fun t => 0 <= t < n + 1)
          (finite_Z_range (- n) (Zlength lengths))
          (finite_Z_range 0 (n + 1)))) =
    2 * pair_savings +
      ListLib.sum (map (fun len => len + 1) lengths).
Proof.
  intros n lengths pair_savings centres Hn Hcentres Hcount Hlengths.
  rewrite set_card_rect_subset_as_nested_sum__certificate_bootstrap.
  rewrite (SumLib.ZRange.sum_Z_range_split
    (- n) 0 (Zlength lengths)) by (pose proof (Zlength_nonneg lengths); lia).
  assert (Hleft :
    SumLib.Sum.sum (fun q : Z => - n <= q < 0)
      (fun q => SumLib.Sum.sum (fun t : Z => 0 <= t < n + 1)
        (fun t => if prop_dec
          ((q < 0 /\ centres (- q) /\ t < 2) \/
           (0 <= q /\ t < Znth q lengths 0 + 1))
          then 1 else 0)) = 2 * pair_savings).
  {
    transitivity
      (SumLib.Sum.sum (fun q : Z => - n <= q < 0)
        (fun q => (if prop_dec (centres (- q)) then 1 else 0) * 2)).
    - apply SumLib.ZRange.sum_Z_range_ext.
      intros q Hq.
      destruct (prop_dec (centres (- q))) as [Hchosen | Hchosen].
      + transitivity
          (SumLib.Sum.sum (fun t : Z => 0 <= t < n + 1)
            (fun t => if prop_dec (t < 2) then 1 else 0)).
        * apply SumLib.ZRange.sum_Z_range_ext.
          intros t Ht.
          destruct (prop_dec
            ((q < 0 /\ centres (- q) /\ t < 2) \/
             (0 <= q /\ t < Znth q lengths 0 + 1))) as [Hbig | Hbig];
            destruct (prop_dec (t < 2)) as [Ht2 | Ht2];
            simpl; try reflexivity.
          -- exfalso. destruct Hbig as [[_ [_ Hbad]] | [Hbad _]];
               [contradiction | lia].
          -- exfalso. apply Hbig. left. split; [lia |]. split; assumption.
        * rewrite sum_indicator_initial_segment__certificate_bootstrap by lia.
          reflexivity.
      + rewrite SumLib.ZRange.sum_Z_range_eq_zero.
        * reflexivity.
        * intros t Ht.
          destruct (prop_dec
            ((q < 0 /\ centres (- q) /\ t < 2) \/
             (0 <= q /\ t < Znth q lengths 0 + 1))) as [Hbig | Hbig].
          -- exfalso. destruct Hbig as [[_ [Hbad _]] | [Hbad _]];
               [contradiction | lia].
          -- reflexivity.
    - rewrite SumLib.Sum.sum_factor_r.
      rewrite <- set_card_Z_as_sum_exam__final_result.
      rewrite <- (negated_center_cardinality__certificate_bootstrap
        n centres Hcentres).
      rewrite Hcount. ring.
  }
  assert (Hright :
    SumLib.Sum.sum (fun q : Z => 0 <= q < Zlength lengths)
      (fun q => SumLib.Sum.sum (fun t : Z => 0 <= t < n + 1)
        (fun t => if prop_dec
          ((q < 0 /\ centres (- q) /\ t < 2) \/
           (0 <= q /\ t < Znth q lengths 0 + 1))
          then 1 else 0)) =
    ListLib.sum (map (fun len => len + 1) lengths)).
  {
    rewrite (SumLib.ZRange.list_sum_map_as_Z_range_sum
      0 (fun len : Z => len + 1) lengths).
    apply SumLib.ZRange.sum_Z_range_ext.
    intros q Hq.
    transitivity
      (SumLib.Sum.sum (fun t : Z => 0 <= t < n + 1)
        (fun t => if prop_dec (t < Znth q lengths 0 + 1)
          then 1 else 0)).
    - apply SumLib.ZRange.sum_Z_range_ext.
      intros t Ht.
      destruct (prop_dec
        ((q < 0 /\ centres (- q) /\ t < 2) \/
         (0 <= q /\ t < Znth q lengths 0 + 1))) as [Hbig | Hbig];
        destruct (prop_dec (t < Znth q lengths 0 + 1)) as [Hsmall | Hsmall];
        simpl; try reflexivity.
      + exfalso. destruct Hbig as [[Hbad _] | [_ Hbad]];
          [lia | contradiction].
      + exfalso. apply Hbig. right. split; [lia | assumption].
    - apply sum_indicator_initial_segment__certificate_bootstrap.
      apply Hlengths. exact Hq.
  }
  cbn [fst snd].
  lia.
Qed.
Lemma block_charge_maps_to_coprime_edge__certificate_bootstrap :
  forall a lo len t,
    InteriorOneBlock a lo (lo + len) ->
    0 <= t < len + 1 ->
    AdjacentCoprime a (lo - 1 + t).
Proof.
  intros a lo len t Hblock Ht.
  unfold InteriorOneBlock in Hblock.
  destruct Hblock as [Hbounds [Hhi [Hleft [Hright Hones]]]].
  unfold AdjacentCoprime.
  split; [lia |].
  destruct (Z.eq_dec t 0) as [-> | Ht0].
  - replace (lo - 1 + 0 + 1) with lo by lia.
    assert (Hone : Znth lo a 0 = 1) by (apply Hones; lia).
    rewrite Hone.
    apply Z.gcd_1_r.
  - destruct (Z.eq_dec t len) as [-> | Htlen].
    + replace (lo - 1 + len) with (lo + len - 1) by lia.
      replace (lo + len - 1 + 1) with (lo + len) by lia.
      assert (Hone : Znth (lo + len - 1) a 0 = 1)
        by (apply Hones; lia).
      rewrite Hone.
      apply Z.gcd_1_l.
    + assert (Hone1 : Znth (lo - 1 + t) a 0 = 1)
        by (apply Hones; lia).
      assert (Hone2 : Znth (lo - 1 + t + 1) a 0 = 1)
        by (apply Hones; lia).
      rewrite Hone1, Hone2.
      reflexivity.
Qed.
Lemma tagged_charge_bound__certificate_bootstrap :
  forall a n lengths starts pair_savings (centres : Z -> Prop),
    n = Zlength a -> 1 <= n ->
    Zlength starts = Zlength lengths ->
    mono_inc starts ->
    (forall q, 0 <= q < Zlength lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q lengths 0)) ->
    PairCenterSelection a n centres ->
    #(fun center : Z => 1 <= center < n - 1 /\ centres center) =
      pair_savings ->
    2 * pair_savings +
      ListLib.sum (map (fun len => len + 1) lengths) <=
    #(fun edge : Z => 0 <= edge < n - 1 /\ AdjacentCoprime a edge).
Proof.
  intros a n lengths starts pair_savings centres
    Hn Hnpos Hlen Hmono Hblocks Hselection Hcount.
  subst n.
  assert (Hcentres : forall center, centres center ->
    1 <= center < Zlength a - 1).
  {
    intros center Hcenter.
    destruct Hselection as [Hvalid _].
    specialize (Hvalid center Hcenter).
    unfold NonOnePairCenter in Hvalid. tauto.
  }
  assert (Hlengths : forall q, 0 <= q < Zlength lengths ->
    0 <= Znth q lengths 0 + 1 <= Zlength a + 1).
  {
    intros q Hq.
    pose proof (Hblocks q Hq) as Hblock.
    unfold InteriorOneBlock in Hblock.
    lia.
  }
  rewrite <- (tagged_charge_source_cardinality__certificate_bootstrap
    (Zlength a) lengths pair_savings centres Hnpos Hcentres Hcount Hlengths).
  eapply set_card_injection_le__pair_scan_exits with
    (f := fun p : Z * Z =>
      if Z_lt_dec (fst p) 0
      then - fst p - 1 + snd p
      else Znth (fst p) starts 0 - 1 + snd p).
  - intros [q t] [[Hq Ht] Htag]. cbn [fst snd] in *.
    destruct (Z_lt_dec q 0) as [Hqneg | Hqnonneg].
    + destruct Htag as [[_ [Hchosen Htwo]] | [Hbad _]]; [|lia].
      pose proof (proj1 Hselection (- q) Hchosen) as Hvalid.
      unfold NonOnePairCenter in Hvalid.
      destruct Hvalid as [Hcb [Hleft [Hcenter [Hright [Hedgeleft Hedgeright]]]]].
      destruct (Z.eq_dec t 0) as [-> | Ht0].
      * replace (- q - 1 + 0) with (- q - 1) by lia.
        split; [lia | exact Hedgeleft].
      * assert (t = 1) by lia. subst t.
        replace (- q - 1 + 1) with (- q) by lia.
        split; [lia | exact Hedgeright].
    + destruct Htag as [[Hbad _] | [_ Hlocal]]; [lia |].
      pose proof (Hblocks q ltac:(lia)) as Hblock.
      pose proof (block_charge_maps_to_coprime_edge__certificate_bootstrap
        a (Znth q starts 0) (Znth q lengths 0) t Hblock ltac:(lia))
        as Hedge.
      split.
      * pose proof Hedge as Hedge'. unfold AdjacentCoprime in Hedge'. lia.
      * exact Hedge.
  - intros [qx tx] [qy ty] [[Hqx Htx] Htagx] [[Hqy Hty] Htagy] Heq.
    cbn [fst snd] in *.
    destruct (Z_lt_dec qx 0) as [Hqxneg | Hqxnonneg];
      destruct (Z_lt_dec qy 0) as [Hqyneg | Hqynonneg].
    + destruct Htagx as [[_ [Hcx Htx2]] | [Hbad _]]; [|lia].
      destruct Htagy as [[_ [Hcy Hty2]] | [Hbad _]]; [|lia].
      assert (Hcentereq : - qx = - qy).
      {
        destruct (Z.eq_dec (- qx) (- qy)) as [He | Hne]; [exact He |].
        pose proof (proj2 Hselection (- qx) (- qy) Hcx Hcy Hne) as Hspace.
        assert (Hsmall : Z.abs ((- qx) - (- qy)) <= 1).
        { apply (proj2 (Z.abs_le _ 1)). lia. }
        lia.
      }
      assert (qx = qy) by lia. subst qy.
      assert (tx = ty) by lia. subst ty. reflexivity.
    + destruct Htagx as [[_ [Hcx Htx2]] | [Hbad _]]; [|lia].
      destruct Htagy as [[Hbad _] | [_ Htylen]]; [lia |].
      pose proof (canonical_profile_pair_block_disjoint__certificate_bootstrap
        a lengths starts centres Hlen Hblocks Hselection
        (- qx) qy Hcx ltac:(lia)) as Hdisj.
      destruct Hdisj; lia.
    + destruct Htagx as [[Hbad _] | [_ Htxlen]]; [lia |].
      destruct Htagy as [[_ [Hcy Hty2]] | [Hbad _]]; [|lia].
      pose proof (canonical_profile_pair_block_disjoint__certificate_bootstrap
        a lengths starts centres Hlen Hblocks Hselection
        (- qy) qx Hcy ltac:(lia)) as Hdisj.
      destruct Hdisj; lia.
    + destruct Htagx as [[Hbad _] | [_ Htxlen]]; [lia |].
      destruct Htagy as [[Hbad _] | [_ Htylen]]; [lia |].
      destruct (Z.eq_dec qx qy) as [-> | Hqneq].
      * assert (tx = ty) by lia. subst ty. reflexivity.
      * destruct (Z.lt_trichotomy qx qy) as [Hxy | [Hxy | Hyx]];
          [|contradiction|].
        -- pose proof (canonical_blocks_strictly_separated__certificate_bootstrap
             a lengths starts qx qy Hlen Hmono Hblocks ltac:(lia) ltac:(lia))
             as Hsep.
           lia.
        -- pose proof (canonical_blocks_strictly_separated__certificate_bootstrap
             a lengths starts qy qx Hlen Hmono Hblocks ltac:(lia) ltac:(lia))
             as Hsep.
           lia.
Qed.
Lemma canonical_profile_yields_joint_prefix__certificate_bootstrap :
  forall a base_sad pair_savings lengths,
    1 <= Zlength a ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    CanonicalInteriorOneRunPrefix a (Zlength a) lengths ->
    JointPairBlockPrefix a (Zlength a)
      base_sad pair_savings lengths.
Proof.
  intros a base_sad pair_savings lengths Hn Hsad Hpair Hcanonical.
  destruct Hcanonical as
    [starts [Hlen [Hmono [Hblocks Hcomplete]]]].
  destruct (pair_savings_prefix_witness__certificate_bootstrap
    a pair_savings Hpair) as [centres [Hselection [Hcount Hpairnonneg]]].
  assert (Hinterior : InteriorOneRunPrefix a (Zlength a) lengths).
  {
    unfold InteriorOneRunPrefix.
    exists starts. split; [exact Hlen |]. split.
    - apply (proj1 (mono_nondec_iff_increasing starts)).
      apply mono_inc_nondec. exact Hmono.
    - split; assumption.
  }
  assert (Hpositive : Forall (fun len => 1 <= len) lengths).
  {
    apply (proj2 (Forall_Znth (fun len => 1 <= len) 0 lengths)).
    intros q Hq.
    pose proof (Hblocks q Hq) as Hblock.
    unfold InteriorOneBlock in Hblock. lia.
  }
  assert (Hbound :
    2 * pair_savings +
      ListLib.sum (map (fun len => len + 1) lengths) <= base_sad).
  {
    pose proof (tagged_charge_bound__certificate_bootstrap
      a (Zlength a) lengths starts pair_savings centres
      eq_refl Hn Hlen Hmono
      (fun q Hq => proj1 (Hblocks q Hq)) Hselection Hcount) as Hcharge.
    unfold CoprimeEdgePrefixCount in Hsad.
    rewrite Hsad. exact Hcharge.
  }
  unfold JointPairBlockPrefix.
  split; [exact Hpair |].
  split; [exact Hinterior |].
  split; [exact Hpairnonneg |].
  split; [exact Hpositive |].
  split; [exact Hbound |].
  exists centres, starts.
  split; [exact Hselection |].
  split; [exact Hcount |].
  split; [exact Hlen |].
  split.
  - apply (proj1 (mono_nondec_iff_increasing starts)).
    apply mono_inc_nondec. exact Hmono.
  - split; [exact Hblocks |].
    intros center q Hcenter Hq.
    eapply canonical_profile_pair_block_disjoint__certificate_bootstrap;
      eauto.
    intros x Hx. exact (proj1 (Hblocks x Hx)).
Qed.
Lemma spec_yields_optimality_evidence__certificate_bootstrap :
  forall a original_k out,
    Spec original_k a out ->
    ExamOptimalityEvidence a original_k out.
Proof.
  intros a original_k out Hspec.
  unfold Spec, min_value_of_subset in Hspec.
  destruct Hspec as [[result sadness] [Hminimum Heq]].
  unfold min_object_of_subset in Hminimum.
  destruct Hminimum as [[Hresult Hsadness] Hlower].
  simpl in Heq.
  subst sadness.
  exists result.
  split; [exact Hresult |].
  split; [exact Hsadness |].
  intros other other_sadness Hother Hother_sadness.
  specialize (Hlower (other, other_sadness)).
  simpl in Hlower.
  apply Hlower.
  split; assumption.
Qed.
Lemma Zlength_map__certificate_bootstrap :
  forall {A B : Type} (f : A -> B) xs,
    Zlength (map f xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__certificate_bootstrap :
  forall {A B : Type} (f : A -> B) xs
      (da : A) (db : B) i,
    0 <= i < Zlength xs ->
    Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Znth_Zrange__certificate_bootstrap :
  forall low high i,
    low <= high -> 0 <= i < high - low ->
    Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  assert (Haux : forall m low j,
    0 <= j < Z.of_nat m ->
    Znth j (Zrange_aux low m) 0 = low + j).
  {
    induction m as [|m IH]; intros lo j Hj; [lia |].
    simpl. destruct (Z.eq_dec j 0) as [-> | Hne].
    - rewrite Znth0_cons. lia.
    - rewrite Znth_cons by lia.
      rewrite IH by (rewrite Nat2Z.inj_succ in Hj; lia). lia.
  }
  rewrite Haux by lia. lia.
Qed.
Lemma materialize_exam_choice__certificate_bootstrap :
  forall a k (chosen : Z -> Prop),
    (forall i, chosen i -> 0 <= i < Zlength a) ->
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) <= k ->
    exists result, SimplifiedExams a k result.
Proof.
  intros a k chosen Hrange Hcard.
  exists (map
    (fun i => if prop_dec (chosen i) then 0 else Znth i a 0)
    (Zrange 0 (Zlength a))).
  exists chosen.
  split; [exact Hrange |].
  split; [exact Hcard |].
  split.
  - rewrite Zlength_map__certificate_bootstrap.
    unfold Zrange.
    rewrite Zlength_correct, Zrange_aux_length__pair_scan_exits,
      Z2Nat.id by (pose proof (Zlength_nonneg a); lia).
    lia.
  - intros i Hi.
    rewrite (@Znth_map__certificate_bootstrap Z Z
      (fun idx => if prop_dec (chosen idx) then 0 else Znth idx a 0)
      (Zrange 0 (Zlength a)) 0 0 i).
    + rewrite Znth_Zrange__certificate_bootstrap by lia.
      replace (0 + i) with i by lia. reflexivity.
    + unfold Zrange.
      rewrite Zlength_correct, Zrange_aux_length__pair_scan_exits,
        Z2Nat.id by (pose proof (Zlength_nonneg a); lia).
      lia.
Qed.
Lemma materialize_exam_choice_sadness__certificate_bootstrap :
  forall a k (chosen : Z -> Prop) sadness,
    (forall i, chosen i -> 0 <= i < Zlength a) ->
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) <= k ->
    sadness = #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) = 1) ->
    exists result,
      SimplifiedExams a k result /\ ExamSadness result sadness.
Proof.
  intros a k chosen sadness Hrange Hcard Hsadness.
  set (result := map
    (fun i => if prop_dec (chosen i) then 0 else Znth i a 0)
    (Zrange 0 (Zlength a))).
  assert (Hlength : Zlength result = Zlength a).
  {
    unfold result. rewrite Zlength_map__certificate_bootstrap.
    unfold Zrange.
    rewrite Zlength_correct, Zrange_aux_length__pair_scan_exits,
      Z2Nat.id by (pose proof (Zlength_nonneg a); lia).
    lia.
  }
  assert (Hvalues : forall i, 0 <= i < Zlength a ->
    Znth i result 0 =
      if prop_dec (chosen i) then 0 else Znth i a 0).
  {
    intros i Hi. unfold result.
    rewrite (@Znth_map__certificate_bootstrap Z Z
      (fun idx => if prop_dec (chosen idx) then 0 else Znth idx a 0)
      (Zrange 0 (Zlength a)) 0 0 i).
    - rewrite Znth_Zrange__certificate_bootstrap by lia.
      replace (0 + i) with i by lia. reflexivity.
    - unfold Zrange.
      rewrite Zlength_correct, Zrange_aux_length__pair_scan_exits,
        Z2Nat.id by (pose proof (Zlength_nonneg a); lia).
      lia.
  }
  exists result. split.
  - exists chosen. split; [exact Hrange |].
    split; [exact Hcard |].
    split; [exact Hlength |].
    exact Hvalues.
  - unfold ExamSadness.
    rewrite Hsadness.
    apply set_card_iff__exam_bridge.
    intros edge. split.
    + intros [Hedge Hgcd]. split; [lia |].
      try rewrite Hlength in Hedge.
      try rewrite Hlength.
      try (rewrite Hvalues in Hgcd by lia;
        rewrite Hvalues in Hgcd by lia).
      try (rewrite Hvalues by lia; rewrite Hvalues by lia).
      exact Hgcd.
    + intros [Hedge Hgcd]. split; [lia |].
      try rewrite Hlength in Hedge.
      try rewrite Hlength.
      try (rewrite Hvalues in Hgcd by lia;
        rewrite Hvalues in Hgcd by lia).
      try (rewrite Hvalues by lia; rewrite Hvalues by lia).
      exact Hgcd.
Qed.
Lemma simplified_exam_exposes_choice_sadness__certificate_bootstrap :
  forall a k result sadness,
    SimplifiedExams a k result ->
    ExamSadness result sadness ->
    exists chosen,
      (forall i, chosen i -> 0 <= i < Zlength a) /\
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i) <= k /\
      sadness = #(fun edge : Z =>
        0 <= edge < Zlength a - 1 /\
        Z.gcd
          (if prop_dec (chosen edge) then 0 else Znth edge a 0)
          (if prop_dec (chosen (edge + 1)) then 0
           else Znth (edge + 1) a 0) = 1).
Proof.
  intros a k result sadness
    [chosen [Hrange [Hcard [Hlength Hvalues]]]] Hsadness.
  exists chosen. split; [exact Hrange |].
  split; [exact Hcard |].
  unfold ExamSadness in Hsadness.
  rewrite Hsadness.
  apply set_card_iff__exam_bridge.
  intros edge. split.
  - intros [Hedge Hgcd]. split; [lia |].
    try rewrite Hlength in Hedge.
    try rewrite Hlength.
    try (rewrite Hvalues in Hgcd by lia;
      rewrite Hvalues in Hgcd by lia).
    try (rewrite Hvalues by lia; rewrite Hvalues by lia).
    exact Hgcd.
  - intros [Hedge Hgcd]. split; [lia |].
    try rewrite Hlength in Hedge.
    try rewrite Hlength.
    try (rewrite Hvalues in Hgcd by lia;
      rewrite Hvalues in Hgcd by lia).
    try (rewrite Hvalues by lia; rewrite Hvalues by lia).
    exact Hgcd.
Qed.
Lemma transformed_coprime_edge_cases__certificate_bootstrap :
  forall x y (left right : Prop),
    0 <= x -> 0 <= y -> Z.gcd x y = 1 ->
    Z.gcd
      (if prop_dec left then 0 else x)
      (if prop_dec right then 0 else y) = 1 <->
    (~ left /\ ~ right) \/
    (left /\ ~ right /\ y = 1) \/
    (~ left /\ right /\ x = 1).
Proof.
  intros x y left right Hx Hy Hcoprime.
  destruct (prop_dec left) as [Hleft | Hleft];
    destruct (prop_dec right) as [Hright | Hright]; simpl.
  - split; [discriminate | tauto].
  - rewrite Z.gcd_0_l_nonneg by lia. tauto.
  - rewrite Z.gcd_0_r_nonneg by lia. tauto.
  - rewrite Hcoprime. tauto.
Qed.
Lemma transformed_coprime_edge_removed_cases__certificate_bootstrap :
  forall x y (left right : Prop),
    0 <= x -> 0 <= y -> Z.gcd x y = 1 ->
    Z.gcd
      (if prop_dec left then 0 else x)
      (if prop_dec right then 0 else y) <> 1 <->
    (left /\ right) \/
    (left /\ ~ right /\ y <> 1) \/
    (~ left /\ right /\ x <> 1).
Proof.
  intros x y left right Hx Hy Hcoprime.
  destruct (prop_dec left) as [Hleft | Hleft];
    destruct (prop_dec right) as [Hright | Hright]; simpl.
  - split.
    + intros _. left. split; assumption.
    + intros _. lia.
  - rewrite Z.gcd_0_l_nonneg by lia. tauto.
  - rewrite Z.gcd_0_r_nonneg by lia. tauto.
  - rewrite Hcoprime. tauto.
Qed.
Lemma transformed_coprime_implies_original__certificate_bootstrap :
  forall x y (left right : Prop),
    0 <= x -> 0 <= y ->
    Z.gcd
      (if prop_dec left then 0 else x)
      (if prop_dec right then 0 else y) = 1 ->
    Z.gcd x y = 1.
Proof.
  intros x y left right Hx Hy Htransformed.
  destruct (prop_dec left) as [Hleft | Hleft];
    destruct (prop_dec right) as [Hright | Hright]; simpl in Htransformed.
  - discriminate.
  - rewrite Z.gcd_0_l_nonneg in Htransformed by lia.
    subst y. apply Z.gcd_1_r.
  - rewrite Z.gcd_0_r_nonneg in Htransformed by lia.
    subst x. apply Z.gcd_1_l.
  - exact Htransformed.
Qed.
Lemma set_card_partition_subset_Z__certificate_bootstrap :
  forall low high (P Q : Z -> Prop),
    (forall z, low <= z < high -> Q z -> P z) ->
    #(fun z : Z => low <= z < high /\ P z) =
    #(fun z : Z => low <= z < high /\ Q z) +
    #(fun z : Z => low <= z < high /\ P z /\ ~ Q z).
Proof.
  intros low high P Q Hsubset.
  rewrite !set_card_Z_as_sum_exam__final_result.
  rewrite <- SumLib.ZRange.sum_Z_range_add.
  apply SumLib.ZRange.sum_Z_range_ext.
  intros z Hz.
  assert (HQP : Q z -> P z) by (apply Hsubset; exact Hz).
  destruct (prop_dec (P z)) as [HP | HP];
    destruct (prop_dec (Q z)) as [HQ | HQ];
    destruct (prop_dec (P z /\ ~ Q z)) as [HR | HR]; simpl;
    try lia; exfalso; tauto.
Qed.
Lemma choice_sadness_is_base_minus_removed__certificate_bootstrap :
  forall a (chosen : Z -> Prop) base_sad sadness,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    sadness = #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) = 1) ->
    base_sad = sadness + #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) <> 1).
Proof.
  intros a chosen base_sad sadness Hnonneg Hbase Hsadness.
  unfold CoprimeEdgePrefixCount in Hbase.
  unfold AdjacentCoprime in Hbase.
  assert (Hbase_simple : base_sad = #(fun edge : Z =>
    0 <= edge < Zlength a - 1 /\
    Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1)).
  {
    rewrite Hbase.
    apply set_card_iff__exam_bridge.
    intros edge. tauto.
  }
  rewrite Hbase_simple, Hsadness.
  apply set_card_partition_subset_Z__certificate_bootstrap.
  intros edge Hedge Htransformed.
  apply transformed_coprime_implies_original__certificate_bootstrap
    with (left := chosen edge) (right := chosen (edge + 1)); try assumption.
  - apply Hnonneg. lia.
  - apply Hnonneg. lia.
Qed.
Lemma removed_edges_at_most_twice_choices__certificate_bootstrap :
  forall a (chosen : Z -> Prop),
    #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) <> 1) <=
    2 * #(fun i : Z => 0 <= i < Zlength a /\ chosen i).
Proof.
  intros a chosen.
  transitivity
    (@set_card (Z * Z)
      (fun p =>
        (0 <= fst p < Zlength a /\ chosen (fst p)) /\
        (0 <= snd p < 2))
      (@Finite_prod Z Z
        (fun i => 0 <= i < Zlength a /\ chosen i)
        (fun tag => 0 <= tag < 2)
        (@Finite_subset Z (fun i => 0 <= i < Zlength a) chosen
          (finite_Z_range 0 (Zlength a)))
        (finite_Z_range 0 2))).
  - eapply set_card_injection_le__pair_scan_exits with
      (f := fun edge =>
        if prop_dec (chosen edge) then (edge, 0) else (edge + 1, 1)).
    + intros edge [Hedge [Hcoprime Hremoved]].
      destruct (prop_dec (chosen edge)) as [Hleft | Hleft].
      * cbn [fst snd]. repeat split; try assumption; lia.
      * assert (Hright : chosen (edge + 1)).
        {
          destruct (prop_dec (chosen (edge + 1))) as [Hright | Hright];
            [exact Hright |].
          simpl in Hremoved.
          rewrite Hcoprime in Hremoved. contradiction.
        }
        cbn [fst snd]. repeat split; try assumption; lia.
    + intros x y Hx Hy Heq.
      destruct (prop_dec (chosen x)) as [Hcx | Hcx];
        destruct (prop_dec (chosen y)) as [Hcy | Hcy];
        inversion Heq; lia.
  - erewrite (@set_card_product__pair_scan_exits Z Z
      (fun i => 0 <= i < Zlength a /\ chosen i)
      (fun tag => 0 <= tag < 2)
      (@Finite_subset Z (fun i => 0 <= i < Zlength a) chosen
        (finite_Z_range 0 (Zlength a)))
      (finite_Z_range 0 2)).
    rewrite set_card_Z_range__pair_scan_exits by lia.
    replace (2 - 0) with 2 by lia.
    rewrite Z.mul_comm.
    apply Z.le_refl.
Qed.
Lemma simplified_exam_coarse_lower_bound__certificate_bootstrap :
  forall a k base_sad result sadness,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    SimplifiedExams a k result ->
    ExamSadness result sadness ->
    base_sad - 2 * k <= sadness.
Proof.
  intros a k base_sad result sadness Hnonneg Hbase Hresult Hsadness.
  destruct (simplified_exam_exposes_choice_sadness__certificate_bootstrap
    a k result sadness Hresult Hsadness)
    as [chosen [Hrange [Hcard Hchoice_sadness]]].
  pose proof (choice_sadness_is_base_minus_removed__certificate_bootstrap
    a chosen base_sad sadness Hnonneg Hbase Hchoice_sadness) as Hpartition.
  pose proof (removed_edges_at_most_twice_choices__certificate_bootstrap
    a chosen) as Hremoved.
  nia.
Qed.
Lemma pair_savings_bounds_every_selection__certificate_bootstrap :
  forall a pair_savings (candidate : Z -> Prop),
    PairSavingsPrefix a (Zlength a) pair_savings ->
    PairCenterSelection a (Zlength a) candidate ->
    #(fun center : Z =>
      1 <= center < Zlength a - 1 /\ candidate center) <= pair_savings.
Proof.
  intros a pair_savings candidate Hpair Hcandidate.
  unfold PairSavingsPrefix, max_value_of_subset,
    max_object_of_subset in Hpair.
  destruct Hpair as [maximum [[Hmaximum Hbound] Hcount]].
  rewrite <- Hcount.
  apply Hbound. exact Hcandidate.
Qed.
Lemma selected_nonone_run_starts_form_pair_selection__certificate_bootstrap :
  forall a (chosen : Z -> Prop),
    PairCenterSelection a (Zlength a)
      (fun center =>
        chosen center /\ ~ chosen (center - 1) /\
        Znth (center - 1) a 0 <> 1 /\
        Znth center a 0 <> 1 /\
        Znth (center + 1) a 0 <> 1 /\
        AdjacentCoprime a (center - 1) /\
        AdjacentCoprime a center).
Proof.
  intros a chosen. split.
  - intros center
      [Hchosen [Hprevious [Hleft [Hcenter [Hright [Hedgeleft Hedgeright]]]]]].
    unfold NonOnePairCenter.
    unfold AdjacentCoprime in Hedgeleft, Hedgeright.
    repeat split; try assumption; lia.
  - intros x y
      [Hchosenx [Hpreviousx [Hleftx [Hcenterx [Hrightx Hedgesx]]]]]
      [Hchoseny [Hpreviousy [Hlefty [Hcentery [Hrighty Hedgesy]]]]]
      Hneq.
    destruct (Z.lt_trichotomy x y) as [Hxy | [Heq | Hyx]];
      [|contradiction|].
    + destruct (Z.eq_dec y (x + 1)) as [Hnext | Hfar].
      * subst y. exfalso. apply Hpreviousy.
        replace (x + 1 - 1) with x by lia. exact Hchosenx.
      * rewrite Z.abs_neq by lia. lia.
    + destruct (Z.eq_dec x (y + 1)) as [Hnext | Hfar].
      * subst x. exfalso. apply Hpreviousx.
        replace (y + 1 - 1) with y by lia. exact Hchoseny.
      * rewrite Z.abs_eq by lia. lia.
Qed.
Lemma selected_nonone_run_starts_bounded__certificate_bootstrap :
  forall a pair_savings (chosen : Z -> Prop),
    PairSavingsPrefix a (Zlength a) pair_savings ->
    #(fun center : Z =>
      1 <= center < Zlength a - 1 /\
      chosen center /\ ~ chosen (center - 1) /\
      Znth (center - 1) a 0 <> 1 /\
      Znth center a 0 <> 1 /\
      Znth (center + 1) a 0 <> 1 /\
      AdjacentCoprime a (center - 1) /\
      AdjacentCoprime a center) <= pair_savings.
Proof.
  intros a pair_savings chosen Hpair.
  apply pair_savings_bounds_every_selection__certificate_bootstrap.
  - exact Hpair.
  - apply selected_nonone_run_starts_form_pair_selection__certificate_bootstrap.
Qed.
Lemma NoDup_firstn__certificate_bootstrap :
  forall (A : Type) (n : nat) (xs : list A),
    NoDup xs -> NoDup (firstn n xs).
Proof.
  intros A n. induction n as [|n IH]; intros xs Hnodup; simpl.
  - constructor.
  - destruct xs as [|x xs]; [constructor |].
    inversion Hnodup as [|? ? Hnotin Htail]; subst.
    constructor.
    + intros Hin. apply Hnotin.
      rewrite <- (firstn_skipn n xs). apply in_or_app. left. exact Hin.
    + apply IH. exact Htail.
Qed.
Lemma NoDup_Znth_injective__certificate_bootstrap :
  forall {A : Type} (default : A) (xs : list A) i j,
    NoDup xs ->
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    Znth i xs default = Znth j xs default ->
    i = j.
Proof.
  intros A default xs i j Hnodup Hi Hj Heq.
  unfold Znth in Heq.
  rewrite Zlength_correct in Hi, Hj.
  pose proof
    ((proj1 (NoDup_nth xs default)) Hnodup
      (Z.to_nat i) (Z.to_nat j) ltac:(lia) ltac:(lia) Heq) as Hij.
  lia.
Qed.
Lemma finite_set_exact_subselection__certificate_bootstrap :
  forall {A : Type} (default : A) (P : A -> Prop) (FP : Finite P) k,
    0 <= k <= @set_card A P FP ->
    exists xs,
      NoDup xs /\
      (forall x, In x xs -> P x) /\
      Zlength xs = k /\
      @set_card A (fun x => P x /\ In x xs)
        (@Finite_subset A P (fun x => In x xs) FP) = k.
Proof.
  intros A default P FP k Hk.
  set (xs := firstn (Z.to_nat k) (@enum A P FP)).
  assert (Henum_length : k <= Z.of_nat (length (@enum A P FP))).
  {
    rewrite <- set_card_as_Zlength__pair_scan_exits. exact (proj2 Hk).
  }
  assert (Hxs_length : Zlength xs = k).
  {
    unfold xs. rewrite Zlength_correct, firstn_length_le.
    - rewrite Z2Nat.id by lia. reflexivity.
    - lia.
  }
  assert (Hxs_nodup : NoDup xs).
  {
    unfold xs. apply NoDup_firstn__certificate_bootstrap.
    apply enum_nodup.
  }
  assert (Hxs_P : forall x, In x xs -> P x).
  {
    intros x Hx. apply (proj2 (@enum_ok A P FP x)).
    unfold xs in Hx.
    rewrite <- (firstn_skipn (Z.to_nat k) (@enum A P FP)).
    apply in_or_app. left. exact Hx.
  }
  exists xs. split; [exact Hxs_nodup |].
  split; [exact Hxs_P |]. split; [exact Hxs_length |].
  apply Z.le_antisymm.
  - replace k with (k - 0) by lia.
    rewrite <- (set_card_Z_range__pair_scan_exits 0 k) by lia.
    eapply set_card_injection_le__pair_scan_exits with
      (Q := fun q : Z => 0 <= q < k)
      (f := fun x =>
        epsilon (inhabits 0%Z)
          (fun q => 0 <= q < Zlength xs /\ Znth q xs default = x)).
    + intros x [HP Hx].
      assert (Hexists : exists q,
        0 <= q < Zlength xs /\ Znth q xs default = x).
      {
        apply In_nth with (d := default) in Hx.
        destruct Hx as [n [Hn Hnth]].
        exists (Z.of_nat n). split.
        - rewrite Zlength_correct. lia.
        - unfold Znth. rewrite Nat2Z.id. exact Hnth.
      }
      pose proof (epsilon_spec
        (inhabits 0%Z)
        (fun q => 0 <= q < Zlength xs /\ Znth q xs default = x)
        Hexists) as Hspec.
      rewrite <- Hxs_length. exact (proj1 Hspec).
    + intros x y Hx Hy Heq.
      assert (Hexistsx : exists q,
        0 <= q < Zlength xs /\ Znth q xs default = x).
      {
        destruct Hx as [_ Hx].
        apply In_nth with (d := default) in Hx.
        destruct Hx as [n [Hn Hnth]].
        exists (Z.of_nat n). split.
        - rewrite Zlength_correct. lia.
        - unfold Znth. rewrite Nat2Z.id. exact Hnth.
      }
      assert (Hexistsy : exists q,
        0 <= q < Zlength xs /\ Znth q xs default = y).
      {
        destruct Hy as [_ Hy].
        apply In_nth with (d := default) in Hy.
        destruct Hy as [n [Hn Hnth]].
        exists (Z.of_nat n). split.
        - rewrite Zlength_correct. lia.
        - unfold Znth. rewrite Nat2Z.id. exact Hnth.
      }
      pose proof (epsilon_spec
        (inhabits 0%Z)
        (fun q => 0 <= q < Zlength xs /\ Znth q xs default = x)
        Hexistsx) as Hspecx.
      pose proof (epsilon_spec
        (inhabits 0%Z)
        (fun q => 0 <= q < Zlength xs /\ Znth q xs default = y)
        Hexistsy) as Hspecy.
      rewrite Heq in Hspecx.
      destruct Hspecx as [_ Hxvalue].
      destruct Hspecy as [_ Hyvalue].
      exact (eq_trans (eq_sym Hxvalue) Hyvalue).
  - replace k with (k - 0) by lia.
    rewrite <- (set_card_Z_range__pair_scan_exits 0 k) by lia.
    eapply set_card_injection_le__pair_scan_exits with
      (f := fun q => Znth q xs default).
    + intros q Hq. split.
      * apply Hxs_P. unfold Znth.
        apply nth_In. change (Z.to_nat q < length xs)%nat.
        rewrite <- (Nat2Z.id (length xs)).
        assert (Hlen0 : 0 <= Z.of_nat (length xs)) by lia.
        apply (proj1 (Z2Nat.inj_lt q (Z.of_nat (length xs))
          (proj1 Hq) Hlen0)).
        rewrite <- Zlength_correct. lia.
      * unfold Znth. apply nth_In.
        change (Z.to_nat q < length xs)%nat.
        rewrite <- (Nat2Z.id (length xs)).
        assert (Hlen0 : 0 <= Z.of_nat (length xs)) by lia.
        apply (proj1 (Z2Nat.inj_lt q (Z.of_nat (length xs))
          (proj1 Hq) Hlen0)).
        rewrite <- Zlength_correct. lia.
    + intros i j Hi Hj Heq.
      eapply (NoDup_Znth_injective__certificate_bootstrap
        default xs i j Hxs_nodup).
      * rewrite Hxs_length. exact Hi.
      * rewrite Hxs_length. exact Hj.
      * exact Heq.
Qed.
Lemma pair_savings_has_exact_subselection__certificate_bootstrap :
  forall a pair_savings use,
    PairSavingsPrefix a (Zlength a) pair_savings ->
    0 <= use <= pair_savings ->
    exists centres selected,
      PairCenterSelection a (Zlength a) centres /\
      NoDup selected /\
      (forall center, In center selected -> centres center) /\
      Zlength selected = use /\
      #(fun center : Z =>
          1 <= center < Zlength a - 1 /\
          centres center /\ In center selected) = use.
Proof.
  intros a pair_savings use Hpair Huse.
  unfold PairSavingsPrefix, max_value_of_subset,
    max_object_of_subset in Hpair.
  destruct Hpair as [centres [[Hcentres _] Hcount]].
  assert (Huse' : 0 <= use <= #(fun center : Z =>
    1 <= center < Zlength a - 1 /\ centres center))
    by (rewrite Hcount; exact Huse).
  destruct (finite_set_exact_subselection__certificate_bootstrap
    0 (fun center : Z =>
      1 <= center < Zlength a - 1 /\ centres center)
    _ use Huse') as [selected [Hnodup [Hinside [Hlen Hselected_card]]]].
  exists centres, selected.
  split; [exact Hcentres |].
  split; [exact Hnodup |].
  split.
  - intros center0 Hin. exact (proj2 (Hinside center0 Hin)).
  - split; [exact Hlen |].
    transitivity (#(fun center0 : Z =>
      (1 <= center0 < Zlength a - 1 /\ centres center0) /\
      In center0 selected)).
    + apply set_card_iff__exam_bridge. intros center0. tauto.
    + exact Hselected_card.
Qed.
Lemma sum_map_succ__certificate_bootstrap :
  forall xs,
    ListLib.sum (map (fun x : Z => x + 1) xs) =
    ListLib.sum xs + Zlength xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl. rewrite IH, Zlength_cons. lia.
Qed.
Lemma stopped_greedy_final_formula__certificate_bootstrap :
  forall sorted next original_k use base_sad remaining sadness out,
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    FinalBudgetResult remaining sadness out ->
    out = Z.max 0 (base_sad - original_k - use - next).
Proof.
  intros sorted next original_k use base_sad remaining sadness out
    [Hnext [Hremaining [Hsadness _]]] Hfinal.
  unfold FinalBudgetResult in Hfinal.
  rewrite sum_map_succ__certificate_bootstrap in Hsadness.
  rewrite Zlength_sublist in Hsadness by lia.
  destruct (Z_le_dec sadness remaining) as [Hsr | Hsr].
  - rewrite Z.min_r in Hfinal by exact Hsr.
    replace (sadness - sadness) with 0 in Hfinal by lia.
    rewrite Z.max_l in Hfinal by lia. subst out.
    symmetry. apply Z.max_l. rewrite Hremaining, Hsadness in Hsr. lia.
  - rewrite Z.min_l in Hfinal by lia.
    rewrite Z.max_r in Hfinal by lia.
    rewrite Z.max_r.
    + rewrite Hfinal, Hremaining, Hsadness. lia.
    + rewrite Hremaining, Hsadness in Hsr. lia.
Qed.
Lemma exact_pair_choice_removed_edges__certificate_bootstrap :
  forall a centres selected,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    PairCenterSelection a (Zlength a) centres ->
    (forall center, In center selected -> centres center) ->
    forall edge,
      (0 <= edge < Zlength a - 1 /\
       Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
       Z.gcd
         (if prop_dec (In edge selected) then 0 else Znth edge a 0)
         (if prop_dec (In (edge + 1) selected) then 0
          else Znth (edge + 1) a 0) <> 1) <->
      exists center, In center selected /\
        (edge = center - 1 \/ edge = center).
Proof.
  intros a centres selected Hnonneg [Hvalid Hspace] Hinside edge.
  split.
  - intros [Hedge [Hcoprime Hremoved]].
    apply transformed_coprime_edge_removed_cases__certificate_bootstrap
      in Hremoved; try (apply Hnonneg; lia); try assumption.
    destruct Hremoved as [[Hleft Hright] |
      [[Hleft _] | [_ [Hright _]]]].
    + exists edge. split; [exact Hleft |]. right. reflexivity.
    + exists edge. split; [exact Hleft |]. right. reflexivity.
    + exists (edge + 1). split; [exact Hright |]. left. lia.
  - intros [center [Hselected [Heq | Heq]]]; subst edge.
    + specialize (Hvalid center (Hinside center Hselected)).
      unfold NonOnePairCenter in Hvalid.
      destruct Hvalid as [Hrange [Hleft [Hcenter [Hright
        [Hedgeleft Hedgeright]]]]].
      unfold AdjacentCoprime in Hedgeleft.
      split; [lia |]. split; [exact (proj2 Hedgeleft) |].
      destruct (prop_dec (In (center - 1) selected)) as [Hprev | Hprev];
        destruct (prop_dec (In (center - 1 + 1) selected))
          as [Hcur | Hcur]; simpl.
      * discriminate.
      * exfalso. apply Hcur. replace (center - 1 + 1) with center by lia.
        exact Hselected.
      * rewrite Z.gcd_0_r_nonneg by (apply Hnonneg; lia). exact Hleft.
      * exfalso. apply Hcur. replace (center - 1 + 1) with center by lia.
        exact Hselected.
    + specialize (Hvalid center (Hinside center Hselected)).
      unfold NonOnePairCenter in Hvalid.
      destruct Hvalid as [Hrange [Hleft [Hcenter [Hright
        [Hedgeleft Hedgeright]]]]].
      unfold AdjacentCoprime in Hedgeright.
      split; [lia |]. split; [exact (proj2 Hedgeright) |].
      destruct (prop_dec (In center selected));
        destruct (prop_dec (In (center + 1) selected)); simpl.
      * discriminate.
      * rewrite Z.gcd_0_l_nonneg by (apply Hnonneg; lia). exact Hright.
      * contradiction.
      * contradiction.
Qed.
Lemma set_card_list_membership__certificate_bootstrap :
  forall (xs : list Z) low high,
    NoDup xs ->
    (forall x, In x xs -> low <= x < high) ->
    #(fun x : Z => low <= x < high /\ In x xs) = Zlength xs.
Proof.
  intros xs low high Hnodup Hrange.
  rewrite set_card_as_Zlength__pair_scan_exits, Zlength_correct.
  f_equal.
  apply Permutation_length.
  apply NoDup_Permutation.
  - apply enum_nodup.
  - exact Hnodup.
  - intros x. rewrite <- enum_ok. split; [tauto |].
    intros Hin. split; [apply Hrange; exact Hin | exact Hin].
Qed.
Lemma exact_pair_edge_image_cardinality__certificate_bootstrap :
  forall a centres selected,
    PairCenterSelection a (Zlength a) centres ->
    NoDup selected ->
    (forall center, In center selected -> centres center) ->
    #(fun edge : Z =>
        0 <= edge < Zlength a - 1 /\
        exists center, In center selected /\
          (edge = center - 1 \/ edge = center)) =
      2 * Zlength selected.
Proof.
  intros a centres selected [Hvalid Hspace] Hnodup Hinside.
  set (Q := fun p : Z * Z =>
    (1 <= fst p < Zlength a - 1 /\ In (fst p) selected) /\
    0 <= snd p < 2).
  assert (FQ : Finite Q).
  {
    unfold Q.
    exact (@Finite_prod Z Z
      (fun center => 1 <= center < Zlength a - 1 /\ In center selected)
      (fun tag => 0 <= tag < 2)
      (@Finite_subset Z
        (fun center => 1 <= center < Zlength a - 1)
        (fun center => In center selected)
        (finite_Z_range 1 (Zlength a - 1)))
      (finite_Z_range 0 2)).
  }
  assert (HQcard : @set_card (Z * Z) Q FQ = 2 * Zlength selected).
  {
    pose (Fcanon := @Finite_prod Z Z
      (fun center => 1 <= center < Zlength a - 1 /\ In center selected)
      (fun tag => 0 <= tag < 2)
      (@Finite_subset Z
        (fun center => 1 <= center < Zlength a - 1)
        (fun center => In center selected)
        (finite_Z_range 1 (Zlength a - 1)))
      (finite_Z_range 0 2)).
    transitivity (@set_card (Z * Z) Q Fcanon).
    - apply set_card_iff__exam_bridge. intros p. reflexivity.
    - unfold Q, Fcanon.
      assert (Hselrange : forall center, In center selected ->
        1 <= center < Zlength a - 1).
      {
        intros center Hselected.
        specialize (Hvalid center (Hinside center Hselected)).
        unfold NonOnePairCenter in Hvalid. lia.
      }
      pose proof (set_card_list_membership__certificate_bootstrap
        selected 1 (Zlength a - 1) Hnodup Hselrange) as Hmember.
      erewrite (@set_card_product__pair_scan_exits Z Z
        (fun center => 1 <= center < Zlength a - 1 /\ In center selected)
        (fun tag => 0 <= tag < 2)).
      assert (Hmember' :
        @set_card Z
          (fun center => 1 <= center < Zlength a - 1 /\ In center selected)
          (@Finite_subset Z
            (fun center => 1 <= center < Zlength a - 1)
            (fun center => In center selected)
            (finite_Z_range 1 (Zlength a - 1))) = Zlength selected).
      {
        transitivity (#(fun center : Z =>
          1 <= center < Zlength a - 1 /\ In center selected)).
        - apply set_card_iff__exam_bridge. intros center. reflexivity.
        - exact Hmember.
      }
      rewrite Hmember'.
      rewrite set_card_Z_range__pair_scan_exits by lia. lia.
  }
  rewrite <- HQcard. apply Z.le_antisymm.
  - eapply set_card_injection_le__pair_scan_exits with
      (f := fun edge =>
        if prop_dec (In edge selected) then (edge, 1) else (edge + 1, 0)).
    + intros edge [Hedge [center [Hselected [Heq | Heq]]]].
      * subst edge.
        destruct (prop_dec (In (center - 1) selected)) as [Hprevious | Hprevious].
        -- exfalso.
           specialize (Hspace (center - 1) center
             (Hinside (center - 1) Hprevious) (Hinside center Hselected)).
           assert (center - 1 <> center) by lia.
           specialize (Hspace H). rewrite Z.abs_eq in Hspace by lia. lia.
        -- pose proof (Hvalid center (Hinside center Hselected)) as Hv.
           unfold NonOnePairCenter in Hv.
           unfold Q. cbn [fst snd]. split.
           ++ split; [lia |]. replace (center - 1 + 1) with center by lia.
              exact Hselected.
           ++ lia.
      * subst edge. destruct (prop_dec (In center selected));
          [|contradiction].
        specialize (Hvalid center (Hinside center Hselected)).
        unfold NonOnePairCenter in Hvalid.
        unfold Q. cbn [fst snd]. split.
        -- split; [lia | exact Hselected].
        -- lia.
    + intros x y Hx Hy Heq.
      destruct (prop_dec (In x selected));
        destruct (prop_dec (In y selected)); inversion Heq; lia.
  - eapply set_card_injection_le__pair_scan_exits with
      (f := fun p => fst p - 1 + snd p).
    + intros [center tag] [[Hcenter Hselected] Htag].
      cbn [fst snd] in *.
      split; [lia |]. exists center. split; [exact Hselected |].
      destruct (Z.eq_dec tag 0) as [-> | Htag0].
      * left. lia.
      * assert (tag = 1) by lia. subst tag. right. lia.
    + intros [x tx] [y ty] [[Hx Hsx] Htx] [[Hy Hsy] Hty] Heq.
      cbn [fst snd] in *.
      assert (x = y).
      {
        destruct (Z.eq_dec x y) as [Hequal | Hneq]; [exact Hequal |].
        specialize (Hspace x y (Hinside x Hsx) (Hinside y Hsy) Hneq).
        destruct (Z_le_gt_dec x y).
        - rewrite Z.abs_eq in Hspace by lia. lia.
        - rewrite Z.abs_neq in Hspace by lia. lia.
      }
      subst y. assert (tx = ty) by lia. subst ty. reflexivity.
Qed.
Lemma exact_pair_phase_attainable__certificate_bootstrap :
  forall a base_sad pair_savings use,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    0 <= use <= pair_savings ->
    exists result,
      SimplifiedExams a use result /\
      ExamSadness result (base_sad - 2 * use).
Proof.
  intros a base_sad pair_savings use Hnonneg Hbase Hpair Huse.
  destruct (pair_savings_has_exact_subselection__certificate_bootstrap
    a pair_savings use Hpair Huse)
    as [centres [selected [Hcentres [Hnodup [Hinside [Hlen Hcard]]]]]].
  assert (Hrange : forall i, In i selected -> 0 <= i < Zlength a).
  {
    intros i Hi. specialize (proj1 Hcentres i (Hinside i Hi)).
    unfold NonOnePairCenter. lia.
  }
  assert (Hchosen_card :
    #(fun i : Z => 0 <= i < Zlength a /\ In i selected) = use).
  {
    rewrite set_card_list_membership__certificate_bootstrap
      with (xs := selected) (low := 0) (high := Zlength a);
      try assumption.
  }
  set (transformed_sad := #(fun edge : Z =>
    0 <= edge < Zlength a - 1 /\
    Z.gcd
      (if prop_dec (In edge selected) then 0 else Znth edge a 0)
      (if prop_dec (In (edge + 1) selected) then 0
       else Znth (edge + 1) a 0) = 1)).
  pose proof (choice_sadness_is_base_minus_removed__certificate_bootstrap
    a (fun i => In i selected) base_sad transformed_sad
    Hnonneg Hbase ltac:(reflexivity)) as Hpartition.
  assert (Hremoved_card :
    #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
      Z.gcd
        (if prop_dec (In edge selected) then 0 else Znth edge a 0)
        (if prop_dec (In (edge + 1) selected) then 0
         else Znth (edge + 1) a 0) <> 1) = 2 * use).
  {
    transitivity (#(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      exists center, In center selected /\
        (edge = center - 1 \/ edge = center))).
    - apply set_card_iff__exam_bridge.
      intros edge.
      pose proof (exact_pair_choice_removed_edges__certificate_bootstrap
        a centres selected Hnonneg Hcentres Hinside edge) as Hiff.
      tauto.
    - rewrite exact_pair_edge_image_cardinality__certificate_bootstrap
        with (centres := centres); try assumption.
      rewrite Hlen. reflexivity.
  }
  cbn beta in Hpartition.
  rewrite Hremoved_card in Hpartition.
  assert (Hsad : transformed_sad = base_sad - 2 * use) by lia.
  subst transformed_sad.
  eapply materialize_exam_choice_sadness__certificate_bootstrap
    with (chosen := fun i => In i selected).
  - exact Hrange.
  - rewrite Hchosen_card. lia.
  - exact (eq_sym Hsad).
Qed.
Lemma map_fst_combine__certificate_bootstrap :
  forall (xs ys : list Z),
    Zlength ys = Zlength xs ->
    map fst (combine xs ys) = xs.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys; reflexivity.
  - destruct ys as [|y ys].
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg xs). lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma lift_length_permutation_to_blocks__certificate_bootstrap :
  forall lengths starts sorted,
    Zlength starts = Zlength lengths ->
    Permutation lengths sorted ->
    exists ordered : list (Z * Z),
      Permutation (combine lengths starts) ordered /\
      map fst ordered = sorted.
Proof.
  intros lengths starts sorted Hlen Hperm.
  assert (Hmap : map fst (combine lengths starts) = lengths).
  { apply map_fst_combine__certificate_bootstrap. exact Hlen. }
  assert (Hsorted : Permutation sorted
    (map fst (combine lengths starts))).
  { rewrite Hmap. apply Permutation_sym. exact Hperm. }
  destruct (@Permutation_map_inv (Z * Z) Z fst sorted
    (combine lengths starts) Hsorted) as [ordered [Heq Hordered]].
  exists ordered. split.
  - exact Hordered.
  - symmetry. exact Heq.
Qed.
Lemma combine_member_has_aligned_index__certificate_bootstrap :
  forall (xs ys : list Z) x y,
    Zlength ys = Zlength xs ->
    In (x, y) (combine xs ys) ->
    exists q, 0 <= q < Zlength xs /\
      Znth q xs 0 = x /\ Znth q ys 0 = y.
Proof.
  induction xs as [|xh xs IH]; intros ys x y Hlen Hin.
  - simpl in Hin. contradiction.
  - destruct ys as [|yh ys].
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg xs). lia.
    + simpl in Hin. destruct Hin as [Heq | Hin].
      * inversion Heq; subst. exists 0. rewrite !Znth0_cons, Zlength_cons.
        repeat split; try reflexivity. pose proof (Zlength_nonneg xs). lia.
      * assert (Htail : Zlength ys = Zlength xs)
          by (rewrite !Zlength_cons in Hlen; lia).
        destruct (IH ys x y Htail Hin) as [q [Hq [Hqx Hqy]]].
        exists (q + 1). rewrite !Znth_cons, Zlength_cons by lia.
        replace (q + 1 - 1) with q by lia.
        repeat split; try assumption; lia.
Qed.
Lemma canonical_profile_sorted_block_pairs__certificate_bootstrap :
  forall a lengths sorted,
    CanonicalInteriorOneRunPrefix a (Zlength a) lengths ->
    Permutation lengths sorted ->
    exists ordered : list (Z * Z),
      map fst ordered = sorted /\
      (forall len start, In (len, start) ordered ->
        InteriorOneBlock a start (start + len)) /\
      (forall len start, In (len, start) ordered ->
        start + len <= Zlength a).
Proof.
  intros a lengths sorted
    [starts [Hlen [Hmono [Hblocks Hcomplete]]]] Hperm.
  destruct (lift_length_permutation_to_blocks__certificate_bootstrap
    lengths starts sorted Hlen Hperm) as [ordered [Hordered Hmap]].
  exists ordered. split; [exact Hmap |]. split.
  - intros len start Hin.
    apply Permutation_sym in Hordered.
    apply (Permutation_in (l := ordered) (l' := combine lengths starts))
      in Hin; [|exact Hordered].
    destruct (combine_member_has_aligned_index__certificate_bootstrap
      lengths starts len start Hlen Hin)
      as [q [Hq [Hqlen Hqstart]]].
    specialize (Hblocks q Hq). rewrite Hqlen, Hqstart in Hblocks.
    exact (proj1 Hblocks).
  - intros len start Hin.
    apply Permutation_sym in Hordered.
    apply (Permutation_in (l := ordered) (l' := combine lengths starts))
      in Hin; [|exact Hordered].
    destruct (combine_member_has_aligned_index__certificate_bootstrap
      lengths starts len start Hlen Hin)
      as [q [Hq [Hqlen Hqstart]]].
    specialize (Hblocks q Hq). rewrite Hqlen, Hqstart in Hblocks.
    exact (proj2 Hblocks).
Qed.
Lemma block_vertex_source_cardinality__certificate_bootstrap :
  forall (lengths : list Z) high,
    (forall q, 0 <= q < Zlength lengths ->
      0 <= Znth q lengths 0 <= high) ->
    @set_card (Z * Z)
      (fun p =>
        (0 <= fst p < Zlength lengths /\ 0 <= snd p < high) /\
        snd p < Znth (fst p) lengths 0)
      (@Finite_subset (Z * Z)
        (fun p =>
          0 <= fst p < Zlength lengths /\ 0 <= snd p < high)
        (fun p => snd p < Znth (fst p) lengths 0)
        (@Finite_prod Z Z
          (fun q => 0 <= q < Zlength lengths)
          (fun t => 0 <= t < high)
          (finite_Z_range 0 (Zlength lengths))
          (finite_Z_range 0 high))) =
    ListLib.sum lengths.
Proof.
  intros lengths high Hbounds.
  rewrite set_card_rect_subset_as_nested_sum__certificate_bootstrap.
  rewrite (SumLib.ZRange.list_sum_as_Z_range_sum lengths).
  apply SumLib.ZRange.sum_Z_range_ext.
  intros q Hq.
  change (SumLib.Sum.sum (fun y : Z => 0 <= y < high)
    (fun y => if prop_dec (y < Znth q lengths 0) then 1 else 0) =
    Znth q lengths 0).
  apply sum_indicator_initial_segment__certificate_bootstrap.
  apply Hbounds. exact Hq.
Qed.
Lemma sublist_zero_as_firstn__certificate_bootstrap :
  forall {A : Type} (xs : list A) k,
    sublist 0 k xs = firstn (Z.to_nat k) xs.
Proof.
  intros A xs k. unfold sublist. simpl. reflexivity.
Qed.
Lemma distinct_interior_one_blocks_disjoint__certificate_bootstrap :
  forall a lo hi lo' hi',
    InteriorOneBlock a lo hi ->
    InteriorOneBlock a lo' hi' ->
    lo <> lo' ->
    hi < lo' \/ hi' < lo.
Proof.
  intros a lo hi lo' hi' Hblock Hblock' Hneq.
  unfold InteriorOneBlock in Hblock, Hblock'.
  destruct Hblock as [Hlo [Hhi [Hleft [Hright Hones]]]].
  destruct Hblock' as [Hlo' [Hhi' [Hleft' [Hright' Hones']]]].
  destruct (Z.lt_trichotomy lo lo') as [Horder | [Heq | Horder]].
  - left. destruct (Z_lt_ge_dec hi lo') as [Hsep | Hover]; [exact Hsep |].
    destruct (Z.eq_dec hi lo') as [Heqend | Hneqend].
    + subst lo'. exfalso. apply Hright. apply Hones'. lia.
    + exfalso. apply Hleft'. apply Hones. lia.
  - contradiction.
  - right. destruct (Z_lt_ge_dec hi' lo) as [Hsep | Hover]; [exact Hsep |].
    destruct (Z.eq_dec hi' lo) as [Heqend | Hneqend].
    + subst lo. exfalso. apply Hright'. apply Hones. lia.
    + exfalso. apply Hleft. apply Hones'. lia.
Qed.
Lemma indexed_block_vertex_map_injective__certificate_bootstrap :
  forall a (ordered : list (Z * Z)) high,
    NoDup ordered ->
    (forall q q', 0 <= q < Zlength ordered ->
      0 <= q' < Zlength ordered ->
      snd (Znth q ordered (0, 0)) = snd (Znth q' ordered (0, 0)) ->
      q = q') ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) + fst (Znth q ordered (0, 0)))) ->
    forall p r,
      ((0 <= fst p < Zlength ordered /\ 0 <= snd p < high) /\
        snd p < fst (Znth (fst p) ordered (0, 0))) ->
      ((0 <= fst r < Zlength ordered /\ 0 <= snd r < high) /\
        snd r < fst (Znth (fst r) ordered (0, 0))) ->
      snd (Znth (fst p) ordered (0, 0)) + snd p =
        snd (Znth (fst r) ordered (0, 0)) + snd r ->
      p = r.
Proof.
  intros a ordered high Hnodup Hstartinj Hblocks [q t] [q' t']
    [[Hq Ht] Htlen] [[Hq' Ht'] Htlen'] Heq.
  cbn [fst snd] in *.
  destruct (Z.eq_dec q q') as [-> | Hneq].
  - assert (t = t') by lia. subst t'. reflexivity.
  - pose proof (Hblocks q Hq) as Hb.
    pose proof (Hblocks q' Hq') as Hb'.
    pose proof (distinct_interior_one_blocks_disjoint__certificate_bootstrap
      a
      (snd (Znth q ordered (0, 0)))
      (snd (Znth q ordered (0, 0)) + fst (Znth q ordered (0, 0)))
      (snd (Znth q' ordered (0, 0)))
      (snd (Znth q' ordered (0, 0)) + fst (Znth q' ordered (0, 0)))
      Hb Hb') as Hdisjoint.
    assert (snd (Znth q ordered (0, 0)) <>
      snd (Znth q' ordered (0, 0))).
    {
      intro Hstarts. apply Hneq. apply Hstartinj; assumption.
    }
    specialize (Hdisjoint H).
    destruct Hdisjoint; lia.
Qed.
Lemma mono_inc_NoDup__certificate_bootstrap :
  forall xs, mono_inc xs -> NoDup xs.
Proof.
  induction xs as [|x xs IH]; intros Hmono; [constructor |].
  rewrite mono_inc_cons in Hmono. destruct Hmono as [Hall Htail].
  constructor.
  - intro Hin. rewrite Forall_forall in Hall.
    specialize (Hall x Hin). lia.
  - apply IH. exact Htail.
Qed.
Lemma combine_NoDup_from_right__certificate_bootstrap :
  forall (xs ys : list Z),
    Zlength ys = Zlength xs ->
    NoDup ys ->
    NoDup (combine xs ys).
Proof.
  induction xs as [|x xs IH]; intros ys Hlen Hnodup.
  - simpl. constructor.
  - destruct ys as [|y ys].
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg xs). lia.
    + simpl. inversion Hnodup as [|? ? Hnotin Htail]; subst.
      constructor.
      * intro Hin. apply in_combine_r in Hin. contradiction.
      * apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- exact Htail.
Qed.
Lemma Znth_In_range__certificate_bootstrap :
  forall {A : Type} (default : A) xs i,
    0 <= i < Zlength xs -> In (Znth i xs default) xs.
Proof.
  intros A default xs i Hi. unfold Znth.
  apply nth_In. rewrite Zlength_correct in Hi. lia.
Qed.
Lemma canonical_profile_sorted_block_pairs_strong__certificate_bootstrap :
  forall a lengths sorted,
    CanonicalInteriorOneRunPrefix a (Zlength a) lengths ->
    Permutation lengths sorted ->
    exists ordered : list (Z * Z),
      map fst ordered = sorted /\
      NoDup ordered /\
      (forall q, 0 <= q < Zlength ordered ->
        InteriorOneBlock a (snd (Znth q ordered (0, 0)))
          (snd (Znth q ordered (0, 0)) +
           fst (Znth q ordered (0, 0)))) /\
      (forall q, 0 <= q < Zlength ordered ->
        snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)) <= Zlength a) /\
      (forall q r, 0 <= q < Zlength ordered ->
        0 <= r < Zlength ordered ->
        snd (Znth q ordered (0, 0)) =
          snd (Znth r ordered (0, 0)) -> q = r).
Proof.
  intros a lengths sorted
    [starts [Hlen [Hmono [Hblocks Hcomplete]]]] Hperm.
  destruct (lift_length_permutation_to_blocks__certificate_bootstrap
    lengths starts sorted Hlen Hperm) as [ordered [Hordered Hmap]].
  assert (Hsource_nodup : NoDup (combine lengths starts)).
  {
    apply combine_NoDup_from_right__certificate_bootstrap; [exact Hlen |].
    apply mono_inc_NoDup__certificate_bootstrap. exact Hmono.
  }
  assert (Hordered_nodup : NoDup ordered).
  { eapply Permutation_NoDup; [exact Hordered | exact Hsource_nodup]. }
  assert (Haligned : forall p, In p ordered ->
    exists u, 0 <= u < Zlength lengths /\
      Znth u lengths 0 = fst p /\ Znth u starts 0 = snd p).
  {
    intros [len start] Hin.
    assert (Hinsource : In (len, start) (combine lengths starts)).
    { eapply Permutation_in; [apply Permutation_sym; exact Hordered | exact Hin]. }
    destruct (combine_member_has_aligned_index__certificate_bootstrap
      lengths starts len start Hlen Hinsource)
      as [u [Hu [Hulen Hustart]]].
    exists u. cbn [fst snd]. split; [exact Hu |].
    split; assumption.
  }
  exists ordered. split; [exact Hmap |].
  split; [exact Hordered_nodup |].
  split.
  - intros q Hq.
    pose proof (Znth_In_range__certificate_bootstrap
      (0, 0) ordered q Hq) as Hin.
    destruct (Haligned (Znth q ordered (0, 0)) Hin)
      as [u [Hu [Hulen Hustart]]].
    specialize (Hblocks u Hu). rewrite Hulen, Hustart in Hblocks.
    exact (proj1 Hblocks).
  - split.
    + intros q Hq.
      pose proof (Znth_In_range__certificate_bootstrap
        (0, 0) ordered q Hq) as Hin.
      destruct (Haligned (Znth q ordered (0, 0)) Hin)
        as [u [Hu [Hulen Hustart]]].
      specialize (Hblocks u Hu). rewrite Hulen, Hustart in Hblocks.
      exact (proj2 Hblocks).
    + intros q r Hq Hr Hstarts.
      pose proof (Znth_In_range__certificate_bootstrap
        (0, 0) ordered q Hq) as Hinq.
      pose proof (Znth_In_range__certificate_bootstrap
        (0, 0) ordered r Hr) as Hinr.
      destruct (Haligned (Znth q ordered (0, 0)) Hinq)
        as [u [Hu [Hulen Hustart]]].
      destruct (Haligned (Znth r ordered (0, 0)) Hinr)
        as [v [Hv [Hvlen Hvstart]]].
      assert (u = v).
      {
        destruct (Z.lt_trichotomy u v) as [Huv | [Heq | Hvu]].
        - specialize (Hmono u v ltac:(lia) ltac:(lia) ltac:(lia)).
          rewrite Hustart, Hvstart in Hmono. lia.
        - exact Heq.
        - specialize (Hmono v u ltac:(lia) ltac:(lia) ltac:(lia)).
          rewrite Hustart, Hvstart in Hmono. lia.
      }
      subst v.
      assert (Hpairs : Znth q ordered (0, 0) =
        Znth r ordered (0, 0)).
      {
        rewrite (surjective_pairing (Znth q ordered (0, 0))).
        rewrite (surjective_pairing (Znth r ordered (0, 0))).
        f_equal; congruence.
      }
      eapply NoDup_Znth_injective__certificate_bootstrap; eauto.
Qed.
Lemma firstn_Zlength_exact__certificate_bootstrap :
  forall {A : Type} (xs : list A) k,
    0 <= k <= Zlength xs ->
    Zlength (firstn (Z.to_nat k) xs) = k.
Proof.
  intros A xs k Hk. rewrite Zlength_correct, firstn_length_le.
  - rewrite Z2Nat.id by lia. reflexivity.
  - rewrite Zlength_correct in Hk. lia.
Qed.
Lemma Znth_firstn_exact__certificate_bootstrap :
  forall {A : Type} (default : A) xs k i,
    0 <= k <= Zlength xs ->
    0 <= i < k ->
    Znth i (firstn (Z.to_nat k) xs) default = Znth i xs default.
Proof.
  intros A default xs k i Hk Hi. unfold Znth.
  assert (Hnat : (Z.to_nat i < Z.to_nat k)%nat).
  {
    pose proof (Z2Nat.inj_lt i k ltac:(lia) ltac:(lia)) as Hiff.
    apply (proj1 Hiff). lia.
  }
  apply nth_firstn. exact Hnat.
Qed.
Lemma sorted_ordered_prefix_properties__certificate_bootstrap :
  forall a sorted (ordered : list (Z * Z)) next,
    map fst ordered = sorted ->
    NoDup ordered ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) + fst (Znth q ordered (0, 0)))) ->
    (forall q r, 0 <= q < Zlength ordered ->
      0 <= r < Zlength ordered ->
      snd (Znth q ordered (0, 0)) = snd (Znth r ordered (0, 0)) ->
      q = r) ->
    0 <= next <= Zlength ordered ->
    exists prefix,
      prefix = firstn (Z.to_nat next) ordered /\
      Zlength prefix = next /\
      map fst prefix = sublist 0 next sorted /\
      NoDup prefix /\
      (forall q, 0 <= q < Zlength prefix ->
        InteriorOneBlock a (snd (Znth q prefix (0, 0)))
          (snd (Znth q prefix (0, 0)) + fst (Znth q prefix (0, 0)))) /\
      (forall q r, 0 <= q < Zlength prefix ->
        0 <= r < Zlength prefix ->
        snd (Znth q prefix (0, 0)) = snd (Znth r prefix (0, 0)) ->
        q = r).
Proof.
  intros a sorted ordered next Hmap Hnodup Hblocks Hstartinj Hnext.
  exists (firstn (Z.to_nat next) ordered).
  split; [reflexivity |].
  assert (Hplen : Zlength (firstn (Z.to_nat next) ordered) = next)
    by (apply firstn_Zlength_exact__certificate_bootstrap; exact Hnext).
  split; [exact Hplen |]. split.
  - rewrite <- Hmap, <- firstn_map.
    rewrite sublist_zero_as_firstn__certificate_bootstrap. reflexivity.
  - split.
    + apply NoDup_firstn__certificate_bootstrap. exact Hnodup.
    + split.
      * intros q Hq.
        rewrite !Znth_firstn_exact__certificate_bootstrap by lia.
        apply Hblocks. lia.
      * intros q r Hq Hr Heq.
        rewrite !Znth_firstn_exact__certificate_bootstrap in Heq by lia.
        apply Hstartinj; lia.
Qed.
Lemma indexed_block_vertex_union_cardinality__certificate_bootstrap :
  forall a (ordered : list (Z * Z)) high,
    NoDup ordered ->
    (forall q r, 0 <= q < Zlength ordered ->
      0 <= r < Zlength ordered ->
      snd (Znth q ordered (0, 0)) = snd (Znth r ordered (0, 0)) ->
      q = r) ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)))) ->
    (forall q, 0 <= q < Zlength ordered ->
      0 <= fst (Znth q ordered (0, 0)) <= high) ->
    #(fun i : Z =>
        0 <= i < Zlength a /\
        exists q, 0 <= q < Zlength ordered /\
          snd (Znth q ordered (0, 0)) <= i <
          snd (Znth q ordered (0, 0)) +
            fst (Znth q ordered (0, 0))) =
      ListLib.sum (map fst ordered).
Proof.
  intros a ordered high Hnodup Hstartinj Hblocks Hlengths.
  set (Source := fun p : Z * Z =>
    (0 <= fst p < Zlength (map fst ordered) /\
      0 <= snd p < high) /\
    snd p < Znth (fst p) (map fst ordered) 0).
  pose (FSource := @Finite_subset (Z * Z)
    (fun p => 0 <= fst p < Zlength (map fst ordered) /\
      0 <= snd p < high)
    (fun p => snd p < Znth (fst p) (map fst ordered) 0)
    (@Finite_prod Z Z
      (fun q => 0 <= q < Zlength (map fst ordered))
      (fun t => 0 <= t < high)
      (finite_Z_range 0 (Zlength (map fst ordered)))
      (finite_Z_range 0 high))).
  assert (Hsource_card : @set_card (Z * Z) Source FSource =
    ListLib.sum (map fst ordered)).
  {
    unfold Source.
    apply block_vertex_source_cardinality__certificate_bootstrap.
    intros q Hq.
    rewrite Zlength_map__certificate_bootstrap in Hq.
    rewrite Znth_map__certificate_bootstrap with
      (da := (0, 0)) (db := 0) by exact Hq.
    apply Hlengths. exact Hq.
  }
  rewrite <- Hsource_card. apply Z.le_antisymm.
  - eapply set_card_injection_le__pair_scan_exits with
      (f := fun i =>
        let q := epsilon (inhabits 0%Z)
          (fun q => 0 <= q < Zlength ordered /\
            snd (Znth q ordered (0, 0)) <= i <
            snd (Znth q ordered (0, 0)) +
              fst (Znth q ordered (0, 0))) in
        (q, i - snd (Znth q ordered (0, 0)))).
    + intros i [Hi Hex].
      pose proof (epsilon_spec (inhabits 0%Z)
        (fun q => 0 <= q < Zlength ordered /\
          snd (Znth q ordered (0, 0)) <= i <
          snd (Znth q ordered (0, 0)) +
            fst (Znth q ordered (0, 0))) Hex) as Hq.
      destruct Hq as [Hqrange Hioffset].
      unfold Source. cbn [fst snd].
      rewrite Zlength_map__certificate_bootstrap.
      split.
      * split; [exact Hqrange |].
        pose proof (Hlengths
          (epsilon (inhabits 0%Z)
            (fun q => 0 <= q < Zlength ordered /\
              snd (Znth q ordered (0, 0)) <= i <
              snd (Znth q ordered (0, 0)) +
                fst (Znth q ordered (0, 0)))) Hqrange) as Hlenbound.
        lia.
      * rewrite Znth_map__certificate_bootstrap with
          (da := (0, 0)) (db := 0) by exact Hqrange.
        lia.
    + intros i j Hi Hj Heq.
      cbn [fst snd] in Heq.
      inversion Heq. lia.
  - eapply set_card_injection_le__pair_scan_exits with
      (f := fun p =>
        snd (Znth (fst p) ordered (0, 0)) + snd p).
    + intros [q t] Hsource. unfold Source in Hsource.
      cbn [fst snd] in *.
      destruct Hsource as [[Hq Ht] Htlen].
      rewrite Zlength_map__certificate_bootstrap in Hq.
      rewrite Znth_map__certificate_bootstrap with
        (da := (0, 0)) (db := 0) in Htlen by exact Hq.
      pose proof (Hblocks q Hq) as Hblock.
      unfold InteriorOneBlock in Hblock.
      split; [lia |]. exists q. split; [exact Hq |]. lia.
    + intros [q t] [r u] Hp Hr Heq.
      unfold Source in Hp, Hr. cbn [fst snd] in *.
      destruct Hp as [[Hq Ht] Htlen].
      destruct Hr as [[Hr Hu] Hulen].
      rewrite Zlength_map__certificate_bootstrap in Hq, Hr.
      rewrite Znth_map__certificate_bootstrap with
        (da := (0, 0)) (db := 0) in Htlen by exact Hq.
      rewrite Znth_map__certificate_bootstrap with
        (da := (0, 0)) (db := 0) in Hulen by exact Hr.
      eapply (indexed_block_vertex_map_injective__certificate_bootstrap
        a ordered high Hnodup Hstartinj Hblocks (q, t) (r, u));
        cbn [fst snd]; eauto.
Qed.
Lemma indexed_block_edge_map_injective__certificate_bootstrap :
  forall a (ordered : list (Z * Z)) high,
    (forall q r, 0 <= q < Zlength ordered ->
      0 <= r < Zlength ordered ->
      snd (Znth q ordered (0, 0)) = snd (Znth r ordered (0, 0)) ->
      q = r) ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)))) ->
    forall p r,
      ((0 <= fst p < Zlength ordered /\ 0 <= snd p < high) /\
        snd p < fst (Znth (fst p) ordered (0, 0)) + 1) ->
      ((0 <= fst r < Zlength ordered /\ 0 <= snd r < high) /\
        snd r < fst (Znth (fst r) ordered (0, 0)) + 1) ->
      snd (Znth (fst p) ordered (0, 0)) - 1 + snd p =
        snd (Znth (fst r) ordered (0, 0)) - 1 + snd r ->
      p = r.
Proof.
  intros a ordered high Hstartinj Hblocks [q t] [r u]
    [[Hq Ht] Htlen] [[Hr Hu] Hulen] Heq.
  cbn [fst snd] in *.
  destruct (Z.eq_dec q r) as [-> | Hneq].
  - assert (t = u) by lia. subst u. reflexivity.
  - pose proof (Hblocks q Hq) as Hb.
    pose proof (Hblocks r Hr) as Hb'.
    assert (Hstarts : snd (Znth q ordered (0, 0)) <>
      snd (Znth r ordered (0, 0))).
    { intro Hsame. apply Hneq. apply Hstartinj; assumption. }
    pose proof (distinct_interior_one_blocks_disjoint__certificate_bootstrap
      a
      (snd (Znth q ordered (0, 0)))
      (snd (Znth q ordered (0, 0)) + fst (Znth q ordered (0, 0)))
      (snd (Znth r ordered (0, 0)))
      (snd (Znth r ordered (0, 0)) + fst (Znth r ordered (0, 0)))
      Hb Hb' Hstarts) as Hdisjoint.
    destruct Hdisjoint; lia.
Qed.
Lemma indexed_block_edge_union_cardinality__certificate_bootstrap :
  forall a (ordered : list (Z * Z)) high,
    (forall q r, 0 <= q < Zlength ordered ->
      0 <= r < Zlength ordered ->
      snd (Znth q ordered (0, 0)) = snd (Znth r ordered (0, 0)) ->
      q = r) ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)))) ->
    (forall q, 0 <= q < Zlength ordered ->
      0 <= fst (Znth q ordered (0, 0)) + 1 <= high) ->
    #(fun edge : Z =>
        0 <= edge < Zlength a - 1 /\
        exists q, 0 <= q < Zlength ordered /\
          snd (Znth q ordered (0, 0)) - 1 <= edge <
          snd (Znth q ordered (0, 0)) +
            fst (Znth q ordered (0, 0))) =
      ListLib.sum (map (fun len => len + 1) (map fst ordered)).
Proof.
  intros a ordered high Hstartinj Hblocks Hlengths.
  set (Source := fun p : Z * Z =>
    (0 <= fst p < Zlength (map fst ordered) /\
      0 <= snd p < high) /\
    snd p < Znth (fst p) (map fst ordered) 0 + 1).
  pose (FSource := @Finite_subset (Z * Z)
    (fun p => 0 <= fst p < Zlength (map fst ordered) /\
      0 <= snd p < high)
    (fun p => snd p < Znth (fst p) (map fst ordered) 0 + 1)
    (@Finite_prod Z Z
      (fun q => 0 <= q < Zlength (map fst ordered))
      (fun t => 0 <= t < high)
      (finite_Z_range 0 (Zlength (map fst ordered)))
      (finite_Z_range 0 high))).
  assert (Hsource_card : @set_card (Z * Z) Source FSource =
    ListLib.sum (map (fun len => len + 1) (map fst ordered))).
  {
    unfold Source.
    apply block_charge_source_cardinality__certificate_bootstrap.
    intros q Hq.
    rewrite Zlength_map__certificate_bootstrap in Hq.
    rewrite Znth_map__certificate_bootstrap with
      (da := (0, 0)) (db := 0) by exact Hq.
    apply Hlengths. exact Hq.
  }
  rewrite <- Hsource_card. apply Z.le_antisymm.
  - eapply set_card_injection_le__pair_scan_exits with
      (f := fun edge =>
        let q := epsilon (inhabits 0%Z)
          (fun q => 0 <= q < Zlength ordered /\
            snd (Znth q ordered (0, 0)) - 1 <= edge <
            snd (Znth q ordered (0, 0)) +
              fst (Znth q ordered (0, 0))) in
        (q, edge - (snd (Znth q ordered (0, 0)) - 1))).
    + intros edge [Hedge Hex].
      pose proof (epsilon_spec (inhabits 0%Z)
        (fun q => 0 <= q < Zlength ordered /\
          snd (Znth q ordered (0, 0)) - 1 <= edge <
          snd (Znth q ordered (0, 0)) +
            fst (Znth q ordered (0, 0))) Hex) as Hq.
      destruct Hq as [Hqrange Hedgeoffset].
      unfold Source. cbn [fst snd].
      rewrite Zlength_map__certificate_bootstrap.
      split.
      * split; [exact Hqrange |].
        pose proof (Hlengths
          (epsilon (inhabits 0%Z)
            (fun q => 0 <= q < Zlength ordered /\
              snd (Znth q ordered (0, 0)) - 1 <= edge <
              snd (Znth q ordered (0, 0)) +
                fst (Znth q ordered (0, 0)))) Hqrange) as Hlenbound.
        lia.
      * rewrite Znth_map__certificate_bootstrap with
          (da := (0, 0)) (db := 0) by exact Hqrange.
        lia.
    + intros i j Hi Hj Heq. cbn [fst snd] in Heq.
      inversion Heq. lia.
  - eapply set_card_injection_le__pair_scan_exits with
      (f := fun p =>
        snd (Znth (fst p) ordered (0, 0)) - 1 + snd p).
    + intros [q t] Hsource. unfold Source in Hsource.
      cbn [fst snd] in *.
      destruct Hsource as [[Hq Ht] Htlen].
      rewrite Zlength_map__certificate_bootstrap in Hq.
      rewrite Znth_map__certificate_bootstrap with
        (da := (0, 0)) (db := 0) in Htlen by exact Hq.
      pose proof (Hblocks q Hq) as Hblock.
      unfold InteriorOneBlock in Hblock.
      split; [lia |]. exists q. split; [exact Hq |]. lia.
    + intros [q t] [r u] Hp Hr Heq.
      unfold Source in Hp, Hr. cbn [fst snd] in *.
      destruct Hp as [[Hq Ht] Htlen].
      destruct Hr as [[Hr Hu] Hulen].
      rewrite Zlength_map__certificate_bootstrap in Hq, Hr.
      rewrite Znth_map__certificate_bootstrap with
        (da := (0, 0)) (db := 0) in Htlen by exact Hq.
      rewrite Znth_map__certificate_bootstrap with
        (da := (0, 0)) (db := 0) in Hulen by exact Hr.
      eapply (indexed_block_edge_map_injective__certificate_bootstrap
        a ordered high Hstartinj Hblocks (q, t) (r, u));
        cbn [fst snd]; eauto.
Qed.
Lemma structured_pair_block_choice_cardinality__certificate_bootstrap :
  forall a centres selected (ordered : list (Z * Z)),
    PairCenterSelection a (Zlength a) centres ->
    NoDup selected ->
    NoDup ordered ->
    (forall center, In center selected -> centres center) ->
    (forall q r, 0 <= q < Zlength ordered ->
      0 <= r < Zlength ordered ->
      snd (Znth q ordered (0, 0)) = snd (Znth r ordered (0, 0)) ->
      q = r) ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)))) ->
    #(fun i : Z => 0 <= i < Zlength a /\
        (In i selected \/
         exists q, 0 <= q < Zlength ordered /\
           snd (Znth q ordered (0, 0)) <= i <
           snd (Znth q ordered (0, 0)) +
             fst (Znth q ordered (0, 0)))) =
      Zlength selected + ListLib.sum (map fst ordered).
Proof.
  intros a centres selected ordered Hcentres Hnodup Horderednodup Hinside
    Hstartinj Hblocks.
  set (BlockVertex := fun i : Z =>
    exists q, 0 <= q < Zlength ordered /\
      snd (Znth q ordered (0, 0)) <= i <
      snd (Znth q ordered (0, 0)) +
        fst (Znth q ordered (0, 0))).
  change (#(fun i : Z => 0 <= i < Zlength a /\
    (In i selected \/ BlockVertex i)) =
    Zlength selected + ListLib.sum (map fst ordered)).
  assert (Hselected_range : forall i, In i selected ->
    0 <= i < Zlength a).
  {
    intros i Hi.
    pose proof (proj1 Hcentres i (Hinside i Hi)) as Hvalid.
    unfold NonOnePairCenter in Hvalid. lia.
  }
  assert (Hdisjoint : forall i, In i selected -> ~ BlockVertex i).
  {
    intros i Hi [q [Hq Hiblock]].
    pose proof (canonical_profile_pair_block_disjoint__certificate_bootstrap
      a (map fst ordered) (map snd ordered) centres) as Hdisj_helper.
    assert (Hlenmaps : Zlength (map snd ordered) =
      Zlength (map fst ordered)).
    { rewrite !Zlength_correct, !length_map. reflexivity. }
    assert (Hmapblocks : forall r, 0 <= r < Zlength (map fst ordered) ->
      InteriorOneBlock a (Znth r (map snd ordered) 0)
        (Znth r (map snd ordered) 0 + Znth r (map fst ordered) 0)).
    {
      intros r Hr. rewrite Zlength_map__certificate_bootstrap in Hr.
      rewrite !Znth_map__certificate_bootstrap with
        (da := (0, 0)) by exact Hr.
      apply Hblocks. exact Hr.
    }
    specialize (Hdisj_helper Hlenmaps Hmapblocks Hcentres i q
      (Hinside i Hi)).
    rewrite Zlength_map__certificate_bootstrap in Hdisj_helper.
    specialize (Hdisj_helper Hq).
    rewrite !Znth_map__certificate_bootstrap with
      (da := (0, 0)) in Hdisj_helper by exact Hq.
    destruct Hdisj_helper; lia.
  }
  pose proof (set_card_partition_subset_Z__certificate_bootstrap
    0 (Zlength a)
    (fun i => In i selected \/ BlockVertex i)
    (fun i => In i selected)) as Hpartition.
  specialize (Hpartition ltac:(intros; tauto)).
  rewrite Hpartition.
  rewrite set_card_list_membership__certificate_bootstrap with
    (xs := selected) (low := 0) (high := Zlength a);
    try assumption.
  assert (Hrest :
    #(fun i : Z => 0 <= i < Zlength a /\
      (In i selected \/ BlockVertex i) /\ ~ In i selected) =
    #(fun i : Z => 0 <= i < Zlength a /\ BlockVertex i)).
  {
    apply set_card_iff__exam_bridge. intros i. split.
    - intros [Hi [[Hsel | Hblock] Hnot]]; [contradiction | tauto].
    - intros [Hi Hblock]. split; [exact Hi |]. split.
      * right. exact Hblock.
      * intro Hsel. exact (Hdisjoint i Hsel Hblock).
  }
  rewrite Hrest.
  unfold BlockVertex.
  rewrite (indexed_block_vertex_union_cardinality__certificate_bootstrap
    a ordered (Zlength a) Horderednodup Hstartinj Hblocks).
  - reflexivity.
  - intros q Hq. pose proof (Hblocks q Hq) as Hb.
    unfold InteriorOneBlock in Hb. lia.
Qed.
Lemma structured_pair_block_choice_removed_edges__certificate_bootstrap :
  forall a centres selected (ordered : list (Z * Z)),
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    PairCenterSelection a (Zlength a) centres ->
    (forall center, In center selected -> centres center) ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)))) ->
    forall edge,
      let chosen := fun i : Z =>
        In i selected \/
        exists q, 0 <= q < Zlength ordered /\
          snd (Znth q ordered (0, 0)) <= i <
          snd (Znth q ordered (0, 0)) +
            fst (Znth q ordered (0, 0)) in
      (0 <= edge < Zlength a - 1 /\
       Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
       Z.gcd
         (if prop_dec (chosen edge) then 0 else Znth edge a 0)
         (if prop_dec (chosen (edge + 1)) then 0
          else Znth (edge + 1) a 0) <> 1) <->
      (exists center, In center selected /\
        (edge = center - 1 \/ edge = center)) \/
      (exists q, 0 <= q < Zlength ordered /\
        snd (Znth q ordered (0, 0)) - 1 <= edge <
        snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0))).
Proof.
  intros a centres selected ordered Hnonneg Hcentres Hinside Hblocks edge.
  cbn zeta.
  set (chosen := fun i : Z =>
    In i selected \/
    exists q, 0 <= q < Zlength ordered /\
      snd (Znth q ordered (0, 0)) <= i <
      snd (Znth q ordered (0, 0)) +
        fst (Znth q ordered (0, 0))).
  change
    (0 <= edge < Zlength a - 1 /\
     Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
     Z.gcd
       (if prop_dec (chosen edge) then 0 else Znth edge a 0)
       (if prop_dec (chosen (edge + 1)) then 0
        else Znth (edge + 1) a 0) <> 1 <->
      (exists center, In center selected /\
        (edge = center - 1 \/ edge = center)) \/
      (exists q, 0 <= q < Zlength ordered /\
        snd (Znth q ordered (0, 0)) - 1 <= edge <
        snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)))).
  split.
  - intros [Hedge [Hcoprime Hremoved]].
    apply transformed_coprime_edge_removed_cases__certificate_bootstrap
      in Hremoved; try (apply Hnonneg; lia); try assumption.
    destruct Hremoved as [[Hleft Hright] |
      [[Hleft Hnotright] | [Hnotleft [Hright Hleftnonone]]]].
    + destruct Hleft as [Hsel | [q [Hq Hvertex]]].
      * left. exists edge. tauto.
      * right. exists q. split; [exact Hq |]. lia.
    + destruct Hleft as [Hsel | [q [Hq Hvertex]]].
      * left. exists edge. tauto.
      * right. exists q. split; [exact Hq |]. lia.
    + destruct Hright as [Hsel | [q [Hq Hvertex]]].
      * left. exists (edge + 1). split; [exact Hsel |]. left. lia.
      * right. exists q. split; [exact Hq |]. lia.
  - intros [Hpair | Hblockedge].
    + destruct Hpair as [center [Hsel [-> | ->]]].
      * pose proof (proj1 Hcentres center (Hinside center Hsel)) as Hv.
        unfold NonOnePairCenter in Hv.
        destruct Hv as [Hrange [Hleft [Hcenter [Hright
          [Hedgeleft Hedgeright]]]]].
        unfold AdjacentCoprime in Hedgeleft.
        split; [lia |]. split; [exact (proj2 Hedgeleft) |].
        apply transformed_coprime_edge_removed_cases__certificate_bootstrap;
          try (apply Hnonneg; lia); try exact (proj2 Hedgeleft).
        assert (Hchosen : chosen center).
        { unfold chosen. left. exact Hsel. }
        destruct (prop_dec (chosen (center - 1))) as [Hprev | Hprev].
        -- left. split; [exact Hprev |].
           replace (center - 1 + 1) with center by lia. exact Hchosen.
        -- right. right. split; [exact Hprev |]. split.
           ++ replace (center - 1 + 1) with center by lia. exact Hchosen.
           ++ exact Hleft.
      * pose proof (proj1 Hcentres center (Hinside center Hsel)) as Hv.
        unfold NonOnePairCenter in Hv.
        destruct Hv as [Hrange [Hleft [Hcenter [Hright
          [Hedgeleft Hedgeright]]]]].
        unfold AdjacentCoprime in Hedgeright.
        split; [lia |]. split; [exact (proj2 Hedgeright) |].
        apply transformed_coprime_edge_removed_cases__certificate_bootstrap;
          try (apply Hnonneg; lia); try exact (proj2 Hedgeright).
        assert (Hchosen : chosen center).
        { unfold chosen. left. exact Hsel. }
        destruct (prop_dec (chosen (center + 1))) as [Hnext | Hnext].
        -- left. split; assumption.
        -- right. left. split; [exact Hchosen |]. split; assumption.
    + destruct Hblockedge as [q [Hq Hedgeblock]].
      pose proof (Hblocks q Hq) as Hb.
      set (lo := snd (Znth q ordered (0, 0))) in *.
      set (len := fst (Znth q ordered (0, 0))) in *.
      assert (Ht : 0 <= edge - (lo - 1) < len + 1) by lia.
      pose proof (block_charge_maps_to_coprime_edge__certificate_bootstrap
        a lo len (edge - (lo - 1)) Hb Ht) as Hcoprime.
      replace (lo - 1 + (edge - (lo - 1))) with edge in Hcoprime by lia.
      unfold AdjacentCoprime in Hcoprime.
      split; [exact (proj1 Hcoprime) |]. split; [exact (proj2 Hcoprime) |].
      apply transformed_coprime_edge_removed_cases__certificate_bootstrap;
        try (apply Hnonneg; lia); try exact (proj2 Hcoprime).
      unfold InteriorOneBlock in Hb.
      destruct Hb as [Hlobounds [Hhibound [Hleft [Hright Hones]]]].
      destruct (Z.eq_dec edge (lo - 1)) as [Heleft | Hneleft].
      * assert (Hchosenright : chosen (edge + 1)).
        {
          unfold chosen. right. exists q. split; [exact Hq |]. lia.
        }
        destruct (prop_dec (chosen edge)) as [Hchosenleft | Hchosenleft].
        -- left. split; assumption.
        -- right. right. split; [exact Hchosenleft |]. split.
           ++ exact Hchosenright.
           ++ subst edge. exact Hleft.
      * destruct (Z.eq_dec edge (lo + len - 1)) as [Heright | Hneright].
        -- assert (Hchosenleft : chosen edge).
           {
             unfold chosen. right. exists q. split; [exact Hq |]. lia.
           }
           destruct (prop_dec (chosen (edge + 1))) as
             [Hchosenright | Hchosenright].
           ++ left. split; assumption.
           ++ right. left. split; [exact Hchosenleft |]. split.
              ** exact Hchosenright.
              ** subst edge. replace (lo + len - 1 + 1) with
                   (lo + len) by lia. exact Hright.
        -- left. split.
           ++ unfold chosen. right. exists q. split; [exact Hq |]. lia.
           ++ unfold chosen. right. exists q. split; [exact Hq |]. lia.
Qed.
Lemma structured_pair_block_removed_cardinality__certificate_bootstrap :
  forall a centres selected (ordered : list (Z * Z)),
    PairCenterSelection a (Zlength a) centres ->
    NoDup selected ->
    (forall center, In center selected -> centres center) ->
    (forall q r, 0 <= q < Zlength ordered ->
      0 <= r < Zlength ordered ->
      snd (Znth q ordered (0, 0)) = snd (Znth r ordered (0, 0)) ->
      q = r) ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)))) ->
    #(fun edge : Z => 0 <= edge < Zlength a - 1 /\
      ((exists center, In center selected /\
          (edge = center - 1 \/ edge = center)) \/
       (exists q, 0 <= q < Zlength ordered /\
          snd (Znth q ordered (0, 0)) - 1 <= edge <
          snd (Znth q ordered (0, 0)) +
            fst (Znth q ordered (0, 0))))) =
      2 * Zlength selected +
        ListLib.sum (map (fun len => len + 1) (map fst ordered)).
Proof.
  intros a centres selected ordered Hcentres Hnodup Hinside
    Hstartinj Hblocks.
  set (PairEdge := fun edge : Z =>
    exists center, In center selected /\
      (edge = center - 1 \/ edge = center)).
  set (BlockEdge := fun edge : Z =>
    exists q, 0 <= q < Zlength ordered /\
      snd (Znth q ordered (0, 0)) - 1 <= edge <
      snd (Znth q ordered (0, 0)) +
        fst (Znth q ordered (0, 0))).
  change (#(fun edge : Z => 0 <= edge < Zlength a - 1 /\
    (PairEdge edge \/ BlockEdge edge)) =
    2 * Zlength selected +
      ListLib.sum (map (fun len => len + 1) (map fst ordered))).
  assert (Hdisjoint : forall edge, PairEdge edge -> ~ BlockEdge edge).
  {
    intros edge [center [Hsel Hepair]]
      [q [Hq Hedgeblock]].
    pose proof (canonical_profile_pair_block_disjoint__certificate_bootstrap
      a (map fst ordered) (map snd ordered) centres) as Hdisj_helper.
    assert (Hlenmaps : Zlength (map snd ordered) =
      Zlength (map fst ordered)).
    { rewrite !Zlength_correct, !length_map. reflexivity. }
    assert (Hmapblocks : forall r, 0 <= r < Zlength (map fst ordered) ->
      InteriorOneBlock a (Znth r (map snd ordered) 0)
        (Znth r (map snd ordered) 0 + Znth r (map fst ordered) 0)).
    {
      intros r Hr. rewrite Zlength_map__certificate_bootstrap in Hr.
      rewrite !Znth_map__certificate_bootstrap with
        (da := (0, 0)) by exact Hr.
      apply Hblocks. exact Hr.
    }
    specialize (Hdisj_helper Hlenmaps Hmapblocks Hcentres center q
      (Hinside center Hsel)).
    rewrite Zlength_map__certificate_bootstrap in Hdisj_helper.
    specialize (Hdisj_helper Hq).
    rewrite !Znth_map__certificate_bootstrap with
      (da := (0, 0)) in Hdisj_helper by exact Hq.
    destruct Hdisj_helper; destruct Hepair; lia.
  }
  pose proof (set_card_partition_subset_Z__certificate_bootstrap
    0 (Zlength a - 1)
    (fun edge => PairEdge edge \/ BlockEdge edge)
    PairEdge) as Hpartition.
  specialize (Hpartition ltac:(intros; tauto)).
  rewrite Hpartition.
  assert (Hpaircard :
    #(fun edge : Z => 0 <= edge < Zlength a - 1 /\ PairEdge edge) =
      2 * Zlength selected).
  {
    unfold PairEdge.
    apply exact_pair_edge_image_cardinality__certificate_bootstrap
      with (centres := centres); assumption.
  }
  rewrite Hpaircard.
  assert (Hrest :
    #(fun edge : Z => 0 <= edge < Zlength a - 1 /\
      (PairEdge edge \/ BlockEdge edge) /\ ~ PairEdge edge) =
    #(fun edge : Z => 0 <= edge < Zlength a - 1 /\ BlockEdge edge)).
  {
    apply set_card_iff__exam_bridge. intros edge. split.
    - intros [Hedge [[Hpair | Hblock] Hnot]]; [contradiction | tauto].
    - intros [Hedge Hblock]. split; [exact Hedge |]. split.
      * right. exact Hblock.
      * intro Hpair. exact (Hdisjoint edge Hpair Hblock).
  }
  rewrite Hrest. unfold BlockEdge.
  rewrite (indexed_block_edge_union_cardinality__certificate_bootstrap
    a ordered (Zlength a) Hstartinj Hblocks).
  - reflexivity.
  - intros q Hq. pose proof (Hblocks q Hq) as Hb.
    unfold InteriorOneBlock in Hb. lia.
Qed.
Lemma structured_pair_block_phase_attainable__certificate_bootstrap :
  forall a base_sad centres selected (ordered : list (Z * Z)) k,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairCenterSelection a (Zlength a) centres ->
    NoDup selected ->
    NoDup ordered ->
    (forall center, In center selected -> centres center) ->
    (forall q r, 0 <= q < Zlength ordered ->
      0 <= r < Zlength ordered ->
      snd (Znth q ordered (0, 0)) = snd (Znth r ordered (0, 0)) ->
      q = r) ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)))) ->
    Zlength selected + ListLib.sum (map fst ordered) <= k ->
    exists result,
      SimplifiedExams a k result /\
      ExamSadness result
        (base_sad -
          (2 * Zlength selected +
            ListLib.sum
              (map (fun len => len + 1) (map fst ordered)))).
Proof.
  intros a base_sad centres selected ordered k Hnonneg Hbase Hcentres
    Hselected_nodup Hordered_nodup Hinside Hstartinj Hblocks Hcost.
  set (chosen := fun i : Z =>
    In i selected \/
    exists q, 0 <= q < Zlength ordered /\
      snd (Znth q ordered (0, 0)) <= i <
      snd (Znth q ordered (0, 0)) +
        fst (Znth q ordered (0, 0))).
  assert (Hrange : forall i, chosen i -> 0 <= i < Zlength a).
  {
    intros i [Hsel | [q [Hq Hvertex]]].
    - pose proof (proj1 Hcentres i (Hinside i Hsel)) as Hv.
      unfold NonOnePairCenter in Hv. lia.
    - pose proof (Hblocks q Hq) as Hb.
      unfold InteriorOneBlock in Hb. lia.
  }
  assert (Hchosen_card :
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) =
      Zlength selected + ListLib.sum (map fst ordered)).
  {
    unfold chosen.
    apply structured_pair_block_choice_cardinality__certificate_bootstrap
      with (centres := centres); assumption.
  }
  set (transformed_sad := #(fun edge : Z =>
    0 <= edge < Zlength a - 1 /\
    Z.gcd
      (if prop_dec (chosen edge) then 0 else Znth edge a 0)
      (if prop_dec (chosen (edge + 1)) then 0
       else Znth (edge + 1) a 0) = 1)).
  pose proof (choice_sadness_is_base_minus_removed__certificate_bootstrap
    a chosen base_sad transformed_sad Hnonneg Hbase ltac:(reflexivity))
    as Hpartition.
  assert (Hremoved :
    #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) <> 1) =
      2 * Zlength selected +
        ListLib.sum (map (fun len => len + 1) (map fst ordered))).
  {
    transitivity (#(fun edge : Z => 0 <= edge < Zlength a - 1 /\
      ((exists center, In center selected /\
          (edge = center - 1 \/ edge = center)) \/
       (exists q, 0 <= q < Zlength ordered /\
          snd (Znth q ordered (0, 0)) - 1 <= edge <
          snd (Znth q ordered (0, 0)) +
            fst (Znth q ordered (0, 0)))))).
    - apply set_card_iff__exam_bridge. intros edge.
      pose proof
        (structured_pair_block_choice_removed_edges__certificate_bootstrap
          a centres selected ordered Hnonneg Hcentres Hinside Hblocks edge)
        as Hiff.
      split.
      * intros Hremoved_edge. split.
        -- exact (proj1 Hremoved_edge).
        -- exact (proj1 Hiff Hremoved_edge).
      * intros [_ Hunion]. exact (proj2 Hiff Hunion).
    - apply structured_pair_block_removed_cardinality__certificate_bootstrap
        with (centres := centres); assumption.
  }
  rewrite Hremoved in Hpartition.
  assert (Hsad : transformed_sad =
    base_sad -
      (2 * Zlength selected +
        ListLib.sum (map (fun len => len + 1) (map fst ordered)))) by lia.
  eapply materialize_exam_choice_sadness__certificate_bootstrap
    with (chosen := chosen).
  - exact Hrange.
  - rewrite Hchosen_card. exact Hcost.
  - exact (eq_sym Hsad).
Qed.
Lemma sum_sublist_succ__certificate_bootstrap :
  forall (xs : list Z) i,
    0 <= i < Zlength xs ->
    ListLib.sum (sublist 0 (i + 1) xs) =
      ListLib.sum (sublist 0 i xs) + Znth i xs 0.
Proof.
  intros xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single 0 i xs) by lia.
  rewrite ListLib.sum_app. simpl. lia.
Qed.
Lemma greedy_block_state_remaining_nonnegative__certificate_bootstrap :
  forall sorted next budget initial_sad remaining sadness,
    0 <= budget ->
    GreedyBlockState sorted next budget initial_sad remaining sadness ->
    0 <= remaining.
Proof.
  intros sorted next budget initial_sad remaining sadness Hbudget
    [Hnext [Hremaining [Hsadness Hfit]]].
  destruct (Z.eq_dec next 0) as [-> | Hnextnz].
  - unfold sublist in Hremaining. simpl in Hremaining. lia.
  - specialize (Hfit (next - 1) ltac:(lia)).
    pose proof (sum_sublist_succ__certificate_bootstrap
      sorted (next - 1) ltac:(lia)) as Hsum.
    replace (next - 1 + 1) with next in Hsum by lia.
    lia.
Qed.
Lemma canonical_greedy_prefix_attainable__certificate_bootstrap :
  forall a base_sad pair_savings lengths original_k sorted use next
      remaining sadness,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    CanonicalInteriorOneRunPrefix a (Zlength a) lengths ->
    1 <= original_k <= Zlength a ->
    Permutation lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    exists result,
      SimplifiedExams a original_k result /\ ExamSadness result sadness.
Proof.
  intros a base_sad pair_savings lengths original_k sorted use next
    remaining sadness Hnonneg Hbase Hpair Hcanonical Hk Hperm Hsorted
    Huse Hgreedy.
  destruct (pair_savings_prefix_witness__certificate_bootstrap
    a pair_savings Hpair) as [allcentres
      [Hallselection [Hallcount Hpairnonneg]]].
  unfold MinValue in Huse.
  assert (Husebounds : 0 <= use <= pair_savings /\ use <= original_k).
  {
    subst use. rewrite Z.min_glb_iff. lia.
  }
  destruct (pair_savings_has_exact_subselection__certificate_bootstrap
    a pair_savings use Hpair (proj1 Husebounds)) as
    [centres [selected
      [Hselection [Hselected_nodup [Hinside [Hselected_len Hselcard]]]]]].
  destruct (canonical_profile_sorted_block_pairs_strong__certificate_bootstrap
    a lengths sorted Hcanonical Hperm) as
    [ordered [Hordered_map [Hordered_nodup
      [Hordered_blocks [Hordered_ends Hordered_startinj]]]]].
  assert (Hordered_len : Zlength ordered = Zlength sorted).
  { rewrite <- Hordered_map, Zlength_map__certificate_bootstrap. reflexivity. }
  destruct (sorted_ordered_prefix_properties__certificate_bootstrap
    a sorted ordered next Hordered_map Hordered_nodup Hordered_blocks
    Hordered_startinj ltac:(pose proof (proj1 Hgreedy); lia)) as
    [prefix [Hprefix [Hprefix_len [Hprefix_map
      [Hprefix_nodup [Hprefix_blocks Hprefix_startinj]]]]]].
  assert (Hbudget : 0 <= original_k - use) by lia.
  pose proof (greedy_block_state_remaining_nonnegative__certificate_bootstrap
    sorted next (original_k - use) (base_sad - 2 * use)
    remaining sadness Hbudget Hgreedy) as Hremaining_nonneg.
  destruct Hgreedy as [Hnext [Hremaining [Hsadness Hfit]]].
  assert (Hcost : Zlength selected + ListLib.sum (map fst prefix) <=
    original_k).
  {
    rewrite Hselected_len, Hprefix_map.
    lia.
  }
  destruct (structured_pair_block_phase_attainable__certificate_bootstrap
    a base_sad centres selected prefix original_k Hnonneg Hbase Hselection
    Hselected_nodup Hprefix_nodup Hinside Hprefix_startinj Hprefix_blocks
    Hcost) as [result [Hresult Hresult_sad]].
  exists result. split; [exact Hresult |].
  replace sadness with
    (base_sad -
      (2 * Zlength selected +
        ListLib.sum (map (fun len => len + 1) (map fst prefix)))).
  - exact Hresult_sad.
  - rewrite Hselected_len, Hprefix_map. lia.
Qed.
Lemma set_card_positive_witness__certificate_bootstrap :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    0 < @set_card A P FP -> exists x, P x.
Proof.
  intros A P FP Hpositive.
  destruct (@enum A P FP) as [|x xs] eqn:Henum.
  - unfold set_card, SumLib.Sum.sum in Hpositive.
    rewrite Henum in Hpositive. simpl in Hpositive. lia.
  - exists x. apply (proj2 (@enum_ok A P FP x)).
    rewrite Henum. simpl. left. reflexivity.
Qed.
Lemma sad_edge_all_one_propagates__certificate_bootstrap :
  forall n (v : Z -> Z) edge,
    0 <= edge < n - 1 ->
    v edge = 1 -> v (edge + 1) = 1 ->
    (forall e, 0 <= e < n - 1 -> Z.gcd (v e) (v (e + 1)) = 1 ->
      v e = 1 /\ v (e + 1) = 1) ->
    forall j, 0 <= j < n -> v j = 1.
Proof.
  intros n v edge Hedge Hvedge Hvedgenext Hall j Hj.
  destruct (Z_le_gt_dec j edge) as [Hleftside | Hrightside].
  - assert (Hleft : forall d : nat,
      (d <= Z.to_nat edge)%nat ->
      v (edge - Z.of_nat d) = 1).
    {
      induction d as [|d IH]; intros Hd.
      - simpl. replace (edge - 0) with edge by lia. exact Hvedge.
      - assert (Hdprev : (d <= Z.to_nat edge)%nat) by lia.
        specialize (IH Hdprev).
        assert (Hidx : 0 <= edge - Z.of_nat (S d) < n - 1).
        {
          rewrite Nat2Z.inj_succ.
          assert (Z.of_nat (Z.to_nat edge) = edge)
            by (rewrite Z2Nat.id; lia).
          lia.
        }
        pose proof (Hall (edge - Z.of_nat (S d)) Hidx) as Hstep.
        assert (Hgcd : Z.gcd
          (v (edge - Z.of_nat (S d)))
          (v (edge - Z.of_nat (S d) + 1)) = 1).
        {
          replace (v (edge - Z.of_nat (S d) + 1)) with 1.
          - apply Z.gcd_1_r.
          - rewrite Nat2Z.inj_succ.
            symmetry.
            replace (edge - Z.succ (Z.of_nat d) + 1) with
              (edge - Z.of_nat d) by lia.
            exact IH.
        }
        exact (proj1 (Hstep Hgcd)).
    }
    specialize (Hleft (Z.to_nat (edge - j))).
    assert (Hdle : (Z.to_nat (edge - j) <= Z.to_nat edge)%nat).
    { apply Z2Nat.inj_le; lia. }
    specialize (Hleft Hdle).
    rewrite Z2Nat.id in Hleft by lia. replace (edge - (edge - j)) with j
      in Hleft by lia. exact Hleft.
  - assert (Hright : forall d : nat,
      (d <= Z.to_nat (n - 1 - (edge + 1)))%nat ->
      v (edge + 1 + Z.of_nat d) = 1).
    {
      induction d as [|d IH]; intros Hd.
      - simpl. replace (edge + 1 + 0) with (edge + 1) by lia.
        exact Hvedgenext.
      - assert (Hdprev :
          (d <= Z.to_nat (n - 1 - (edge + 1)))%nat) by lia.
        specialize (IH Hdprev).
        assert (Hidx : 0 <= edge + 1 + Z.of_nat d < n - 1).
        {
          assert (Z.of_nat (Z.to_nat (n - 1 - (edge + 1))) =
            n - 1 - (edge + 1)) by (rewrite Z2Nat.id; lia).
          lia.
        }
        pose proof (Hall (edge + 1 + Z.of_nat d) Hidx) as Hstep.
        assert (Hgcd : Z.gcd
          (v (edge + 1 + Z.of_nat d))
          (v (edge + 1 + Z.of_nat d + 1)) = 1).
        { rewrite IH. apply Z.gcd_1_l. }
        rewrite Nat2Z.inj_succ.
        replace (edge + 1 + Z.succ (Z.of_nat d)) with
          (edge + 1 + Z.of_nat d + 1) by lia.
        exact (proj2 (Hstep Hgcd)).
    }
    specialize (Hright (Z.to_nat (j - (edge + 1)))).
    assert (Hdle :
      (Z.to_nat (j - (edge + 1)) <=
       Z.to_nat (n - 1 - (edge + 1)))%nat).
    { apply Z2Nat.inj_le; lia. }
    specialize (Hright Hdle).
    rewrite Z2Nat.id in Hright by lia.
    replace (edge + 1 + (j - (edge + 1))) with j in Hright by lia.
    exact Hright.
Qed.
Lemma sad_edge_with_nonone_endpoint_exists__certificate_bootstrap :
  forall n (v : Z -> Z),
    (exists j, 0 <= j < n /\ v j <> 1) ->
    0 < #(fun edge : Z =>
      0 <= edge < n - 1 /\ Z.gcd (v edge) (v (edge + 1)) = 1) ->
    exists edge, 0 <= edge < n - 1 /\
      Z.gcd (v edge) (v (edge + 1)) = 1 /\
      (v edge <> 1 \/ v (edge + 1) <> 1).
Proof.
  intros n v [j [Hj Hvj]] Hpositive.
  destruct (set_card_positive_witness__certificate_bootstrap
    (fun edge : Z =>
      0 <= edge < n - 1 /\ Z.gcd (v edge) (v (edge + 1)) = 1)
    _ Hpositive) as [edge [Hedge Hgcd]].
  destruct (classic (exists e, 0 <= e < n - 1 /\
    Z.gcd (v e) (v (e + 1)) = 1 /\
    (v e <> 1 \/ v (e + 1) <> 1))) as [Hex | Hnone].
  - exact Hex.
  - exfalso. apply Hvj.
    eapply sad_edge_all_one_propagates__certificate_bootstrap;
      try eassumption.
    + apply NNPP. intro Hne. apply Hnone.
      exists edge. tauto.
    + apply NNPP. intro Hne. apply Hnone.
      exists edge. tauto.
    + intros e He Hge. split.
      * apply NNPP. intro Hne. apply Hnone. exists e. tauto.
      * apply NNPP. intro Hne. apply Hnone. exists e. tauto.
Qed.
Lemma set_card_at_most_singleton__certificate_bootstrap :
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
  pose proof (@enum_nodup A P FP) as Hnd.
  rewrite Henum in Hnd. inversion Hnd; subst.
  apply H1. left. rewrite (Honly _ Ha), (Honly _ Hb). reflexivity.
Qed.
Lemma set_card_member_positive__certificate_bootstrap :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x,
    P x -> 1 <= @set_card A P FP.
Proof.
  intros A P FP x Hx.
  unfold set_card, SumLib.Sum.sum.
  assert (In x (@enum A P FP)) as Hin by
    (apply (proj1 (@enum_ok A P FP x)); exact Hx).
  rewrite fold_ones_length__pair_scan_exits.
  replace 1 with (Z.of_nat 1) by reflexivity.
  apply Nat2Z.inj_le. simpl.
  apply in_split in Hin as [l1 [l2 Heq]].
  rewrite Heq, length_app. simpl. lia.
Qed.
Lemma additional_zero_sadness_monotone__certificate_bootstrap :
  forall a (chosen : Z -> Prop) idx edge,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    0 <= edge < Zlength a - 1 ->
    Z.gcd
      (if prop_dec (chosen edge \/ edge = idx) then 0 else Znth edge a 0)
      (if prop_dec (chosen (edge + 1) \/ edge + 1 = idx) then 0
       else Znth (edge + 1) a 0) = 1 ->
    Z.gcd
      (if prop_dec (chosen edge) then 0 else Znth edge a 0)
      (if prop_dec (chosen (edge + 1)) then 0
       else Znth (edge + 1) a 0) = 1.
Proof.
  intros a chosen idx edge Hnonneg Hedge Hnew.
  pose proof (transformed_coprime_implies_original__certificate_bootstrap
    (Znth edge a 0) (Znth (edge + 1) a 0)
    (chosen edge \/ edge = idx) (chosen (edge + 1) \/ edge + 1 = idx)
    ltac:(apply Hnonneg; lia) ltac:(apply Hnonneg; lia) Hnew) as Horiginal.
  apply transformed_coprime_edge_cases__certificate_bootstrap;
    try (apply Hnonneg; lia); try exact Horiginal.
  apply transformed_coprime_edge_cases__certificate_bootstrap in Hnew;
    try (apply Hnonneg; lia); try exact Horiginal.
  destruct Hnew as [[Hnl Hnr] |
    [[Hl [Hnr Hyone]] | [Hnl [Hr Hxone]]]].
  - left. tauto.
  - destruct (classic (chosen edge)) as [Hold | Hold].
    + right. left. tauto.
    + left. tauto.
  - destruct (classic (chosen (edge + 1))) as [Hold | Hold].
    + right. right. tauto.
    + left. tauto.
Qed.
Lemma one_additional_zero_reduces_sadness__certificate_bootstrap :
  forall a (chosen : Z -> Prop) current_sad,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    (exists j, 0 <= j < Zlength a /\ Znth j a 0 <> 1) ->
    current_sad = #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) = 1) ->
    0 < current_sad ->
    exists idx,
      0 <= idx < Zlength a /\ ~ chosen idx /\
      #(fun i : Z => 0 <= i < Zlength a /\
        (chosen i \/ i = idx)) <=
        #(fun i : Z => 0 <= i < Zlength a /\ chosen i) + 1 /\
      #(fun edge : Z =>
        0 <= edge < Zlength a - 1 /\
        Z.gcd
          (if prop_dec (chosen edge \/ edge = idx)
           then 0 else Znth edge a 0)
          (if prop_dec (chosen (edge + 1) \/ edge + 1 = idx)
           then 0 else Znth (edge + 1) a 0) = 1) <=
        current_sad - 1.
Proof.
  intros a chosen current_sad Hnonneg [j [Hj Haj]] Hsad Hpositive.
  set (v := fun i : Z =>
    if prop_dec (chosen i) then 0 else Znth i a 0).
  assert (Hvnonneg : forall i, 0 <= i < Zlength a -> 0 <= v i).
  {
    intros i Hi. unfold v. destruct (prop_dec (chosen i));
      [lia | apply Hnonneg; exact Hi].
  }
  assert (Hvnonone : exists i, 0 <= i < Zlength a /\ v i <> 1).
  {
    exists j. split; [exact Hj |]. unfold v.
    destruct (prop_dec (chosen j)); [discriminate | exact Haj].
  }
  assert (Hsad_v : current_sad = #(fun edge : Z =>
    0 <= edge < Zlength a - 1 /\
    Z.gcd (v edge) (v (edge + 1)) = 1)).
  { unfold v. exact Hsad. }
  destruct (sad_edge_with_nonone_endpoint_exists__certificate_bootstrap
    (Zlength a) v Hvnonone ltac:(rewrite <- Hsad_v; exact Hpositive)) as
    [edge [Hedge [Hedge_sad [Hleftnonone | Hrightnonone]]]].
  - exists (edge + 1).
    assert (Hnotchosen : ~ chosen (edge + 1)).
    {
      intro Hchosen.
      assert (Hvzero : v (edge + 1) = 0).
      { unfold v. destruct (prop_dec (chosen (edge + 1)));
          [reflexivity | contradiction]. }
      rewrite Hvzero, Z.gcd_0_r_nonneg in Hedge_sad by
        (apply Hvnonneg; lia).
      contradiction.
    }
    split; [lia |]. split; [exact Hnotchosen |].
    assert (Hchoice_card :
      #(fun i : Z => 0 <= i < Zlength a /\
        (chosen i \/ i = edge + 1)) <=
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i) + 1).
    {
      pose proof (set_card_partition_subset_Z__certificate_bootstrap
        0 (Zlength a) (fun i => chosen i \/ i = edge + 1) chosen
        ltac:(intros; tauto)) as Hpart.
      rewrite Hpart.
      pose proof (set_card_at_most_singleton__certificate_bootstrap
        (fun i : Z => 0 <= i < Zlength a /\
          (chosen i \/ i = edge + 1) /\ ~ chosen i) _ (edge + 1)
        ltac:(intros i [_ [[Hchosen_i | Heq] Hnot_i]];
          [contradiction | exact Heq])) as Hone.
      lia.
    }
    split; [exact Hchoice_card |].
    assert (Horiginal :
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1).
    {
      unfold v in Hedge_sad.
      eapply transformed_coprime_implies_original__certificate_bootstrap;
        try (apply Hnonneg; lia); exact Hedge_sad.
    }
    assert (Htarget_removed :
      Z.gcd
        (if prop_dec (chosen edge \/ edge = edge + 1)
         then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1) \/ edge + 1 = edge + 1)
         then 0 else Znth (edge + 1) a 0) <> 1).
    {
      apply transformed_coprime_edge_removed_cases__certificate_bootstrap;
        try (apply Hnonneg; lia); try exact Horiginal.
      destruct (classic (chosen edge)) as [Hchosenleft | Hchosenleft].
      * left. split; [left; exact Hchosenleft | right; lia].
      * right. right. split.
        -- intros [Hbad | Hbad]; [contradiction | lia].
        -- split; [right; lia |]. unfold v in Hleftnonone.
           destruct (prop_dec (chosen edge)); [contradiction | exact Hleftnonone].
    }
    set (OldSad := fun e : Z =>
      Z.gcd
        (if prop_dec (chosen e) then 0 else Znth e a 0)
        (if prop_dec (chosen (e + 1)) then 0
         else Znth (e + 1) a 0) = 1).
    set (NewSad := fun e : Z =>
      Z.gcd
        (if prop_dec (chosen e \/ e = edge + 1)
         then 0 else Znth e a 0)
        (if prop_dec (chosen (e + 1) \/ e + 1 = edge + 1)
         then 0 else Znth (e + 1) a 0) = 1).
    assert (Hsubset : forall e, 0 <= e < Zlength a - 1 ->
      NewSad e -> OldSad e).
    {
      intros e He Hnew.
      eapply additional_zero_sadness_monotone__certificate_bootstrap;
        eauto.
    }
    pose proof (set_card_partition_subset_Z__certificate_bootstrap
      0 (Zlength a - 1) OldSad NewSad Hsubset) as Hpart.
    assert (Hlost : 1 <= #(fun e : Z =>
      0 <= e < Zlength a - 1 /\ OldSad e /\ ~ NewSad e)).
    {
      eapply set_card_member_positive__certificate_bootstrap with (x := edge).
      split; [exact Hedge |]. split.
      * unfold OldSad, v in *. exact Hedge_sad.
      * unfold NewSad. intro Hnew. exact (Htarget_removed Hnew).
    }
    change (#(fun e : Z => 0 <= e < Zlength a - 1 /\ NewSad e) <=
      current_sad - 1).
    change (current_sad =
      #(fun e : Z => 0 <= e < Zlength a - 1 /\ OldSad e)) in Hsad.
    lia.
  - exists edge.
    assert (Hnotchosen : ~ chosen edge).
    {
      intro Hchosen.
      assert (Hvzero : v edge = 0).
      { unfold v. destruct (prop_dec (chosen edge));
          [reflexivity | contradiction]. }
      rewrite Hvzero, Z.gcd_0_l_nonneg in Hedge_sad by
        (apply Hvnonneg; lia).
      contradiction.
    }
    split; [lia |]. split; [exact Hnotchosen |].
    assert (Hchoice_card :
      #(fun i : Z => 0 <= i < Zlength a /\ (chosen i \/ i = edge)) <=
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i) + 1).
    {
      pose proof (set_card_partition_subset_Z__certificate_bootstrap
        0 (Zlength a) (fun i => chosen i \/ i = edge) chosen
        ltac:(intros; tauto)) as Hpart.
      rewrite Hpart.
      pose proof (set_card_at_most_singleton__certificate_bootstrap
        (fun i : Z => 0 <= i < Zlength a /\
          (chosen i \/ i = edge) /\ ~ chosen i) _ edge
        ltac:(intros i [_ [[Hchosen_i | Heq] Hnot_i]];
          [contradiction | exact Heq])) as Hone.
      lia.
    }
    split; [exact Hchoice_card |].
    assert (Horiginal :
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1).
    {
      unfold v in Hedge_sad.
      eapply transformed_coprime_implies_original__certificate_bootstrap;
        try (apply Hnonneg; lia); exact Hedge_sad.
    }
    assert (Htarget_removed :
      Z.gcd
        (if prop_dec (chosen edge \/ edge = edge)
         then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1) \/ edge + 1 = edge)
         then 0 else Znth (edge + 1) a 0) <> 1).
    {
      apply transformed_coprime_edge_removed_cases__certificate_bootstrap;
        try (apply Hnonneg; lia); try exact Horiginal.
      destruct (classic (chosen (edge + 1))) as [Hchosenright | Hchosenright].
      * left. split; [right; reflexivity | left; exact Hchosenright].
      * right. left. split; [right; reflexivity |]. split.
        -- intros [Hbad | Hbad]; [contradiction | lia].
        -- unfold v in Hrightnonone.
           destruct (prop_dec (chosen (edge + 1)));
             [contradiction | exact Hrightnonone].
    }
    set (OldSad := fun e : Z =>
      Z.gcd
        (if prop_dec (chosen e) then 0 else Znth e a 0)
        (if prop_dec (chosen (e + 1)) then 0
         else Znth (e + 1) a 0) = 1).
    set (NewSad := fun e : Z =>
      Z.gcd
        (if prop_dec (chosen e \/ e = edge)
         then 0 else Znth e a 0)
        (if prop_dec (chosen (e + 1) \/ e + 1 = edge)
         then 0 else Znth (e + 1) a 0) = 1).
    assert (Hsubset : forall e, 0 <= e < Zlength a - 1 ->
      NewSad e -> OldSad e).
    {
      intros e He Hnew.
      eapply additional_zero_sadness_monotone__certificate_bootstrap;
        eauto.
    }
    pose proof (set_card_partition_subset_Z__certificate_bootstrap
      0 (Zlength a - 1) OldSad NewSad Hsubset) as Hpart.
    assert (Hlost : 1 <= #(fun e : Z =>
      0 <= e < Zlength a - 1 /\ OldSad e /\ ~ NewSad e)).
    {
      eapply set_card_member_positive__certificate_bootstrap with (x := edge).
      split; [exact Hedge |]. split.
      * unfold OldSad, v in *. exact Hedge_sad.
      * unfold NewSad. intro Hnew. exact (Htarget_removed Hnew).
    }
    change (#(fun e : Z => 0 <= e < Zlength a - 1 /\ NewSad e) <=
      current_sad - 1).
    change (current_sad =
      #(fun e : Z => 0 <= e < Zlength a - 1 /\ OldSad e)) in Hsad.
    lia.
Qed.
Lemma residual_zero_reduction_with_fuel__certificate_bootstrap :
  forall (fuel : nat) a (chosen : Z -> Prop) current_sad target,
    (forall i, chosen i -> 0 <= i < Zlength a) ->
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    (exists j, 0 <= j < Zlength a /\ Znth j a 0 <> 1) ->
    current_sad = #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) = 1) ->
    0 <= target ->
    current_sad - target <= Z.of_nat fuel ->
    exists (extended : Z -> Prop) final_sad,
      (forall i, extended i -> 0 <= i < Zlength a) /\
      #(fun i : Z => 0 <= i < Zlength a /\ extended i) <=
        #(fun i : Z => 0 <= i < Zlength a /\ chosen i) +
          Z.of_nat fuel /\
      final_sad = #(fun edge : Z =>
        0 <= edge < Zlength a - 1 /\
        Z.gcd
          (if prop_dec (extended edge) then 0 else Znth edge a 0)
          (if prop_dec (extended (edge + 1)) then 0
           else Znth (edge + 1) a 0) = 1) /\
      final_sad <= target.
Proof.
  induction fuel as [|fuel IH];
    intros a chosen current_sad target Hchosen Hnonneg Hnonone
      Hsad Htarget Hfuel.
  - exists chosen, current_sad. split; [exact Hchosen |]. split.
    + simpl. lia.
    + split; [exact Hsad |]. simpl in Hfuel. lia.
  - destruct (Z_le_gt_dec current_sad target) as [Hdone | Hmore].
    + exists chosen, current_sad. split; [exact Hchosen |]. split.
      * pose proof (Nat2Z.is_nonneg fuel). simpl. lia.
      * split; [exact Hsad | exact Hdone].
    + destruct (one_additional_zero_reduces_sadness__certificate_bootstrap
        a chosen current_sad Hnonneg Hnonone Hsad ltac:(lia)) as
        [idx [Hidx [Hfresh [Hcard Hdrop]]]].
      set (chosen' := fun i : Z => chosen i \/ i = idx).
      set (sad' := #(fun edge : Z =>
        0 <= edge < Zlength a - 1 /\
        Z.gcd
          (if prop_dec (chosen' edge) then 0 else Znth edge a 0)
          (if prop_dec (chosen' (edge + 1)) then 0
           else Znth (edge + 1) a 0) = 1)).
      assert (Hchosen' : forall i, chosen' i -> 0 <= i < Zlength a).
      {
        intros i Hi. unfold chosen' in Hi. destruct Hi as [Hi | ->];
          [apply Hchosen; exact Hi | exact Hidx].
      }
      assert (Hsad' : sad' = #(fun edge : Z =>
        0 <= edge < Zlength a - 1 /\
        Z.gcd
          (if prop_dec (chosen' edge) then 0 else Znth edge a 0)
          (if prop_dec (chosen' (edge + 1)) then 0
           else Znth (edge + 1) a 0) = 1)) by reflexivity.
      assert (Hdrop' : sad' <= current_sad - 1).
      {
        unfold sad', chosen'. exact Hdrop.
      }
      assert (Hfuel' : sad' - target <= Z.of_nat fuel).
      { simpl in Hfuel. lia. }
      destruct (IH a chosen' sad' target Hchosen' Hnonneg Hnonone
        Hsad' Htarget Hfuel') as
        [extended [final_sad [Hextended [Hextended_card
          [Hfinal_sad Hfinal_target]]]]].
      exists extended, final_sad. split; [exact Hextended |]. split.
      * unfold chosen' in Hextended_card, Hcard.
        simpl in *. lia.
      * split; assumption.
Qed.
Lemma structured_pair_block_choice_profile__certificate_bootstrap :
  forall a base_sad centres selected (ordered : list (Z * Z)),
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairCenterSelection a (Zlength a) centres ->
    NoDup selected ->
    NoDup ordered ->
    (forall center, In center selected -> centres center) ->
    (forall q r, 0 <= q < Zlength ordered ->
      0 <= r < Zlength ordered ->
      snd (Znth q ordered (0, 0)) = snd (Znth r ordered (0, 0)) ->
      q = r) ->
    (forall q, 0 <= q < Zlength ordered ->
      InteriorOneBlock a (snd (Znth q ordered (0, 0)))
        (snd (Znth q ordered (0, 0)) +
          fst (Znth q ordered (0, 0)))) ->
    exists chosen : Z -> Prop,
      (forall i, chosen i -> 0 <= i < Zlength a) /\
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i) =
        Zlength selected + ListLib.sum (map fst ordered) /\
      #(fun edge : Z =>
        0 <= edge < Zlength a - 1 /\
        Z.gcd
          (if prop_dec (chosen edge) then 0 else Znth edge a 0)
          (if prop_dec (chosen (edge + 1)) then 0
           else Znth (edge + 1) a 0) = 1) =
        base_sad -
          (2 * Zlength selected +
            ListLib.sum
              (map (fun len => len + 1) (map fst ordered))).
Proof.
  intros a base_sad centres selected ordered Hnonneg Hbase Hcentres
    Hselected_nodup Hordered_nodup Hinside Hstartinj Hblocks.
  set (chosen := fun i : Z =>
    In i selected \/
    exists q, 0 <= q < Zlength ordered /\
      snd (Znth q ordered (0, 0)) <= i <
      snd (Znth q ordered (0, 0)) +
        fst (Znth q ordered (0, 0))).
  assert (Hrange : forall i, chosen i -> 0 <= i < Zlength a).
  {
    intros i [Hsel | [q [Hq Hvertex]]].
    - pose proof (proj1 Hcentres i (Hinside i Hsel)) as Hv.
      unfold NonOnePairCenter in Hv. lia.
    - pose proof (Hblocks q Hq) as Hb.
      unfold InteriorOneBlock in Hb. lia.
  }
  assert (Hchosen_card :
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) =
      Zlength selected + ListLib.sum (map fst ordered)).
  {
    unfold chosen.
    apply structured_pair_block_choice_cardinality__certificate_bootstrap
      with (centres := centres); assumption.
  }
  set (transformed_sad := #(fun edge : Z =>
    0 <= edge < Zlength a - 1 /\
    Z.gcd
      (if prop_dec (chosen edge) then 0 else Znth edge a 0)
      (if prop_dec (chosen (edge + 1)) then 0
       else Znth (edge + 1) a 0) = 1)).
  pose proof (choice_sadness_is_base_minus_removed__certificate_bootstrap
    a chosen base_sad transformed_sad Hnonneg Hbase ltac:(reflexivity))
    as Hpartition.
  assert (Hremoved :
    #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) <> 1) =
      2 * Zlength selected +
        ListLib.sum (map (fun len => len + 1) (map fst ordered))).
  {
    transitivity (#(fun edge : Z => 0 <= edge < Zlength a - 1 /\
      ((exists center, In center selected /\
          (edge = center - 1 \/ edge = center)) \/
       (exists q, 0 <= q < Zlength ordered /\
          snd (Znth q ordered (0, 0)) - 1 <= edge <
          snd (Znth q ordered (0, 0)) +
            fst (Znth q ordered (0, 0)))))).
    - apply set_card_iff__exam_bridge. intros edge.
      pose proof
        (structured_pair_block_choice_removed_edges__certificate_bootstrap
          a centres selected ordered Hnonneg Hcentres Hinside Hblocks edge)
        as Hiff.
      split.
      * intros Hremoved_edge. split.
        -- exact (proj1 Hremoved_edge).
        -- exact (proj1 Hiff Hremoved_edge).
      * intros [_ Hunion]. exact (proj2 Hiff Hunion).
    - apply structured_pair_block_removed_cardinality__certificate_bootstrap
        with (centres := centres); assumption.
  }
  exists chosen. split; [exact Hrange |]. split; [exact Hchosen_card |].
  unfold transformed_sad in Hpartition. rewrite Hremoved in Hpartition.
  lia.
Qed.
Lemma canonical_greedy_prefix_choice__certificate_bootstrap :
  forall a base_sad pair_savings lengths original_k sorted use next
      remaining sadness,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    CanonicalInteriorOneRunPrefix a (Zlength a) lengths ->
    1 <= original_k <= Zlength a ->
    Permutation lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    exists chosen : Z -> Prop,
      (forall i, chosen i -> 0 <= i < Zlength a) /\
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i) =
        original_k - remaining /\
      sadness = #(fun edge : Z =>
        0 <= edge < Zlength a - 1 /\
        Z.gcd
          (if prop_dec (chosen edge) then 0 else Znth edge a 0)
          (if prop_dec (chosen (edge + 1)) then 0
           else Znth (edge + 1) a 0) = 1).
Proof.
  intros a base_sad pair_savings lengths original_k sorted use next
    remaining sadness Hnonneg Hbase Hpair Hcanonical Hk Hperm Hsorted
    Huse Hgreedy.
  destruct (pair_savings_prefix_witness__certificate_bootstrap
    a pair_savings Hpair) as [allcentres
      [Hallselection [Hallcount Hpairnonneg]]].
  unfold MinValue in Huse.
  assert (Husebounds : 0 <= use <= pair_savings /\ use <= original_k).
  {
    subst use. rewrite Z.min_glb_iff. lia.
  }
  destruct (pair_savings_has_exact_subselection__certificate_bootstrap
    a pair_savings use Hpair (proj1 Husebounds)) as
    [centres [selected
      [Hselection [Hselected_nodup [Hinside [Hselected_len Hselcard]]]]]].
  destruct (canonical_profile_sorted_block_pairs_strong__certificate_bootstrap
    a lengths sorted Hcanonical Hperm) as
    [ordered [Hordered_map [Hordered_nodup
      [Hordered_blocks [Hordered_ends Hordered_startinj]]]]].
  assert (Hordered_len : Zlength ordered = Zlength sorted).
  { rewrite <- Hordered_map, Zlength_map__certificate_bootstrap. reflexivity. }
  destruct (sorted_ordered_prefix_properties__certificate_bootstrap
    a sorted ordered next Hordered_map Hordered_nodup Hordered_blocks
    Hordered_startinj ltac:(pose proof (proj1 Hgreedy); lia)) as
    [prefix [Hprefix [Hprefix_len [Hprefix_map
      [Hprefix_nodup [Hprefix_blocks Hprefix_startinj]]]]]].
  destruct Hgreedy as [Hnext [Hremaining [Hsadness Hfit]]].
  destruct (structured_pair_block_choice_profile__certificate_bootstrap
    a base_sad centres selected prefix Hnonneg Hbase Hselection
    Hselected_nodup Hprefix_nodup Hinside Hprefix_startinj Hprefix_blocks)
    as [chosen [Hrange [Hcard Hprofile_sad]]].
  exists chosen. split; [exact Hrange |]. split.
  - rewrite Hcard, Hselected_len, Hprefix_map. lia.
  - rewrite Hprofile_sad, Hselected_len, Hprefix_map. lia.
Qed.
Lemma canonical_stopped_greedy_upper_bound__certificate_bootstrap :
  forall a base_sad pair_savings lengths original_k sorted use next
      remaining sadness out,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    (exists j, 0 <= j < Zlength a /\ Znth j a 0 <> 1) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    CanonicalInteriorOneRunPrefix a (Zlength a) lengths ->
    1 <= original_k <= Zlength a ->
    Permutation lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    FinalBudgetResult remaining sadness out ->
    exists result final_sad,
      SimplifiedExams a original_k result /\
      ExamSadness result final_sad /\
      final_sad <= out.
Proof.
  intros a base_sad pair_savings lengths original_k sorted use next
    remaining sadness out Hnonneg Hnonone Hbase Hpair Hcanonical Hk
    Hperm Hsorted Huse Hgreedy Hfinal.
  pose proof (greedy_block_state_remaining_nonnegative__certificate_bootstrap
    sorted next (original_k - use) (base_sad - 2 * use)
    remaining sadness ltac:(unfold MinValue in Huse; lia) Hgreedy)
    as Hremaining_nonneg.
  destruct (canonical_greedy_prefix_choice__certificate_bootstrap
    a base_sad pair_savings lengths original_k sorted use next remaining
    sadness Hnonneg Hbase Hpair Hcanonical Hk Hperm Hsorted Huse Hgreedy)
    as [chosen [Hrange [Hcard Hsad]]].
  assert (Hsad_nonneg : 0 <= sadness).
  {
    rewrite Hsad.
    apply set_card_nonnegative__pair_scan_exits.
  }
  set (spent := Z.min remaining sadness).
  assert (Hspent : 0 <= spent /\ spent <= remaining /\ spent <= sadness).
  { unfold spent. rewrite Z.min_glb_iff. lia. }
  assert (Hout : out = sadness - spent).
  {
    unfold FinalBudgetResult in Hfinal.
    unfold spent. rewrite Z.max_r in Hfinal by lia. exact Hfinal.
  }
  assert (Hfuel : sadness - out <= Z.of_nat (Z.to_nat spent)).
  { rewrite Hout, Z2Nat.id by lia. lia. }
  destruct (residual_zero_reduction_with_fuel__certificate_bootstrap
    (Z.to_nat spent) a chosen sadness out Hrange Hnonneg Hnonone Hsad
    ltac:(rewrite Hout; lia) Hfuel) as
    [extended [final_sad [Hextended [Hextended_card
      [Hfinal_sad Hfinal_bound]]]]].
  assert (Hcard_budget :
    #(fun i : Z => 0 <= i < Zlength a /\ extended i) <= original_k).
  {
    rewrite Z2Nat.id in Hextended_card by lia.
    rewrite Hcard in Hextended_card. lia.
  }
  destruct (materialize_exam_choice_sadness__certificate_bootstrap
    a original_k extended final_sad Hextended Hcard_budget Hfinal_sad)
    as [result [Hresult Hresult_sad]].
  exists result, final_sad. repeat split; assumption.
Qed.
Lemma removed_edges_at_most_choices_plus_collisions__certificate_bootstrap :
  forall a (chosen : Z -> Prop),
    let Removed := fun edge : Z =>
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) <> 1 in
    let Collision := fun center : Z =>
      1 <= center < Zlength a - 1 /\
      chosen center /\ ~ chosen (center - 1) /\
      Removed (center - 1) /\ Removed center in
    #(fun edge : Z => 0 <= edge < Zlength a - 1 /\ Removed edge) <=
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i) +
      #(fun center : Z =>
        1 <= center < Zlength a - 1 /\ Collision center).
Proof.
  intros a chosen. cbn zeta.
  set (Removed := fun edge : Z =>
    Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
    Z.gcd
      (if prop_dec (chosen edge) then 0 else Znth edge a 0)
      (if prop_dec (chosen (edge + 1)) then 0
       else Znth (edge + 1) a 0) <> 1).
  set (Collision := fun center : Z =>
    1 <= center < Zlength a - 1 /\
    chosen center /\ ~ chosen (center - 1) /\
    Removed (center - 1) /\ Removed center).
  pose proof (set_card_partition_subset_Z__certificate_bootstrap
    0 (Zlength a - 1) Removed Collision) as Hpartition.
  specialize (Hpartition ltac:(intros center Hcenter Hcollision;
    unfold Collision in Hcollision; tauto)).
  assert (Hnonbonus :
    #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\ Removed edge /\ ~ Collision edge) <=
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i)).
  {
    eapply set_card_injection_le__pair_scan_exits with
      (f := fun edge =>
        if prop_dec (chosen edge) then edge else edge + 1).
    - intros edge [Hedge [Hremoved Hnotcollision]].
      unfold Removed in Hremoved.
      destruct Hremoved as [Horiginal Hchanged].
      destruct (prop_dec (chosen edge)) as [Hleft | Hleft].
      + split; [lia | exact Hleft].
      + assert (Hright : chosen (edge + 1)).
        {
          destruct (prop_dec (chosen (edge + 1))) as [Hright | Hright];
            [exact Hright |].
          simpl in Hchanged. contradiction.
        }
        split; [lia | exact Hright].
    - intros x y [Hx [HRx Hnotx]] [Hy [HRy Hnoty]] Heq.
      destruct (prop_dec (chosen x)) as [Hcx | Hcx];
        destruct (prop_dec (chosen y)) as [Hcy | Hcy]; simpl in Heq.
      + exact Heq.
      + exfalso. apply Hnotx. unfold Collision.
        replace (x - 1) with y by lia.
        split; [lia |]. split; [exact Hcx |]. split; [exact Hcy |].
        split; [exact HRy | exact HRx].
      + exfalso. apply Hnoty. unfold Collision.
        replace (y - 1) with x by lia.
        split; [lia |]. split; [exact Hcy |]. split; [exact Hcx |].
        split; [exact HRx | exact HRy].
      + lia.
  }
  change (#(fun edge : Z => 0 <= edge < Zlength a - 1 /\ Removed edge) <=
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) +
    #(fun center : Z =>
      1 <= center < Zlength a - 1 /\ Collision center)).
  assert (Hcollision_range :
    #(fun z : Z => 0 <= z < Zlength a - 1 /\ Collision z) =
    #(fun z : Z => 1 <= z < Zlength a - 1 /\ Collision z)).
  {
    apply set_card_iff__exam_bridge. intros z. split.
    - intros [Hz Hc]. split; [exact (proj1 Hc) | exact Hc].
    - intros [Hz Hc]. split; [lia | exact Hc].
  }
  rewrite Hpartition, Hcollision_range. lia.
Qed.
Lemma chosen_run_start_exists__certificate_bootstrap :
  forall (chosen : Z -> Prop) endpoint,
    0 <= endpoint -> chosen endpoint ->
    exists start,
      0 <= start <= endpoint /\
      (start = 0 \/ ~ chosen (start - 1)) /\
      forall j, start <= j <= endpoint -> chosen j.
Proof.
  intros chosen endpoint Hendpoint.
  remember (Z.to_nat endpoint) as d eqn:Hd.
  assert (Hendpoint_eq : endpoint = Z.of_nat d).
  { subst d. rewrite Z2Nat.id by lia. reflexivity. }
  subst endpoint. clear Hd Hendpoint.
  induction d as [|d IH]; intros Hend.
  - exists 0.
    repeat split; try lia. intros j Hj. replace j with 0 by lia. exact Hend.
  - destruct (classic (chosen (Z.of_nat d))) as [Hprev | Hprev].
    + destruct (IH Hprev) as [start [Hrange [Hboundary Hall]]].
      exists start.
      split; [rewrite Nat2Z.inj_succ; lia |]. split; [exact Hboundary |].
      intros j Hj.
      destruct (Z.eq_dec j (Z.of_nat (S d))) as [-> | Hneq];
        [exact Hend |].
      apply Hall. rewrite Nat2Z.inj_succ in Hj. lia.
    + exists (Z.of_nat (S d)).
      split; [lia |]. split.
      * right. replace (Z.of_nat (S d) - 1) with (Z.of_nat d)
          by (rewrite Nat2Z.inj_succ; lia). exact Hprev.
      * intros j Hj. replace j with (Z.of_nat (S d)) by lia. exact Hend.
Qed.
Lemma chosen_run_start_unique__certificate_bootstrap :
  forall (chosen : Z -> Prop) endpoint s t,
    (0 <= s <= endpoint /\
      (s = 0 \/ ~ chosen (s - 1)) /\
      forall j, s <= j <= endpoint -> chosen j) ->
    (0 <= t <= endpoint /\
      (t = 0 \/ ~ chosen (t - 1)) /\
      forall j, t <= j <= endpoint -> chosen j) ->
    s = t.
Proof.
  intros chosen endpoint s t [Hs [Hsb Halls]] [Ht [Htb Hallt]].
  destruct (Z.lt_trichotomy s t) as [Hst | [-> | Hts]];
    [|reflexivity|].
  - destruct Htb as [-> | Hnot]; [lia |].
    exfalso. apply Hnot. apply Halls. lia.
  - destruct Hsb as [-> | Hnot]; [lia |].
    exfalso. apply Hnot. apply Hallt. lia.
Qed.
Lemma chain_start_exists__certificate_bootstrap :
  forall (link : Z -> Prop) endpoint,
    0 <= endpoint ->
    exists start,
      0 <= start <= endpoint /\
      (start = 0 \/ ~ link (start - 1)) /\
      forall j, start <= j < endpoint -> link j.
Proof.
  intros link endpoint Hendpoint.
  remember (Z.to_nat endpoint) as d eqn:Hd.
  assert (Hendpoint_eq : endpoint = Z.of_nat d).
  { subst d. rewrite Z2Nat.id by lia. reflexivity. }
  subst endpoint. clear Hd Hendpoint.
  induction d as [|d IH].
  - exists 0. repeat split; lia.
  - destruct (classic (link (Z.of_nat d))) as [Hprev | Hprev].
    + destruct IH as [start [Hrange [Hboundary Hall]]].
      exists start. split; [rewrite Nat2Z.inj_succ; lia |].
      split; [exact Hboundary |]. intros j Hj.
      destruct (Z.eq_dec j (Z.of_nat d)) as [-> | Hneq];
        [exact Hprev |]. apply Hall. rewrite Nat2Z.inj_succ in Hj. lia.
    + exists (Z.of_nat (S d)). split; [lia |]. split.
      * right. replace (Z.of_nat (S d) - 1) with (Z.of_nat d)
          by (rewrite Nat2Z.inj_succ; lia). exact Hprev.
      * intros j Hj. lia.
Qed.
Lemma chain_start_unique__certificate_bootstrap :
  forall (link : Z -> Prop) endpoint s t,
    (0 <= s <= endpoint /\
      (s = 0 \/ ~ link (s - 1)) /\
      forall j, s <= j < endpoint -> link j) ->
    (0 <= t <= endpoint /\
      (t = 0 \/ ~ link (t - 1)) /\
      forall j, t <= j < endpoint -> link j) ->
    s = t.
Proof.
  intros link endpoint s t [Hs [Hsb Halls]] [Ht [Htb Hallt]].
  destruct (Z.lt_trichotomy s t) as [Hst | [-> | Hts]];
    [|reflexivity|].
  - destruct Htb as [-> | Hnot]; [lia |].
    exfalso. apply Hnot. apply Halls. lia.
  - destruct Hsb as [-> | Hnot]; [lia |].
    exfalso. apply Hnot. apply Hallt. lia.
Qed.
Lemma removed_edges_at_most_choices_plus_closed_runs__certificate_bootstrap :
  forall a (chosen : Z -> Prop),
    let Removed := fun edge : Z =>
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) <> 1 in
    let ClosedRun := fun start : Z =>
      1 <= start < Zlength a - 1 /\
      ~ chosen (start - 1) /\ Removed (start - 1) /\
      exists endpoint,
        start <= endpoint < Zlength a - 1 /\
        (forall j, start <= j <= endpoint -> chosen j) /\
        (forall edge, start <= edge < endpoint -> Removed edge) /\
        ~ chosen (endpoint + 1) /\ Removed endpoint in
    #(fun edge : Z => 0 <= edge < Zlength a - 1 /\ Removed edge) <=
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i) +
      #(fun start : Z =>
        1 <= start < Zlength a - 1 /\ ClosedRun start).
Proof.
  intros a chosen. cbn zeta.
  set (Removed := fun edge : Z =>
    Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
    Z.gcd
      (if prop_dec (chosen edge) then 0 else Znth edge a 0)
      (if prop_dec (chosen (edge + 1)) then 0
       else Znth (edge + 1) a 0) <> 1).
  set (Start := fun endpoint start : Z =>
    0 <= start <= endpoint /\
    (start = 0 \/ ~ (chosen (start - 1) /\ Removed (start - 1))) /\
    forall j, start <= j < endpoint -> chosen j /\ Removed j).
  set (start_of := fun endpoint : Z =>
    epsilon (inhabits 0%Z) (Start endpoint)).
  assert (Hstart : forall endpoint,
    0 <= endpoint -> Start endpoint (start_of endpoint)).
  {
    intros endpoint Hendpoint.
    unfold start_of. apply epsilon_spec. unfold Start.
    apply (chain_start_exists__certificate_bootstrap
      (fun j => chosen j /\ Removed j) endpoint). exact Hendpoint.
  }
  set (ClosedRun := fun start : Z =>
    1 <= start < Zlength a - 1 /\
    ~ chosen (start - 1) /\ Removed (start - 1) /\
    exists endpoint,
      start <= endpoint < Zlength a - 1 /\
      (forall j, start <= j <= endpoint -> chosen j) /\
      (forall edge, start <= edge < endpoint -> Removed edge) /\
      ~ chosen (endpoint + 1) /\ Removed endpoint).
  assert (Hclosed_range : forall start, ClosedRun start ->
    1 <= start < Zlength a - 1).
  { intros start Hclosed. exact (proj1 Hclosed). }
  set (Target := fun z : Z =>
    (0 <= z /\ chosen z) \/ (z < 0 /\ ClosedRun (- z))).
  assert (Htarget_card :
    #(fun z : Z => - Zlength a <= z < Zlength a /\ Target z) =
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i) +
      #(fun start : Z =>
        1 <= start < Zlength a - 1 /\ ClosedRun start)).
  {
    pose proof (set_card_partition_subset_Z__certificate_bootstrap
      (- Zlength a) (Zlength a) Target
      (fun z => 0 <= z /\ chosen z)) as Hpart.
    specialize (Hpart ltac:(intros z Hz Hbase; left; exact Hbase)).
    assert (Hbase_card :
      #(fun z : Z => - Zlength a <= z < Zlength a /\
        (0 <= z /\ chosen z)) =
      #(fun z : Z => 0 <= z < Zlength a /\ chosen z)).
    {
      apply set_card_iff__exam_bridge. intros z. split.
      - intros [Hz [Hz0 Hchosen]]. split; [lia | exact Hchosen].
      - intros [Hz Hchosen]. split; [lia |]. split; [lia | exact Hchosen].
    }
    assert (Hrest_card :
      #(fun z : Z => - Zlength a <= z < Zlength a /\
        Target z /\ ~ (0 <= z /\ chosen z)) =
      #(fun z : Z => - Zlength a <= z < 0 /\ ClosedRun (- z))).
    {
      apply set_card_iff__exam_bridge. intros z. unfold Target.
      split.
      - intros [Hz [[Hbase | Hbonus] Hnot]].
        + contradiction.
        + split; [lia | exact (proj2 Hbonus)].
      - intros [Hz Hbonus]. split; [lia |]. split.
        + right. split; [lia | exact Hbonus].
        + lia.
    }
    rewrite Hpart, Hbase_card, Hrest_card.
    rewrite <- (negated_center_cardinality__certificate_bootstrap
      (Zlength a) ClosedRun Hclosed_range).
    reflexivity.
  }
  rewrite <- Htarget_card.
  eapply set_card_injection_le__pair_scan_exits with
    (f := fun edge =>
      if prop_dec (chosen (edge + 1)) then edge + 1
      else let start := start_of edge in
        if prop_dec (1 <= start /\ Removed (start - 1))
        then - start else start).
  - intros edge [Hedge Hremoved].
    assert (Hcover : chosen edge \/ chosen (edge + 1)).
    {
      unfold Removed in Hremoved.
      destruct Hremoved as [Horiginal Hchanged].
      destruct (prop_dec (chosen edge)) as [Hleft | Hleft];
        [left; exact Hleft |].
      destruct (prop_dec (chosen (edge + 1))) as [Hright | Hright];
        [right; exact Hright |].
      simpl in Hchanged. contradiction.
    }
    destruct (prop_dec (chosen (edge + 1))) as [Hright | Hright].
    + split; [lia |]. unfold Target. left. split; [lia | exact Hright].
    + assert (Hleft : chosen edge) by tauto.
      pose proof (Hstart edge ltac:(lia)) as Hspec.
      cbn zeta.
      destruct (prop_dec
        (1 <= start_of edge /\ Removed (start_of edge - 1))) as
        [Hbonus | Hbonus].
      * simpl. split.
        -- pose proof (proj1 Hspec). lia.
        -- unfold Target. right. split; [lia |].
           replace (- - start_of edge) with (start_of edge) by ring.
           unfold ClosedRun.
           destruct Hspec as [Hsrange [Hsboundary Hsall]].
           split; [lia |]. split.
           ++ destruct Hsboundary as [Hs0 | Hsnot]; [lia |].
              intro Hchosen_prev. apply Hsnot. split;
                [exact Hchosen_prev | exact (proj2 Hbonus)].
           ++ split; [exact (proj2 Hbonus) |].
              exists edge. split; [lia |]. split.
              ** intros j Hj. destruct (Z.eq_dec j edge) as [-> | Hneq];
                   [exact Hleft |]. apply (proj1 (Hsall j ltac:(lia))).
              ** split.
                 --- intros e He. exact (proj2 (Hsall e He)).
                 --- split; [exact Hright | exact Hremoved].
      * simpl. split.
        -- pose proof (proj1 Hspec). lia.
        -- unfold Target. left. split.
           ++ pose proof (proj1 Hspec). lia.
           ++ destruct Hspec as [Hsrange [_ Hsall]].
              destruct (Z.eq_dec (start_of edge) edge) as [Heq | Hneq].
              ** rewrite Heq. exact Hleft.
              ** exact (proj1 (Hsall (start_of edge) ltac:(lia))).
  - intros x y [Hx HRx] [Hy HRy] Heq.
    assert (Hcoverx : chosen x \/ chosen (x + 1)).
    {
      unfold Removed in HRx.
      destruct HRx as [Horiginal Hchanged].
      destruct (prop_dec (chosen x)) as [Hleft | Hleft]; [tauto |].
      destruct (prop_dec (chosen (x + 1))) as [Hright | Hright]; [tauto |].
      simpl in Hchanged. contradiction.
    }
    assert (Hcovery : chosen y \/ chosen (y + 1)).
    {
      unfold Removed in HRy.
      destruct HRy as [Horiginal Hchanged].
      destruct (prop_dec (chosen y)) as [Hleft | Hleft]; [tauto |].
      destruct (prop_dec (chosen (y + 1))) as [Hright | Hright]; [tauto |].
      simpl in Hchanged. contradiction.
    }
    cbn zeta in Heq.
    destruct (prop_dec (chosen (x + 1))) as [Hxr | Hxr];
      destruct (prop_dec (chosen (y + 1))) as [Hyr | Hyr].
    + simpl in Heq. lia.
    + assert (Hyl : chosen y) by tauto.
      pose proof (Hstart y ltac:(lia)) as Hyspec.
      destruct (prop_dec
        (1 <= start_of y /\ Removed (start_of y - 1))) as
        [Hybonus | Hybonus]; simpl in Heq.
      * change (x + 1 = - start_of y) in Heq.
        destruct Hybonus as [Hypos Hyremoved]. lia.
      * assert (Hstart_eq : start_of y = x + 1) by lia.
        exfalso. apply Hybonus. split; [lia |].
        rewrite Hstart_eq. replace (x + 1 - 1) with x by lia. exact HRx.
    + assert (Hxl : chosen x) by tauto.
      pose proof (Hstart x ltac:(lia)) as Hxspec.
      destruct (prop_dec
        (1 <= start_of x /\ Removed (start_of x - 1))) as
        [Hxbonus | Hxbonus]; simpl in Heq.
      * change (- start_of x = y + 1) in Heq.
        destruct Hxbonus as [Hxpos Hxremoved]. lia.
      * assert (Hstart_eq : start_of x = y + 1) by lia.
        exfalso. apply Hxbonus. split; [lia |].
        rewrite Hstart_eq. replace (y + 1 - 1) with y by lia. exact HRy.
    + assert (Hxl : chosen x) by tauto.
      assert (Hyl : chosen y) by tauto.
      pose proof (Hstart x ltac:(lia)) as Hxspec.
      pose proof (Hstart y ltac:(lia)) as Hyspec.
      destruct (prop_dec
        (1 <= start_of x /\ Removed (start_of x - 1))) as
        [Hxbonus | Hxbonus];
        destruct (prop_dec
          (1 <= start_of y /\ Removed (start_of y - 1))) as
          [Hybonus | Hybonus]; simpl in Heq.
      * assert (Hs : start_of x = start_of y) by lia.
        destruct Hxspec as [Hxrange [_ Hxall]].
        destruct Hyspec as [Hyrange [_ Hyall]].
        destruct (Z.lt_trichotomy x y) as [Hxy | [-> | Hyx]].
        -- exfalso. apply Hxr.
           destruct (Z.eq_dec (x + 1) y) as [He | Hne].
           ++ rewrite He. exact Hyl.
           ++ exact (proj1 (Hyall (x + 1) ltac:(lia))).
        -- reflexivity.
        -- exfalso. apply Hyr.
           destruct (Z.eq_dec (y + 1) x) as [He | Hne].
           ++ rewrite He. exact Hxl.
           ++ exact (proj1 (Hxall (y + 1) ltac:(lia))).
      * destruct Hxbonus as [Hxpos Hxremoved].
        pose proof (proj1 Hyspec). lia.
      * destruct Hybonus as [Hypos Hyremoved].
        pose proof (proj1 Hxspec). lia.
      * assert (Hs : start_of x = start_of y) by lia.
        destruct Hxspec as [Hxrange [_ Hxall]].
        destruct Hyspec as [Hyrange [_ Hyall]].
        destruct (Z.lt_trichotomy x y) as [Hxy | [-> | Hyx]].
        -- exfalso. apply Hxr.
           destruct (Z.eq_dec (x + 1) y) as [He | Hne].
           ++ rewrite He. exact Hyl.
           ++ exact (proj1 (Hyall (x + 1) ltac:(lia))).
        -- reflexivity.
        -- exfalso. apply Hyr.
           destruct (Z.eq_dec (y + 1) x) as [He | Hne].
           ++ rewrite He. exact Hxl.
           ++ exact (proj1 (Hxall (y + 1) ltac:(lia))).
Qed.
Lemma one_run_left_boundary_with_fuel__certificate_bootstrap :
  forall (fuel : nat) a low j,
    0 < low <= j -> Znth (low - 1) a 0 <> 1 -> Znth j a 0 = 1 ->
    j - low <= Z.of_nat fuel ->
    exists lo, low <= lo <= j /\ Znth (lo - 1) a 0 <> 1 /\
      forall t, lo <= t <= j -> Znth t a 0 = 1.
Proof.
  induction fuel as [|fuel IH]; intros a low j Hbounds Hleft Hj Hfuel.
  - exists low. assert (j = low) by (simpl in Hfuel; lia). subst j.
    split; [lia |]. split; [exact Hleft |].
    intros t Ht. replace t with low by lia. exact Hj.
  - destruct (Z.eq_dec j low) as [-> | Hneq].
    + exists low. split; [lia |]. split; [exact Hleft |].
      intros t Ht. replace t with low by lia. exact Hj.
    + destruct (Z.eq_dec (Znth (j - 1) a 0) 1) as [Hprev | Hprev].
      * assert (Hfuel' : j - 1 - low <= Z.of_nat fuel).
        { simpl in Hfuel. lia. }
        destruct (IH a low (j - 1) ltac:(lia) Hleft Hprev Hfuel') as
          [lo [Hlo [Hlobound Hall]]].
        exists lo. split; [lia |]. split; [exact Hlobound |].
        intros t Ht. destruct (Z.eq_dec t j) as [-> | Htneq];
          [exact Hj |]. apply Hall. lia.
      * exists j. split; [lia |]. split; [exact Hprev |].
        intros t Ht. replace t with j by lia. exact Hj.
Qed.
Lemma one_run_right_boundary_with_fuel__certificate_bootstrap :
  forall (fuel : nat) a high j,
    j < high < Zlength a -> Znth high a 0 <> 1 -> Znth j a 0 = 1 ->
    high - 1 - j <= Z.of_nat fuel ->
    exists hi, j < hi <= high /\ Znth hi a 0 <> 1 /\
      forall t, j <= t < hi -> Znth t a 0 = 1.
Proof.
  induction fuel as [|fuel IH]; intros a high j Hbounds Hright Hj Hfuel.
  - exists high. assert (j = high - 1) by (simpl in Hfuel; lia). subst j.
    split; [lia |]. split; [exact Hright |].
    intros t Ht. replace t with (high - 1) by lia. exact Hj.
  - destruct (Z.eq_dec (j + 1) high) as [Heq | Hneq].
    + exists high. split; [lia |]. split; [exact Hright |]. intros t Ht.
      replace t with j by lia. exact Hj.
    + destruct (Z.eq_dec (Znth (j + 1) a 0) 1) as [Hnext | Hnext].
      * assert (Hfuel' : high - 1 - (j + 1) <= Z.of_nat fuel).
        { simpl in Hfuel. lia. }
        destruct (IH a high (j + 1) ltac:(lia) Hright Hnext Hfuel') as
          [hi [Hhi [Hhibound Hall]]].
        exists hi. split; [lia |]. split; [exact Hhibound |].
        intros t Ht. destruct (Z.eq_dec t j) as [-> | Htneq];
          [exact Hj |]. apply Hall. lia.
      * exists (j + 1). split; [lia |]. split; [exact Hnext |].
        intros t Ht. replace t with j by lia. exact Hj.
Qed.
Lemma one_between_nonones_has_interior_block__certificate_bootstrap :
  forall a low high j,
    0 < low <= j /\ j < high < Zlength a ->
    Znth (low - 1) a 0 <> 1 -> Znth high a 0 <> 1 ->
    Znth j a 0 = 1 ->
    exists lo hi,
      low <= lo <= j /\ j < hi <= high /\ InteriorOneBlock a lo hi.
Proof.
  intros a low high j Hbounds Hleft Hright Hj.
  destruct (one_run_left_boundary_with_fuel__certificate_bootstrap
    (Z.to_nat (j - low)) a low j ltac:(lia) Hleft Hj
    ltac:(rewrite Z2Nat.id by lia; lia)) as
    [lo [Hlo [Hlobound Hallleft]]].
  destruct (one_run_right_boundary_with_fuel__certificate_bootstrap
    (Z.to_nat (high - 1 - j)) a high j ltac:(lia) Hright Hj
    ltac:(rewrite Z2Nat.id by lia; lia)) as
    [hi [Hhi [Hhibound Hallright]]].
  exists lo, hi. split; [lia |]. split; [lia |]. unfold InteriorOneBlock.
  repeat split; try assumption; try lia.
  intros t Ht. destruct (Z_le_gt_dec t j) as [Htj | Hjt].
  - apply Hallleft. lia.
  - apply Hallright. lia.
Qed.
Lemma interior_block_start_before_endpoint__certificate_bootstrap :
  forall a lo len endpoint,
    InteriorOneBlock a lo (lo + len) ->
    lo + len <= endpoint + 1 ->
    lo <= endpoint.
Proof.
  intros a lo len endpoint Hblock Hbound.
  unfold InteriorOneBlock in Hblock. lia.
Qed.
Lemma closed_run_bonus_bound_by_pairs_and_full_blocks__certificate_bootstrap :
  forall a (chosen : Z -> Prop) pair_savings lengths,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    CanonicalInteriorOneRunPrefix a (Zlength a) lengths ->
    let Removed := fun edge : Z =>
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) <> 1 in
    let ClosedRun := fun start : Z =>
      1 <= start < Zlength a - 1 /\
      ~ chosen (start - 1) /\ Removed (start - 1) /\
      exists endpoint,
        start <= endpoint < Zlength a - 1 /\
        (forall j, start <= j <= endpoint -> chosen j) /\
        (forall edge, start <= edge < endpoint -> Removed edge) /\
        ~ chosen (endpoint + 1) /\ Removed endpoint in
    exists starts,
      Zlength starts = Zlength lengths /\
      mono_inc starts /\
      (forall q, 0 <= q < Zlength lengths ->
        InteriorOneBlock a (Znth q starts 0)
          (Znth q starts 0 + Znth q lengths 0) /\
        Znth q starts 0 + Znth q lengths 0 <= Zlength a) /\
      let Pairish := fun start : Z =>
        ClosedRun start /\ Znth start a 0 <> 1 /\
        Znth (start + 1) a 0 <> 1 in
      PairCenterSelection a (Zlength a) Pairish /\
      (forall center, Pairish center -> chosen center) /\
      #(fun start : Z =>
          1 <= start < Zlength a - 1 /\ ClosedRun start) <=
        #(fun center : Z =>
          1 <= center < Zlength a - 1 /\ Pairish center) +
        #(fun q : Z =>
          0 <= q < Zlength lengths /\
          forall j,
            Znth q starts 0 <= j < Znth q starts 0 + Znth q lengths 0 ->
            chosen j).
Proof.
  intros a chosen pair_savings lengths Hnonneg Hpair Hcanonical.
  cbn zeta.
  destruct Hcanonical as
    [starts [Hstarts_len [Hstarts_inc [Hblocks Hcomplete]]]].
  exists starts. split; [exact Hstarts_len |].
  split; [exact Hstarts_inc |]. split; [exact Hblocks |].
  set (Removed := fun edge : Z =>
    Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
    Z.gcd
      (if prop_dec (chosen edge) then 0 else Znth edge a 0)
      (if prop_dec (chosen (edge + 1)) then 0
       else Znth (edge + 1) a 0) <> 1).
  set (ClosedRun := fun start : Z =>
    1 <= start < Zlength a - 1 /\
    ~ chosen (start - 1) /\ Removed (start - 1) /\
    exists endpoint,
      start <= endpoint < Zlength a - 1 /\
      (forall j, start <= j <= endpoint -> chosen j) /\
      (forall edge, start <= edge < endpoint -> Removed edge) /\
      ~ chosen (endpoint + 1) /\ Removed endpoint).
  set (Pairish := fun start : Z =>
    ClosedRun start /\ Znth start a 0 <> 1 /\ Znth (start + 1) a 0 <> 1).
  set (FullBlock := fun q : Z =>
    forall j,
      Znth q starts 0 <= j < Znth q starts 0 + Znth q lengths 0 ->
      chosen j).
  pose proof (set_card_partition_subset_Z__certificate_bootstrap
    1 (Zlength a - 1) ClosedRun Pairish) as Hpartition.
  specialize (Hpartition ltac:(intros z Hz Hpairish; exact (proj1 Hpairish))).
  assert (Hpairish_selection :
    PairCenterSelection a (Zlength a) Pairish).
  {
    split.
      + intros center Hcenter. unfold Pairish in Hcenter.
        destruct Hcenter as [Hclosed [Hcenter_nonone Hright_nonone]].
        unfold ClosedRun in Hclosed.
        destruct Hclosed as [Hrange [Hnotprev [Hprev
          [endpoint [Hend [Hallchosen [Hallremoved [Hnotnext Hlast]]]]]]]].
        assert (Hchosen_center : chosen center) by (apply Hallchosen; lia).
        assert (Hprev_nonone : Znth (center - 1) a 0 <> 1).
        {
          unfold Removed in Hprev.
          destruct Hprev as [Hprev_orig Hprev_changed].
          replace (center - 1 + 1) with center in Hprev_changed by lia.
          destruct (prop_dec (chosen (center - 1))) as [Hbad | Hbad];
            [contradiction |].
          destruct (prop_dec (chosen center)) as [Hyes | Hyes];
            [|contradiction].
          simpl in Hprev_changed.
          rewrite Z.gcd_0_r_nonneg in Hprev_changed by
            (apply Hnonneg; lia).
          exact Hprev_changed.
        }
        assert (Hedge_right : Removed center).
        {
          destruct (Z.eq_dec endpoint center) as [-> | Hneq];
            [exact Hlast | apply Hallremoved; lia].
        }
        unfold NonOnePairCenter. split; [exact Hrange |].
        split; [exact Hprev_nonone |]. split; [exact Hcenter_nonone |].
        split; [exact Hright_nonone |]. split.
        * unfold AdjacentCoprime. split; [lia |].
          unfold Removed in Hprev. exact (proj1 Hprev).
        * unfold AdjacentCoprime. split; [lia |].
          unfold Removed in Hedge_right. exact (proj1 Hedge_right).
      + intros x y Hx Hy Hneq.
        unfold Pairish, ClosedRun in Hx, Hy.
        destruct Hx as [[Hxr [Hxn [Hxprev
          [xe [Hxe [Hxall Hxrest]]]]]] Hxvalues].
        destruct Hy as [[Hyr [Hyn [Hyprev
          [ye [Hye [Hyall Hyrest]]]]]] Hyvalues].
        destruct (Z.lt_trichotomy x y) as [Hxy | [Heq | Hyx]];
          [|contradiction|].
        * destruct (Z.eq_dec y (x + 1)) as [-> | Hfar].
          -- exfalso. apply Hyn. replace (x + 1 - 1) with x by lia.
             apply Hxall. lia.
          -- rewrite Z.abs_neq by lia. lia.
        * destruct (Z.eq_dec x (y + 1)) as [-> | Hfar].
          -- exfalso. apply Hxn. replace (y + 1 - 1) with y by lia.
             apply Hyall. lia.
          -- rewrite Z.abs_eq by lia. lia.
  }
  assert (Hpairish_bound :
    #(fun start : Z => 1 <= start < Zlength a - 1 /\ Pairish start) <=
    pair_savings).
  { apply pair_savings_bounds_every_selection__certificate_bootstrap;
      assumption. }
  assert (Hnonpair_bound :
    #(fun start : Z => 1 <= start < Zlength a - 1 /\
      ClosedRun start /\ ~ Pairish start) <=
    #(fun q : Z => 0 <= q < Zlength lengths /\ FullBlock q)).
  {
    set (BlockWitness := fun start q : Z =>
      0 <= q < Zlength lengths /\
      exists endpoint,
        start <= endpoint < Zlength a - 1 /\
        (forall j, start <= j <= endpoint -> chosen j) /\
        ~ chosen (endpoint + 1) /\
        start <= Znth q starts 0 /\
        Znth q starts 0 + Znth q lengths 0 <= endpoint + 1 /\
        FullBlock q).
    assert (Hwitness : forall start,
      1 <= start < Zlength a - 1 -> ClosedRun start -> ~ Pairish start ->
      exists q, BlockWitness start q).
    {
      intros start Hstart Hclosed Hnotpair.
      pose proof Hclosed as Hclosed_copy.
      unfold ClosedRun in Hclosed.
      destruct Hclosed as [Hrange [Hnotprev [Hprev
        [endpoint [Hend [Hallchosen [Hallremoved [Hnotnext Hlast]]]]]]]].
      assert (Hprev_nonone : Znth (start - 1) a 0 <> 1).
      {
        assert (Hchosen_start : chosen start) by (apply Hallchosen; lia).
        unfold Removed in Hprev.
        destruct Hprev as [Horig Hchanged].
        replace (start - 1 + 1) with start in Hchanged by lia.
        destruct (prop_dec (chosen (start - 1))) as [Hbad | Hbad];
          [contradiction |].
        destruct (prop_dec (chosen start)) as [Hyes | Hyes];
          [|contradiction].
        simpl in Hchanged.
        rewrite Z.gcd_0_r_nonneg in Hchanged by (apply Hnonneg; lia).
        exact Hchanged.
      }
      assert (Hnext_nonone : Znth (endpoint + 1) a 0 <> 1).
      {
        assert (Hchosen_end : chosen endpoint) by (apply Hallchosen; lia).
        unfold Removed in Hlast.
        destruct Hlast as [Horig Hchanged].
        destruct (prop_dec (chosen endpoint)) as [Hyes | Hyes];
          [|contradiction].
        destruct (prop_dec (chosen (endpoint + 1))) as [Hbad | Hbad];
          [contradiction |].
        simpl in Hchanged.
        rewrite Z.gcd_0_l_nonneg in Hchanged by (apply Hnonneg; lia).
        exact Hchanged.
      }
      assert (Hone : Znth start a 0 = 1 \/ Znth (start + 1) a 0 = 1).
      {
        unfold Pairish in Hnotpair.
        destruct (Z.eq_dec (Znth start a 0) 1) as [Hone | Hone]; [tauto |].
        destruct (Z.eq_dec (Znth (start + 1) a 0) 1) as [Htwo | Htwo];
          [tauto |]. exfalso. apply Hnotpair.
        split; [exact Hclosed_copy |]. split; assumption.
      }
      destruct Hone as [Hone | Hone].
      - destruct (one_between_nonones_has_interior_block__certificate_bootstrap
          a start (endpoint + 1) start ltac:(lia) Hprev_nonone
          Hnext_nonone Hone) as [lo [hi [Hlo [Hhi Hblock]]]].
        destruct (Hcomplete lo hi Hblock ltac:(unfold InteriorOneBlock in Hblock; lia))
          as [q [Hq [Hqstart Hqlen]]].
        exists q. unfold BlockWitness. split; [exact Hq |].
        exists endpoint. repeat split; try assumption; try lia.
        unfold FullBlock. intros j Hj. apply Hallchosen.
        rewrite Hqstart, Hqlen in Hj. lia.
      - assert (Hinside : start + 1 <= endpoint).
        { destruct (Z.eq_dec endpoint start) as [-> | Hneq];
            [contradiction | lia]. }
        destruct (one_between_nonones_has_interior_block__certificate_bootstrap
          a start (endpoint + 1) (start + 1) ltac:(lia) Hprev_nonone
          Hnext_nonone Hone) as [lo [hi [Hlo [Hhi Hblock]]]].
        destruct (Hcomplete lo hi Hblock ltac:(unfold InteriorOneBlock in Hblock; lia))
          as [q [Hq [Hqstart Hqlen]]].
        exists q. unfold BlockWitness. split; [exact Hq |].
        exists endpoint. repeat split; try assumption; try lia.
        unfold FullBlock. intros j Hj. apply Hallchosen.
        rewrite Hqstart, Hqlen in Hj. lia.
    }
    eapply set_card_injection_le__pair_scan_exits with
      (f := fun start => epsilon (inhabits 0%Z) (BlockWitness start)).
    - intros start [Hstart [Hclosed Hnotpair]].
      pose proof (epsilon_spec (inhabits 0%Z) (BlockWitness start)
        (Hwitness start Hstart Hclosed Hnotpair)) as Hw.
      unfold BlockWitness in Hw.
      destruct Hw as [Hq [endpoint [Hend [Hall [Hnotnext
        [Hlo [Hhi Hfull]]]]]]].
      split; assumption.
    - intros x y [Hx [Hclosedx Hnotx]] [Hy [Hclosedy Hnoty]] Heq.
      pose proof (epsilon_spec (inhabits 0%Z) (BlockWitness x)
        (Hwitness x Hx Hclosedx Hnotx)) as Hwx.
      pose proof (epsilon_spec (inhabits 0%Z) (BlockWitness y)
        (Hwitness y Hy Hclosedy Hnoty)) as Hwy.
      unfold BlockWitness in Hwx, Hwy.
      destruct Hwx as [Hqx Hwx1]. destruct Hwx1 as [xe Hwx2].
      destruct Hwx2 as [Hxe Hwx3]. destruct Hwx3 as [Hxchosen Hwx4].
      destruct Hwx4 as [Hxnotnext Hwx5]. destruct Hwx5 as [Hxlo Hwx6].
      destruct Hwy as [Hqy Hwy1]. destruct Hwy1 as [ye Hwy2].
      destruct Hwy2 as [Hye Hwy3]. destruct Hwy3 as [Hychosen Hwy4].
      destruct Hwy4 as [Hynotnext Hwy5]. destruct Hwy5 as [Hylo Hwy6].
      assert (Hbxe : Znth (epsilon (inhabits 0%Z) (BlockWitness x))
          starts 0 <= xe).
      {
        eapply interior_block_start_before_endpoint__certificate_bootstrap.
        - exact (proj1 (Hblocks _ Hqx)).
        - exact (proj1 Hwx6).
      }
      assert (Hbye : Znth (epsilon (inhabits 0%Z) (BlockWitness y))
          starts 0 <= ye).
      { eapply interior_block_start_before_endpoint__certificate_bootstrap.
        - exact (proj1 (Hblocks _ Hqy)).
        - exact (proj1 Hwy6). }
      assert (Hsame_start :
        Znth (epsilon (inhabits 0%Z) (BlockWitness x)) starts 0 =
        Znth (epsilon (inhabits 0%Z) (BlockWitness y)) starts 0)
        by now rewrite Heq.
      unfold ClosedRun in Hclosedx, Hclosedy.
      destruct (Z.lt_trichotomy x y) as [Hxy | [Heqxy | Hyx]].
      + exfalso. apply (proj1 (proj2 Hclosedy)).
        apply Hxchosen. split; [lia |].
        eapply Z.le_trans with (m := y); [lia |].
        eapply Z.le_trans; [exact Hylo |].
        rewrite Hsame_start in Hbxe. exact Hbxe.
      + exact Heqxy.
      + exfalso. apply (proj1 (proj2 Hclosedx)).
        apply Hychosen. split; [lia |].
        eapply Z.le_trans with (m := x); [lia |].
        eapply Z.le_trans; [exact Hxlo |].
        rewrite <- Hsame_start in Hbye. exact Hbye.
  }
  change (PairCenterSelection a (Zlength a) Pairish /\
    (forall center, Pairish center -> chosen center) /\
    #(fun start : Z => 1 <= start < Zlength a - 1 /\ ClosedRun start) <=
      #(fun center : Z => 1 <= center < Zlength a - 1 /\ Pairish center) +
      #(fun q : Z => 0 <= q < Zlength lengths /\ FullBlock q)).
  split; [exact Hpairish_selection |]. split.
  - intros center Hcenter. unfold Pairish, ClosedRun in Hcenter.
    destruct Hcenter as [[Hrange [Hnotprev [Hprev
      [endpoint [Hend [Hallchosen Hrest]]]]]] Hvalues].
    apply Hallchosen. lia.
  - rewrite Hpartition. lia.
Qed.
Lemma NoDup_map_on_members__certificate_bootstrap :
  forall {A B : Type} (f : A -> B) xs,
    NoDup xs ->
    (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
    NoDup (map f xs).
Proof.
  intros A B f xs Hnd Hinj.
  induction Hnd as [|x xs Hnotin Hnd IH].
  - constructor.
  - simpl. constructor.
    + rewrite in_map_iff. intros [y [Heq Hy]].
      assert (Hyx : y = x).
      { apply (Hinj y x); simpl; auto. }
      subst y. contradiction.
    + apply IH. intros y z Hy Hz Heq.
      apply Hinj; simpl; auto.
Qed.
Lemma fully_chosen_canonical_blocks_cost__certificate_bootstrap :
  forall a lengths (chosen : Z -> Prop) starts,
    Zlength starts = Zlength lengths ->
    mono_inc starts ->
    (forall q, 0 <= q < Zlength lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q lengths 0) /\
      Znth q starts 0 + Znth q lengths 0 <= Zlength a) ->
    exists qs,
      NoDup qs /\
      (forall q, In q qs <->
        0 <= q < Zlength lengths /\
        forall j,
          Znth q starts 0 <= j < Znth q starts 0 + Znth q lengths 0 ->
          chosen j) /\
      ListLib.sum (map (fun q => Znth q lengths 0) qs) <=
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i).
Proof.
  intros a lengths chosen starts Hstarts_len Hstarts_inc Hblocks.
  set (Full := fun q : Z =>
    forall j, Znth q starts 0 <= j < Znth q starts 0 +
      Znth q lengths 0 -> chosen j).
  pose (FQ := @Finite_subset Z
    (fun q => 0 <= q < Zlength lengths) Full
    (finite_Z_range 0 (Zlength lengths))).
  set (Q := fun q : Z => 0 <= q < Zlength lengths /\ Full q).
  set (qs := @enum Z Q FQ).
  exists qs. split.
  - unfold qs. apply enum_nodup.
  - split.
    + intros q. unfold qs, Q.
      rewrite <- (@enum_ok Z
        (fun q => 0 <= q < Zlength lengths /\ Full q) FQ q).
      reflexivity.
    + set (pack := fun q : Z =>
        (Znth q lengths 0, Znth q starts 0)).
      set (ordered := map pack qs).
      assert (Hqs_nodup : NoDup qs) by (unfold qs; apply enum_nodup).
      assert (Hqs_range : forall q, In q qs ->
        0 <= q < Zlength lengths).
      {
        intros q Hq. unfold qs, Q in Hq.
        rewrite <- enum_ok in Hq. exact (proj1 Hq).
      }
      assert (Hpack_inj : forall q r, In q qs -> In r qs ->
        pack q = pack r -> q = r).
      {
        intros q r Hq Hr Heq.
        destruct (Z.lt_trichotomy q r) as [Hlt | [He | Hgt]];
          [|exact He|].
        - assert (Hstartlt : Znth q starts 0 < Znth r starts 0)
            by (apply Hstarts_inc; pose proof (Hqs_range q Hq);
                pose proof (Hqs_range r Hr); lia).
          unfold pack in Heq. apply (f_equal snd) in Heq. cbn in Heq. lia.
        - assert (Hstartlt : Znth r starts 0 < Znth q starts 0)
            by (apply Hstarts_inc; pose proof (Hqs_range q Hq);
                pose proof (Hqs_range r Hr); lia).
          unfold pack in Heq. apply (f_equal snd) in Heq. cbn in Heq. lia.
      }
      assert (Hordered_nodup : NoDup ordered).
      { unfold ordered. apply NoDup_map_on_members__certificate_bootstrap;
          assumption. }
      assert (Hordered_len : Zlength ordered = Zlength qs).
      { unfold ordered. apply Zlength_map__certificate_bootstrap. }
      assert (Hordered_startinj : forall q r,
        0 <= q < Zlength ordered -> 0 <= r < Zlength ordered ->
        snd (Znth q ordered (0, 0)) =
        snd (Znth r ordered (0, 0)) -> q = r).
      {
        intros q r Hq Hr Heq.
        unfold ordered in Heq.
        rewrite !Znth_map__certificate_bootstrap with (da := 0%Z) in Heq
          by (rewrite Hordered_len in *; assumption).
        unfold pack in Heq. cbn in Heq.
        change (Znth (Znth q qs 0) starts 0 =
          Znth (Znth r qs 0) starts 0) in Heq.
        assert (Hq_qs : 0 <= q < Zlength qs) by
          (rewrite <- Hordered_len; exact Hq).
        assert (Hr_qs : 0 <= r < Zlength qs) by
          (rewrite <- Hordered_len; exact Hr).
        pose proof (Hqs_range _
          (Znth_In_range__certificate_bootstrap 0 qs q Hq_qs)) as Hqval.
        pose proof (Hqs_range _
          (Znth_In_range__certificate_bootstrap 0 qs r Hr_qs)) as Hrval.
        assert (Hqrval : Znth q qs 0 = Znth r qs 0).
        {
          destruct (Z.lt_trichotomy (Znth q qs 0) (Znth r qs 0))
            as [Hlt | [He | Hgt]]; [|exact He|].
          - exfalso. pose proof (Hstarts_inc _ _ (proj1 Hqval) Hlt
              ltac:(rewrite Hstarts_len; exact (proj2 Hrval))) as Hs.
            rewrite Heq in Hs.
            exact (Z.lt_irrefl _ Hs).
          - exfalso. pose proof (Hstarts_inc _ _ (proj1 Hrval) Hgt
              ltac:(rewrite Hstarts_len; exact (proj2 Hqval))) as Hs.
            rewrite <- Heq in Hs.
            exact (Z.lt_irrefl _ Hs).
        }
        eapply (NoDup_Znth_injective__certificate_bootstrap
          0 qs q r Hqs_nodup); eauto.
      }
      assert (Hordered_blocks : forall r,
        0 <= r < Zlength ordered ->
        InteriorOneBlock a (snd (Znth r ordered (0, 0)))
          (snd (Znth r ordered (0, 0)) +
            fst (Znth r ordered (0, 0)))).
      {
        intros r Hr. unfold ordered.
        rewrite Znth_map__certificate_bootstrap with (da := 0%Z)
          by (rewrite Hordered_len in *; exact Hr).
        unfold pack. cbn.
        assert (Hri : In (Znth r qs 0) qs).
        { apply Znth_In_range__certificate_bootstrap.
          rewrite <- Hordered_len. exact Hr. }
        exact (proj1 (Hblocks _ (Hqs_range _ Hri))).
      }
      assert (Hcost :
        #(fun i : Z => 0 <= i < Zlength a /\
          exists r, 0 <= r < Zlength ordered /\
            snd (Znth r ordered (0, 0)) <= i <
            snd (Znth r ordered (0, 0)) +
              fst (Znth r ordered (0, 0))) =
        ListLib.sum (map fst ordered)).
      {
        apply indexed_block_vertex_union_cardinality__certificate_bootstrap
          with (high := Zlength a); try assumption.
        intros r Hr. pose proof (Hordered_blocks r Hr) as Hb.
        unfold InteriorOneBlock in Hb. lia.
      }
      assert (Hsum : ListLib.sum (map fst ordered) =
        ListLib.sum (map (fun q => Znth q lengths 0) qs)).
      { unfold ordered, pack. rewrite map_map. reflexivity. }
      rewrite <- Hsum, <- Hcost.
      eapply set_card_injection_le__pair_scan_exits with (f := fun i => i).
      * intros i [Hi [r [Hr Hir]]]. split; [exact Hi |].
        assert (Hrqs : 0 <= r < Zlength qs) by
          (rewrite <- Hordered_len; exact Hr).
        unfold ordered in Hir.
        rewrite !Znth_map__certificate_bootstrap with (da := 0%Z) in Hir
          by exact Hrqs.
        unfold pack in Hir. cbn in Hir.
        assert (Hqin : In (Znth r qs 0) qs) by
          (apply Znth_In_range__certificate_bootstrap; exact Hrqs).
        unfold qs, Q in Hqin. rewrite <- enum_ok in Hqin.
        apply (proj2 Hqin). exact Hir.
      * intros x y Hx Hy Heq. exact Heq.
Qed.
Lemma sum_firstn_shift_nondec__certificate_bootstrap :
  forall x xs m, mono_nondec (x :: xs) -> (m <= length xs)%nat ->
    ListLib.sum (firstn m (x :: xs)) <= ListLib.sum (firstn m xs).
Proof.
  intros x xs m. revert x xs.
  induction m as [|m IH]; intros x xs Hmono Hm; simpl; [lia |].
  destruct xs as [|y ys]; simpl in Hm; [lia |].
  rewrite mono_nondec_cons in Hmono. destruct Hmono as [Hxy Htail].
  inversion Hxy as [|? ? Hxley Hrest]; subst.
  simpl. pose proof (IH y ys Htail ltac:(lia)). lia.
Qed.
Lemma nodup_Z_indices_length_bound__certificate_bootstrap :
  forall qs n, 0 <= n -> NoDup qs ->
    (forall q, In q qs -> 0 <= q < n) -> Zlength qs <= n.
Proof.
  intros qs n Hn Hnd Hrange.
  rewrite <- (set_card_list_membership__certificate_bootstrap qs 0 n Hnd Hrange).
  transitivity (#(fun q : Z => 0 <= q < n)).
  - eapply set_card_injection_le__pair_scan_exits with (f := fun q => q).
    + intros q [Hq _]. exact Hq.
    + intros; assumption.
  - rewrite set_card_Z_range__pair_scan_exits by exact Hn. lia.
Qed.
Lemma sum_permutation__certificate_bootstrap :
  forall xs ys : list Z, Permutation xs ys -> ListLib.sum xs = ListLib.sum ys.
Proof. intros xs ys Hperm. induction Hperm; simpl; lia. Qed.
Lemma selected_tail_values__certificate_bootstrap :
  forall x xs qs, (forall q, In q qs -> 1 <= q) ->
    map (fun q => Znth q (x :: xs) 0) qs =
    map (fun q => Znth q xs 0) (map (fun q => q - 1) qs).
Proof.
  intros x xs qs Hpositive. rewrite map_map.
  apply map_ext_in. intros q Hq. simpl.
  pose proof (Hpositive q Hq).
  rewrite Znth_cons by lia. reflexivity.
Qed.
Lemma sublist_cons_positive__certificate_bootstrap :
  forall (x : Z) (xs : list Z) (m : Z), 1 <= m ->
    sublist 0 m (x :: xs) = x :: sublist 0 (m - 1) xs.
Proof.
  intros x xs m Hm. unfold sublist. simpl.
  replace m with (Z.succ (m - 1)) at 1 by lia.
  rewrite Z2Nat.inj_succ by lia. reflexivity.
Qed.
Lemma sorted_prefix_below_selected_indices__certificate_bootstrap :
  forall sorted qs, ListLib.increasing sorted -> NoDup qs ->
    (forall q, In q qs -> 0 <= q < Zlength sorted) ->
    ListLib.sum (sublist 0 (Zlength qs) sorted) <=
    ListLib.sum (map (fun q => Znth q sorted 0) qs).
Proof.
  induction sorted as [|x xs IH]; intros qs Hinc Hnd Hrange.
  - assert (qs = nil).
    { destruct qs as [|q qs]; [reflexivity |]. exfalso.
      pose proof (Hrange q ltac:(simpl; auto)). rewrite Zlength_nil in H. lia. }
    subst qs. reflexivity.
  - assert (Htail_inc : ListLib.increasing xs).
    { apply mono_nondec_iff_increasing. apply mono_nondec_iff_increasing in Hinc.
      rewrite mono_nondec_cons in Hinc. exact (proj2 Hinc). }
    destruct (in_dec Z.eq_dec 0 qs) as [Hzero | Hzero].
    + apply in_split in Hzero. destruct Hzero as [left [right Hqs]].
      set (rest := left ++ right).
      assert (Hperm : Permutation qs (0 :: rest)).
      { subst qs. unfold rest. apply Permutation_sym. apply Permutation_middle. }
      assert (Hrest_nd : NoDup rest).
      { pose proof (Permutation_NoDup Hperm Hnd) as Hnd'.
        inversion Hnd'; assumption. }
      assert (Hrest_nonzero : ~ In 0 rest).
      { pose proof (Permutation_NoDup Hperm Hnd) as Hnd'.
        inversion Hnd'; assumption. }
      set (tail_qs := map (fun q => q - 1) rest).
      assert (Htail_nd : NoDup tail_qs).
      { unfold tail_qs. apply FinFun.Injective_map_NoDup.
        - intros q r Heq. lia. - exact Hrest_nd. }
      assert (Hrest_range : forall q, In q rest ->
        1 <= q < Zlength (x :: xs)).
      { intros q Hq. assert (Hin : In q qs).
        { eapply Permutation_in.
          - exact (Permutation_sym Hperm).
          - simpl. auto. }
        pose proof (Hrange q Hin) as Hqr. split; [|lia].
        destruct (Z.eq_dec q 0); [subst; contradiction | lia]. }
      assert (Htail_range : forall q, In q tail_qs -> 0 <= q < Zlength xs).
      { intros q Hq. unfold tail_qs in Hq. rewrite in_map_iff in Hq.
        destruct Hq as [r [Hr Hrin]]. subst q.
        pose proof (Hrest_range r Hrin). rewrite Zlength_cons in H. lia. }
      pose proof (IH tail_qs Htail_inc Htail_nd Htail_range) as HIH.
      assert (Hlen : Zlength qs = 1 + Zlength tail_qs).
      { assert (Hpz : Zlength qs = Zlength (0 :: rest)).
        { rewrite !Zlength_correct.
          exact (f_equal Z.of_nat (Permutation_length Hperm)). }
        rewrite Hpz, Zlength_cons.
        unfold tail_qs. rewrite Zlength_map__certificate_bootstrap. lia. }
      pose proof (Zlength_nonneg tail_qs) as Htail_len_nonneg.
      rewrite Hlen.
      rewrite sublist_cons_positive__certificate_bootstrap by lia.
      replace (1 + Zlength tail_qs - 1)
        with (Zlength tail_qs) by ring. simpl.
      assert (Hvalues : ListLib.sum (map (fun q => Znth q (x :: xs) 0) qs) =
        x + ListLib.sum (map (fun q => Znth q xs 0) tail_qs)).
      { rewrite (sum_permutation__certificate_bootstrap _ _
          (Permutation_map (fun q => Znth q (x :: xs) 0) Hperm)).
        simpl. unfold tail_qs.
        rewrite <- (selected_tail_values__certificate_bootstrap x xs rest).
        - reflexivity. - intros q Hq. exact (proj1 (Hrest_range q Hq)). }
      rewrite Hvalues.
      exact ((proj1 (Z.add_le_mono_l _ _ x)) HIH).
    + set (tail_qs := map (fun q => q - 1) qs).
      assert (Hpositive : forall q, In q qs -> 1 <= q).
      { intros q Hq. pose proof (Hrange q Hq).
        destruct (Z.eq_dec q 0); [subst; contradiction | lia]. }
      assert (Htail_nd : NoDup tail_qs).
      { unfold tail_qs. apply FinFun.Injective_map_NoDup.
        - intros q r Heq. lia. - exact Hnd. }
      assert (Htail_range : forall q, In q tail_qs -> 0 <= q < Zlength xs).
      { intros q Hq. unfold tail_qs in Hq. rewrite in_map_iff in Hq.
        destruct Hq as [r [Hr Hrin]]. subst q.
        pose proof (Hrange r Hrin) as Hrng.
        pose proof (Hpositive r Hrin) as Hrpos.
        rewrite Zlength_cons in Hrng. lia. }
      pose proof (IH tail_qs Htail_inc Htail_nd Htail_range) as HIH.
      assert (Hlen : Zlength tail_qs = Zlength qs).
      { unfold tail_qs. apply Zlength_map__certificate_bootstrap. }
      assert (Hbound : Zlength qs <= Zlength xs).
      { rewrite <- Hlen.
        apply nodup_Z_indices_length_bound__certificate_bootstrap.
        - apply Zlength_nonneg.
        - exact Htail_nd.
        - exact Htail_range. }
      rewrite (selected_tail_values__certificate_bootstrap x xs qs Hpositive).
      rewrite Hlen in HIH. eapply Z.le_trans; [|exact HIH].
      rewrite !sublist_zero_as_firstn__certificate_bootstrap.
      apply sum_firstn_shift_nondec__certificate_bootstrap.
      * apply mono_nondec_iff_increasing. exact Hinc.
      * assert (Hxs : Z.to_nat (Zlength xs) = length xs).
        { rewrite Zlength_correct, Nat2Z.id. reflexivity. }
        rewrite <- Hxs.
        apply (proj1 (Z2Nat.inj_le (Zlength qs) (Zlength xs)
          (Zlength_nonneg qs) (Zlength_nonneg xs))).
        exact Hbound.
Qed.
Lemma pair_centers_and_full_blocks_cost__certificate_bootstrap :
  forall a lengths (chosen centres : Z -> Prop) starts,
    Zlength starts = Zlength lengths ->
    mono_inc starts ->
    (forall q, 0 <= q < Zlength lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q lengths 0) /\
      Znth q starts 0 + Znth q lengths 0 <= Zlength a) ->
    PairCenterSelection a (Zlength a) centres ->
    (forall center, centres center -> chosen center) ->
    exists qs,
      NoDup qs /\
      (forall q, In q qs <->
        0 <= q < Zlength lengths /\
        forall j,
          Znth q starts 0 <= j < Znth q starts 0 + Znth q lengths 0 ->
          chosen j) /\
      Zlength qs = #(fun q : Z =>
        0 <= q < Zlength lengths /\
        forall j,
          Znth q starts 0 <= j < Znth q starts 0 + Znth q lengths 0 ->
          chosen j) /\
      #(fun center : Z =>
          1 <= center < Zlength a - 1 /\ centres center) +
        ListLib.sum (map (fun q => Znth q lengths 0) qs) <=
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i).
Proof.
  intros a lengths chosen centres starts Hlen Hmono Hblocks Hcentres Hchosen.
  set (chosen_rest := fun i : Z => chosen i /\ ~ centres i).
  destruct (fully_chosen_canonical_blocks_cost__certificate_bootstrap
    a lengths chosen_rest starts Hlen Hmono Hblocks) as
    [qs [Hqsnd [Hqsmem Hqscost]]].
  assert (Hqsmem_full : forall q, In q qs <->
    0 <= q < Zlength lengths /\
    forall j,
      Znth q starts 0 <= j < Znth q starts 0 + Znth q lengths 0 ->
      chosen j).
  {
    intros q. split.
    - intros Hqin. apply (proj1 (Hqsmem q)) in Hqin.
      split; [exact (proj1 Hqin) |].
      intros j Hj. exact (proj1 ((proj2 Hqin) j Hj)).
    - intros [Hq Hfull]. apply (proj2 (Hqsmem q)). split; [exact Hq |].
      intros j Hj. split; [apply Hfull; exact Hj |].
      intro Hcj.
      pose proof (canonical_profile_pair_block_disjoint__certificate_bootstrap
        a lengths starts centres Hlen
        (fun r Hr => proj1 (Hblocks r Hr)) Hcentres j q Hcj Hq) as Hd.
      destruct Hd; lia.
  }
  exists qs. split; [exact Hqsnd |].
  split; [exact Hqsmem_full |]. split.
  - rewrite <- (set_card_list_membership__certificate_bootstrap
      qs 0 (Zlength lengths) Hqsnd).
    + apply set_card_iff__exam_bridge. intros q. split.
      * intros [Hq Hqin]. exact (proj1 (Hqsmem_full q) Hqin).
      * intros Hq. split; [exact (proj1 Hq) |].
        exact (proj2 (Hqsmem_full q) Hq).
    + intros q Hqin. exact (proj1 (proj1 (Hqsmem_full q) Hqin)).
  - pose proof (set_card_partition_subset_Z__certificate_bootstrap
      0 (Zlength a) chosen centres) as Hpartition.
    specialize (Hpartition ltac:(intros i Hi; apply Hchosen; exact Hi)).
    assert (Hcentres_card :
      #(fun i : Z => 0 <= i < Zlength a /\ centres i) =
      #(fun center : Z =>
        1 <= center < Zlength a - 1 /\ centres center)).
    {
      apply set_card_iff__exam_bridge. intros i. split.
      - intros [_ Hi]. pose proof (proj1 Hcentres i Hi) as Hvalid.
        unfold NonOnePairCenter in Hvalid. tauto.
      - intros [Hi Hc]. split; [lia | exact Hc].
    }
    assert (Hrest_card :
      #(fun i : Z => 0 <= i < Zlength a /\ chosen_rest i) =
      #(fun i : Z => 0 <= i < Zlength a /\ chosen i /\ ~ centres i)).
    { apply set_card_iff__exam_bridge. intros i. unfold chosen_rest. tauto. }
    rewrite Hpartition, Hcentres_card, <- Hrest_card. lia.
Qed.
Lemma combine_aligned_member_active__certificate_bootstrap :
  forall lengths starts q,
    Zlength starts = Zlength lengths ->
    0 <= q < Zlength lengths ->
    In (Znth q lengths 0, Znth q starts 0) (combine lengths starts).
Proof.
  induction lengths as [|x lengths IH]; intros starts q Hlen Hq.
  - rewrite Zlength_nil in Hq. lia.
  - destruct starts as [|y starts].
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg lengths). lia.
    + rewrite !Zlength_cons in Hlen.
      rewrite Zlength_cons in Hq.
      destruct (Z.eq_dec q 0) as [-> | Hq0].
      * rewrite !Znth0_cons. simpl. auto.
      * assert (Hqpos : 0 < q) by lia.
        rewrite !Znth_cons by lia. simpl. right.
        apply IH.
        -- lia.
        -- pose proof (Zlength_nonneg lengths). lia.
Qed.
Lemma In_Znth_index_active__certificate_bootstrap :
  forall {A : Type} (xs : list A) x d,
    In x xs -> exists i, 0 <= i < Zlength xs /\ Znth i xs d = x.
Proof.
  intros A xs. induction xs as [|y ys IH]; intros x d Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + exists 0. rewrite Znth0_cons, Zlength_cons.
      split; [pose proof (Zlength_nonneg ys); lia | reflexivity].
    + destruct (IH x d Hin) as [i [Hi Heq]].
      exists (i + 1). rewrite Znth_cons, Zlength_cons by lia.
      replace (i + 1 - 1) with i by lia. split; [lia | exact Heq].
Qed.
Lemma selected_indices_align_under_permutation_active__certificate_bootstrap :
  forall lengths starts sorted qs,
    Zlength starts = Zlength lengths ->
    mono_inc starts ->
    Permutation lengths sorted ->
    NoDup qs ->
    (forall q, In q qs -> 0 <= q < Zlength lengths) ->
    exists rs,
      NoDup rs /\
      (forall r, In r rs -> 0 <= r < Zlength sorted) /\
      Zlength rs = Zlength qs /\
      map (fun r => Znth r sorted 0) rs =
        map (fun q => Znth q lengths 0) qs.
Proof.
  intros lengths starts sorted qs Hlen Hstarts Hperm Hqsnd Hqsrange.
  destruct (lift_length_permutation_to_blocks__certificate_bootstrap
    lengths starts sorted Hlen Hperm) as [ordered [Hordered Hmap]].
  assert (Hordered_len : Zlength ordered = Zlength sorted).
  { rewrite <- Hmap. symmetry. apply Zlength_map__certificate_bootstrap. }
  set (Match := fun q r : Z =>
    0 <= r < Zlength ordered /\
    Znth r ordered (0, 0) = (Znth q lengths 0, Znth q starts 0)).
  assert (Hmatch : forall q, 0 <= q < Zlength lengths ->
    exists r, Match q r).
  {
    intros q Hq.
    assert (Hinsource : In (Znth q lengths 0, Znth q starts 0)
      (combine lengths starts)).
    { apply combine_aligned_member_active__certificate_bootstrap; assumption. }
    assert (Hinordered : In (Znth q lengths 0, Znth q starts 0) ordered).
    { eapply Permutation_in; [exact Hordered | exact Hinsource]. }
    destruct (In_Znth_index_active__certificate_bootstrap
      ordered (Znth q lengths 0, Znth q starts 0) (0, 0) Hinordered)
      as [r [Hr Hval]].
    exists r. unfold Match. split; assumption.
  }
  set (position := fun q : Z =>
    epsilon (inhabits 0%Z) (Match q)).
  assert (Hposition : forall q, 0 <= q < Zlength lengths ->
    Match q (position q)).
  { intros q Hq. unfold position. apply epsilon_spec. apply Hmatch. exact Hq. }
  set (rs := map position qs).
  exists rs. split.
  - unfold rs. apply NoDup_map_on_members__certificate_bootstrap.
    + exact Hqsnd.
    + intros q r Hqin Hrin Heq.
      pose proof (Hposition q (Hqsrange q Hqin)) as Hpq.
      pose proof (Hposition r (Hqsrange r Hrin)) as Hpr.
      unfold Match in Hpq, Hpr. destruct Hpq as [Hpqrange Hpqe].
      destruct Hpr as [Hprrange Hpre]. rewrite Heq in Hpqe.
      rewrite Hpre in Hpqe. inversion Hpqe.
      destruct (Z.lt_trichotomy q r) as [Hlt | [Heqr | Hgt]];
        [|exact Heqr|].
      * pose proof (Hstarts q r (proj1 (Hqsrange q Hqin)) Hlt
          ltac:(rewrite Hlen; exact (proj2 (Hqsrange r Hrin)))) as Hs. lia.
      * pose proof (Hstarts r q (proj1 (Hqsrange r Hrin)) Hgt
          ltac:(rewrite Hlen; exact (proj2 (Hqsrange q Hqin)))) as Hs. lia.
  - split.
    + intros r Hrin. unfold rs in Hrin. rewrite in_map_iff in Hrin.
    destruct Hrin as [q [Heq Hqin]]. subst r.
    pose proof (Hposition q (Hqsrange q Hqin)) as Hp.
    unfold Match in Hp. rewrite <- Hordered_len. exact (proj1 Hp).
    + split.
      * unfold rs. apply Zlength_map__certificate_bootstrap.
      * unfold rs. rewrite map_map. apply map_ext_in. intros q Hqin.
    pose proof (Hposition q (Hqsrange q Hqin)) as Hp.
    unfold Match in Hp. destruct Hp as [Hprange Hpe].
    assert (Hsorted_range : 0 <= position q < Zlength sorted)
      by (rewrite <- Hordered_len; exact Hprange).
    rewrite <- Hmap.
    rewrite Znth_map__certificate_bootstrap with (da := (0, 0))
      by (rewrite Hordered_len; exact Hsorted_range).
    rewrite Hpe. reflexivity.
Qed.
Lemma sum_lowerbound_times_length__certificate_bootstrap :
  forall c xs,
    ListLib.lowerbound c xs -> Zlength xs * c <= ListLib.sum xs.
Proof.
  intros c xs. induction xs as [|x xs IH]; intros Hlower.
  - rewrite Zlength_nil. simpl. lia.
  - simpl in Hlower. destruct Hlower as [Hcx Htail].
    rewrite Zlength_cons. simpl. specialize (IH Htail). nia.
Qed.
Lemma increasing_prefix_growth_lower__certificate_bootstrap :
  forall sorted lo hi,
    ListLib.increasing sorted ->
    0 <= lo <= hi -> hi <= Zlength sorted ->
    ListLib.sum (sublist 0 lo sorted) +
      (hi - lo) * Znth lo sorted 0 <=
    ListLib.sum (sublist 0 hi sorted).
Proof.
  intros sorted lo hi Hinc Hlohi Hhi.
  rewrite (sublist_split 0 hi lo sorted) by lia.
  rewrite ListLib.sum_app.
  assert (Hlower : ListLib.lowerbound (Znth lo sorted 0)
    (sublist lo hi sorted)).
  {
    apply ListLib.lowerbound_sublist_intro; try lia.
    intros i Hi.
    pose proof (proj2 (mono_nondec_iff_increasing sorted) Hinc) as Hmono.
    apply Hmono; lia.
  }
  pose proof (sum_lowerbound_times_length__certificate_bootstrap
    (Znth lo sorted 0) (sublist lo hi sorted) Hlower) as Hsum.
  rewrite Zlength_sublist in Hsum by lia. lia.
Qed.
Lemma stopped_greedy_pair_block_exchange__certificate_bootstrap :
  forall sorted original_k use next remaining initial_sad sadness p rs,
    ListLib.increasing sorted ->
    Forall (fun len : Z => 1 <= len) sorted ->
    0 <= use <= original_k ->
    GreedyBlockState sorted next (original_k - use)
      initial_sad remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    0 <= p <= use ->
    NoDup rs ->
    (forall r, In r rs -> 0 <= r < Zlength sorted) ->
    p + ListLib.sum (map (fun r => Znth r sorted 0) rs) <= original_k ->
    p + Zlength rs <= use + next.
Proof.
  intros sorted original_k use next remaining initial_sad sadness p rs
    Hinc Hpositive Huse Hgreedy Hstop Hp Hrsnd Hrsrange Hcost.
  destruct Hgreedy as [Hnext [Hremaining [Hsadness Hfit]]].
  assert (Hrslen : Zlength rs <= Zlength sorted).
  { apply nodup_Z_indices_length_bound__certificate_bootstrap;
      [apply Zlength_nonneg | exact Hrsnd | exact Hrsrange]. }
  destruct (Z.eq_dec next (Zlength sorted)) as [Hdone | Hnotdone].
  - lia.
  - assert (Hnextlt : next < Zlength sorted) by lia.
    assert (Hremaining_nonneg : 0 <= remaining).
    {
      destruct (Z.eq_dec next 0) as [-> | Hnext0].
      - unfold sublist in Hremaining. simpl in Hremaining. lia.
      - specialize (Hfit (next - 1) ltac:(lia)).
        pose proof (sum_sublist_succ__certificate_bootstrap
          sorted (next - 1) ltac:(lia)) as Hsumstep.
        replace (next - 1 + 1) with next in Hsumstep by lia. lia.
    }
    assert (Hstopvalue : Znth next sorted 0 > remaining) by tauto.
    destruct (Z_le_gt_dec (p + Zlength rs) (use + next)) as [Hok | Hbad];
      [exact Hok |].
    assert (HnextB : next < Zlength rs) by lia.
    pose proof (sorted_prefix_below_selected_indices__certificate_bootstrap
      sorted rs Hinc Hrsnd Hrsrange) as Hprefix_selected.
    pose proof (increasing_prefix_growth_lower__certificate_bootstrap
      sorted next (Zlength rs) Hinc ltac:(lia) ltac:(lia)) as Hgrowth.
    assert (Hnextpositive : 1 <= Znth next sorted 0).
    {
      rewrite Forall_forall in Hpositive.
      apply Hpositive.
      apply Znth_In_range__certificate_bootstrap. lia.
    }
    nia.
Qed.
Lemma canonical_stopped_greedy_competitor_lower_bound__certificate_bootstrap :
  forall a base_sad pair_savings lengths original_k sorted use next
      remaining sadness out,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    CanonicalInteriorOneRunPrefix a (Zlength a) lengths ->
    1 <= original_k <= Zlength a ->
    Permutation lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    forall other other_sadness,
      SimplifiedExams a original_k other ->
      ExamSadness other other_sadness ->
      out <= other_sadness.
Proof.
  intros a base_sad pair_savings lengths original_k sorted use next
    remaining sadness out Hnonneg Hbase Hpair Hcanonical Hk Hperm Hinc
    Huse Hgreedy Hstop Hfinal other other_sadness Hother Hother_sad.
  pose proof (stopped_greedy_final_formula__certificate_bootstrap
    sorted next original_k use base_sad remaining sadness out
    Hgreedy Hfinal) as Hout.
  destruct (simplified_exam_exposes_choice_sadness__certificate_bootstrap
    a original_k other other_sadness Hother Hother_sad) as
    [chosen [Hchosen_range [Hchosen_card Hchoice_sad]]].
  pose proof (choice_sadness_is_base_minus_removed__certificate_bootstrap
    a chosen base_sad other_sadness Hnonneg Hbase Hchoice_sad) as Hpartition.
  assert (Hother_nonneg : 0 <= other_sadness).
  {
    unfold ExamSadness in Hother_sad. rewrite Hother_sad.
    apply set_card_nonnegative__pair_scan_exits.
  }
  unfold MinValue in Huse.
  destruct (Z_le_gt_dec original_k pair_savings) as [Hkle | Hpairlt].
  - rewrite Z.min_l in Huse by lia. subst use.
    pose proof (simplified_exam_coarse_lower_bound__certificate_bootstrap
      a original_k base_sad other other_sadness Hnonneg Hbase Hother
      Hother_sad) as Hcoarse.
    assert (Hnext_nonneg : 0 <= next) by
      (pose proof (proj1 Hgreedy); lia).
    rewrite Hout. apply Z.max_lub; nia.
  - rewrite Z.min_r in Huse by lia. subst use.
    set (Removed := fun edge : Z =>
      Z.gcd (Znth edge a 0) (Znth (edge + 1) a 0) = 1 /\
      Z.gcd
        (if prop_dec (chosen edge) then 0 else Znth edge a 0)
        (if prop_dec (chosen (edge + 1)) then 0
         else Znth (edge + 1) a 0) <> 1).
    set (ClosedRun := fun start : Z =>
      1 <= start < Zlength a - 1 /\
      ~ chosen (start - 1) /\ Removed (start - 1) /\
      exists endpoint,
        start <= endpoint < Zlength a - 1 /\
        (forall j, start <= j <= endpoint -> chosen j) /\
        (forall edge, start <= edge < endpoint -> Removed edge) /\
        ~ chosen (endpoint + 1) /\ Removed endpoint).
    set (Pairish := fun start : Z =>
      ClosedRun start /\ Znth start a 0 <> 1 /\
      Znth (start + 1) a 0 <> 1).
    fold Removed in Hpartition.
    pose proof (removed_edges_at_most_choices_plus_closed_runs__certificate_bootstrap
      a chosen) as Hremoved_runs.
    cbn zeta in Hremoved_runs. fold Removed ClosedRun in Hremoved_runs.
    pose proof (closed_run_bonus_bound_by_pairs_and_full_blocks__certificate_bootstrap
      a chosen pair_savings lengths Hnonneg Hpair Hcanonical) as Hbonus.
    cbn zeta in Hbonus. fold Removed ClosedRun Pairish in Hbonus.
    destruct Hbonus as [starts [Hstarts_len [Hstarts_inc [Hstarts_blocks
      [Hpairish_selection [Hpairish_chosen Hclosed_bound]]]]]].
    destruct (pair_centers_and_full_blocks_cost__certificate_bootstrap
      a lengths chosen Pairish starts Hstarts_len Hstarts_inc Hstarts_blocks
      Hpairish_selection Hpairish_chosen) as
      [qs [Hqsnd [Hqsmem [Hqslen Hpair_block_cost]]]].
    destruct (selected_indices_align_under_permutation_active__certificate_bootstrap
      lengths starts sorted qs Hstarts_len Hstarts_inc Hperm Hqsnd
      ltac:(intros q Hq; exact (proj1 ((proj1 (Hqsmem q)) Hq)))) as
      [rs [Hrsnd [Hrsrange [Hrslen Hrsvalues]]]].
    assert (Hsorted_positive : Forall (fun len : Z => 1 <= len) sorted).
    {
      eapply Permutation_Forall; [exact Hperm |].
      rewrite Forall_forall. intros len Hlenin.
      destruct (In_Znth_index_active__certificate_bootstrap
        lengths len 0 Hlenin) as [q [Hq Hqval]].
      pose proof (Hstarts_blocks q Hq) as Hb.
      unfold InteriorOneBlock in Hb. rewrite Hqval in Hb. lia.
    }
    set (p := #(fun center : Z =>
      1 <= center < Zlength a - 1 /\ Pairish center)).
    assert (Hp : 0 <= p <= pair_savings).
    {
      split; [unfold p; apply set_card_nonnegative__pair_scan_exits |].
      unfold p. apply pair_savings_bounds_every_selection__certificate_bootstrap;
        assumption.
    }
    assert (Hexchange : p + Zlength rs <= pair_savings + next).
    {
      apply (stopped_greedy_pair_block_exchange__certificate_bootstrap
        sorted original_k pair_savings next remaining
        (base_sad - 2 * pair_savings) sadness p rs); try assumption.
      - lia.
      - unfold p in *. rewrite Hrsvalues. nia.
    }
    rewrite Hout. apply Z.max_lub; [exact Hother_nonneg |].
    rewrite <- Hqslen in Hclosed_bound.
    rewrite <- Hrslen in Hclosed_bound.
    fold p in Hclosed_bound.
    assert (Hremoved_numeric :
      #(fun edge : Z => 0 <= edge < Zlength a - 1 /\ Removed edge) <=
        original_k + p + Zlength rs) by nia.
    assert (Hremoved_total :
      #(fun edge : Z => 0 <= edge < Zlength a - 1 /\ Removed edge) <=
        original_k + pair_savings + next) by nia.
    assert (Hpartition_numeric :
      base_sad = other_sadness +
        #(fun edge : Z => 0 <= edge < Zlength a - 1 /\ Removed edge))
      by exact Hpartition.
    lia.
Qed.
Lemma canonical_profile_yields_joint_certificate__certificate_bootstrap :
  forall a base_sad pair_savings lengths,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    (exists j, 0 <= j < Zlength a /\ Znth j a 0 <> 1) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    CanonicalInteriorOneRunPrefix a (Zlength a) lengths ->
    ExamJointOptimizationCertificate a base_sad pair_savings lengths.
Proof.
  intros a base_sad pair_savings lengths Hnonneg Hnonone Hbase Hpair
    Hcanonical.
  assert (Hlength : 1 <= Zlength a).
  { destruct Hnonone as [j [Hj _]]. lia. }
  split.
  - apply canonical_profile_yields_joint_prefix__certificate_bootstrap;
      assumption.
  - intros original_k sorted use next remaining sadness out Hk Hperm Hinc
      Huse Hgreedy Hstop Hfinal.
    destruct (canonical_stopped_greedy_upper_bound__certificate_bootstrap
      a base_sad pair_savings lengths original_k sorted use next remaining
      sadness out Hnonneg Hnonone Hbase Hpair Hcanonical Hk Hperm Hinc Huse
      Hgreedy Hfinal) as
      [result [final_sad [Hresult [Hresult_sad Hupper]]]].
    pose proof
      (canonical_stopped_greedy_competitor_lower_bound__certificate_bootstrap
        a base_sad pair_savings lengths original_k sorted use next remaining
        sadness out Hnonneg Hbase Hpair Hcanonical Hk Hperm Hinc Huse
        Hgreedy Hstop Hfinal result final_sad Hresult Hresult_sad) as Hlower.
    assert (Hsame : final_sad = out) by lia.
    subst final_sad.
    exists result. repeat split; try assumption.
    intros other other_sadness Hother Hother_sadness.
    eapply canonical_stopped_greedy_competitor_lower_bound__certificate_bootstrap;
      eauto.
Qed.
Theorem canonical_certificate_nil_from_scans__certificate_bootstrap :
  forall a base_sad pair_savings,
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0) ->
    (exists j, 0 <= j < Zlength a /\ Znth j a 0 <> 1) ->
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    CanonicalExamBlockCollectionCertificate a base_sad pair_savings nil.
Proof.
  intros a base_sad pair_savings Hnonneg Hnonone Hbase Hpair future
    Hcanonical.
  simpl in Hcanonical |- *.
  eapply canonical_profile_yields_joint_certificate__certificate_bootstrap;
    eauto.
Qed.
Lemma fold_ones_length__pair_scan_safety :
  forall {A : Type} (xs : list A),
    List.fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
      Z.of_nat (List.length xs).
Proof.
  intros A xs.
  induction xs as [|x xs IH]; [reflexivity |].
  change (1 + List.fold_right
    (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
    Z.of_nat (S (List.length xs))).
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.
Lemma set_card_as_Zlength__pair_scan_safety :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    @set_card A P FP = Z.of_nat (List.length (@enum A P FP)).
Proof.
  intros A P FP.
  unfold set_card, SumLib.Sum.sum.
  apply fold_ones_length__pair_scan_safety.
Qed.
Lemma set_card_injection_le__pair_scan_safety :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q) (f : A -> B),
    (forall x, P x -> Q (f x)) ->
    (forall x y, P x -> P y -> f x = f y -> x = y) ->
    @set_card A P FP <= @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f Hmaps Hinj.
  rewrite !set_card_as_Zlength__pair_scan_safety.
  assert (Hlen :
    (List.length (map f (@enum A P FP)) <=
     List.length (@enum B Q FQ))%nat).
  {
    apply NoDup_incl_length.
    - assert (Hgeneral : forall xs : list A,
        NoDup xs ->
        (forall x, In x xs -> P x) ->
        NoDup (map f xs)).
      {
        intros xs Hnodup.
        induction Hnodup as [|x xs Hnotin Hnodup IH]; intros Hall; simpl.
        - constructor.
        - constructor.
          + intro Hin.
            apply in_map_iff in Hin.
            destruct Hin as [y [Hfy Hy]].
            apply Hnotin.
            assert (HPx : P x) by (apply Hall; left; reflexivity).
            assert (HPy : P y) by (apply Hall; right; exact Hy).
            assert (Hxy : x = y).
            { apply Hinj; try assumption. symmetry; exact Hfy. }
            rewrite Hxy. exact Hy.
          + apply IH.
            intros y Hy. apply Hall. right. exact Hy.
      }
      apply Hgeneral.
      + exact (@enum_nodup A P FP).
      + intros x Hx.
        apply (proj2 (@enum_ok A P FP x)); exact Hx.
    - intros y Hy.
      apply in_map_iff in Hy.
      destruct Hy as [x [<- Hx]].
      apply (proj1 (@enum_ok B Q FQ (f x))).
      apply Hmaps.
      apply (proj2 (@enum_ok A P FP x)); exact Hx.
  }
  rewrite length_map in Hlen.
  exact (proj1 (Nat2Z.inj_le _ _) Hlen).
Qed.
Lemma Zrange_aux_length__pair_scan_safety :
  forall low m, List.length (Zrange_aux low m) = m.
Proof.
  intros low m.
  revert low.
  induction m; intros; simpl; congruence.
Qed.
Lemma set_card_Z_range__pair_scan_safety :
  forall low high, low <= high ->
    @set_card Z (fun z => low <= z < high) (finite_Z_range low high) =
      high - low.
Proof.
  intros low high Hrange.
  rewrite set_card_as_Zlength__pair_scan_safety.
  change (Z.of_nat (List.length (Zrange low high)) = high - low).
  unfold Zrange.
  rewrite Zrange_aux_length__pair_scan_safety, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma pair_savings_scan_int_bound__pair_scan_safety :
  forall a hi committed pending savings,
    0 <= hi ->
    PairSavingsScan a hi committed pending savings ->
    savings <= hi.
Proof.
  intros a hi committed pending savings Hhi Hscan.
  unfold PairSavingsScan in Hscan.
  destruct Hscan as [Hvalue [Hpending Hprefix]].
  unfold PairSavingsPrefix, max_value_of_subset,
    max_object_of_subset in Hprefix.
  destruct Hprefix as [chosen [[Hselected Hmax] Hsavings]].
  subst savings.
  pose proof
    (@set_card_injection_le__pair_scan_safety
      Z Z
      (fun center : Z => 1 <= center < hi - 1 /\ chosen center)
      (fun index : Z => 0 <= index < hi)
      (finite_Z_range' 1 (hi - 1) chosen)
      (finite_Z_range 0 hi)
      (fun center => center)) as Hcount.
  specialize (Hcount
    ltac:(intros center [[Hlo Hupper] Hchosen]; lia)
    ltac:(intros x y Hx Hy Heq; exact Heq)).
  rewrite (set_card_Z_range__pair_scan_safety 0 hi) in Hcount by lia.
  lia.
Qed.
Lemma set_card_Z_as_sum__coprime_scan :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_interval_empty__coprime_scan :
  forall low high (P : Z -> Prop),
    high <= low ->
    #(fun z : Z => low <= z < high /\ P z) = 0.
Proof.
  intros low high P Hempty.
  rewrite set_card_Z_as_sum__coprime_scan.
  apply SumLib.ZRange.sum_Z_range_empty.
  exact Hempty.
Qed.
Lemma coprime_prefix_count_extend_hit__coprime_scan :
  forall (a : list Z) (hi count : Z),
    0 <= hi ->
    CoprimeEdgePrefixCount a hi count ->
    AdjacentCoprime a hi ->
    CoprimeEdgePrefixCount a (hi + 1) (count + 1).
Proof.
  intros a hi count Hhi Hcount Hedge.
  unfold CoprimeEdgePrefixCount in *.
  rewrite !set_card_Z_as_sum__coprime_scan in *.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by lia.
  destruct (prop_dec (AdjacentCoprime a hi)); [lia | contradiction].
Qed.
Lemma coprime_prefix_count_extend_miss__coprime_scan :
  forall (a : list Z) (hi count : Z),
    0 <= hi ->
    CoprimeEdgePrefixCount a hi count ->
    ~ AdjacentCoprime a hi ->
    CoprimeEdgePrefixCount a (hi + 1) count.
Proof.
  intros a hi count Hhi Hcount Hedge.
  unfold CoprimeEdgePrefixCount in *.
  rewrite !set_card_Z_as_sum__coprime_scan in *.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by lia.
  destruct (prop_dec (AdjacentCoprime a hi)); [contradiction | lia].
Qed.
Lemma pair_savings_prefix_zero__coprime_scan :
  forall a, PairSavingsPrefix a 0 0.
Proof.
  intros a.
  unfold PairSavingsPrefix, max_value_of_subset, max_object_of_subset.
  exists (fun _ : Z => False).
  split.
  - split.
    + unfold PairCenterSelection.
      split; intros; contradiction.
    + intros other Hother.
      rewrite set_card_interval_empty__coprime_scan by lia.
      rewrite set_card_interval_empty__coprime_scan by lia.
      lia.
  - rewrite set_card_interval_empty__coprime_scan by lia.
    reflexivity.
Qed.
Lemma zero_quot_two__pair_scan_transitions : 0 ÷ 2 = 0.
Proof. apply Zquot_0_l. Qed.
Lemma set_card_extensional__pair_scan_transitions :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros x.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
            1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma non_one_pair_center_extend_noncoprime__pair_scan_transitions :
  forall a hi center,
    0 <= hi ->
    ~ AdjacentCoprime a (hi - 1) ->
    (NonOnePairCenter a (hi + 1) center <->
     NonOnePairCenter a hi center).
Proof.
  intros a hi center Hhi Hbreak.
  unfold NonOnePairCenter.
  split.
  - intros H.
    destruct H as [Hrange [Hleft [Hcenter [Hright [Hedge1 Hedge2]]]]].
    split.
    + destruct (Z.eq_dec center (hi - 1)) as [-> | Hneq].
      * contradiction.
      * lia.
    + exact (conj Hleft (conj Hcenter (conj Hright (conj Hedge1 Hedge2)))).
  - intros H.
    destruct H as [Hrange [Hleft [Hcenter [Hright [Hedge1 Hedge2]]]]].
    split; [lia |].
    exact (conj Hleft (conj Hcenter (conj Hright (conj Hedge1 Hedge2)))).
Qed.
Lemma pair_center_selection_extend_noncoprime__pair_scan_transitions :
  forall a hi chosen,
    0 <= hi ->
    ~ AdjacentCoprime a (hi - 1) ->
    (PairCenterSelection a (hi + 1) chosen <->
     PairCenterSelection a hi chosen).
Proof.
  intros a hi chosen Hhi Hbreak.
  unfold PairCenterSelection.
  split; intros [Hvalid Hsep]; split; try exact Hsep;
    intros center Hchosen.
  - apply (proj1
      (non_one_pair_center_extend_noncoprime__pair_scan_transitions
        a hi center Hhi Hbreak)).
    apply Hvalid. exact Hchosen.
  - apply (proj2
      (non_one_pair_center_extend_noncoprime__pair_scan_transitions
        a hi center Hhi Hbreak)).
    apply Hvalid. exact Hchosen.
Qed.
Lemma pair_center_count_extend_noncoprime__pair_scan_transitions :
  forall a hi chosen,
    0 <= hi ->
    ~ AdjacentCoprime a (hi - 1) ->
    (PairCenterSelection a hi chosen \/
     PairCenterSelection a (hi + 1) chosen) ->
    #(fun center : Z => 1 <= center < hi - 1 /\ chosen center) =
    #(fun center : Z => 1 <= center < hi + 1 - 1 /\ chosen center).
Proof.
  intros a hi chosen Hhi Hbreak Hselection.
  eapply set_card_extensional__pair_scan_transitions.
  intros center.
  split.
  - intros [Hrange Hchosen]. split; [lia | exact Hchosen].
  - intros [Hrange Hchosen].
    split; [| exact Hchosen].
    destruct Hselection as [Hselection | Hselection].
    + destruct Hselection as [Hvalid _].
      specialize (Hvalid center Hchosen).
      unfold NonOnePairCenter in Hvalid. tauto.
    + destruct Hselection as [Hvalid _].
      specialize (Hvalid center Hchosen).
      pose proof
        (proj1
          (non_one_pair_center_extend_noncoprime__pair_scan_transitions
            a hi center Hhi Hbreak) Hvalid) as Hold.
      unfold NonOnePairCenter in Hold. tauto.
Qed.
Lemma pair_savings_prefix_extend_noncoprime__pair_scan_transitions :
  forall a hi savings,
    0 <= hi ->
    ~ AdjacentCoprime a (hi - 1) ->
    PairSavingsPrefix a hi savings ->
    PairSavingsPrefix a (hi + 1) savings.
Proof.
  intros a hi savings Hhi Hbreak Hprefix.
  unfold PairSavingsPrefix, max_value_of_subset, max_object_of_subset in *.
  destruct Hprefix as [chosen [[Hselected Hmax] Hvalue]].
  exists chosen.
  split.
  - split.
    + apply (proj2
        (pair_center_selection_extend_noncoprime__pair_scan_transitions
          a hi chosen Hhi Hbreak)).
      exact Hselected.
    + intros other Hother.
      pose proof
        (proj1
          (pair_center_selection_extend_noncoprime__pair_scan_transitions
            a hi other Hhi Hbreak) Hother) as Hother_old.
      specialize (Hmax other Hother_old).
      rewrite <-
        (pair_center_count_extend_noncoprime__pair_scan_transitions
          a hi other Hhi Hbreak (or_intror Hother)).
      rewrite <-
        (pair_center_count_extend_noncoprime__pair_scan_transitions
          a hi chosen Hhi Hbreak (or_introl Hselected)).
      exact Hmax.
  - rewrite <-
      (pair_center_count_extend_noncoprime__pair_scan_transitions
        a hi chosen Hhi Hbreak (or_introl Hselected)).
    exact Hvalue.
Qed.
Lemma pair_run_suffix_extend_coprime_nonone__pair_scan_transitions :
  forall a i pending,
    PairRunSuffix a (i + 1) pending ->
    Znth (i + 1) a 0 <> 1 ->
    AdjacentCoprime a i ->
    PairRunSuffix a ((i + 1) + 1) (pending + 1).
Proof.
  intros a i pending Hsuffix Hnonone Hedge.
  unfold PairRunSuffix in *; simpl in *.
  replace (i + 1 + 1 - (pending + 1) - 1)
    with (i + 1 - pending - 1) by lia.
  destruct Hsuffix as [Hstart [Hvalues [Hedges Hleft]]].
  split; [lia |].
  split.
  - intros j Hj.
    destruct (Z.eq_dec j (i + 1)) as [-> | Hneq].
    + exact Hnonone.
    + apply Hvalues. lia.
  - split.
    + intros j Hj.
      destruct (Z.eq_dec j i) as [-> | Hneq].
      * exact Hedge.
      * apply Hedges. lia.
    + exact Hleft.
Qed.
Lemma pair_run_suffix_restart_noncoprime__pair_scan_transitions :
  forall a i,
    0 <= i + 1 < Zlength a ->
    Znth (i + 1) a 0 <> 1 ->
    ~ AdjacentCoprime a i ->
    PairRunSuffix a ((i + 1) + 1) 0.
Proof.
  intros a i Hibounds Hnonone Hbreak.
  unfold PairRunSuffix; simpl.
  replace (i + 1 + 1 - 0 - 1) with (i + 1) by lia.
  split; [lia |].
  split.
  - intros j Hj. assert (j = i + 1) by lia. subst j. exact Hnonone.
  - split.
    + intros j Hj. lia.
    + right; right.
      replace (i + 1 - 1) with i by lia.
      exact Hbreak.
Qed.
Lemma pair_scan_break_step__pair_scan_transitions :
  forall a i committed pending old_savings,
    0 <= i -> i + 1 < Zlength a ->
    Znth (i + 1) a 0 <> 1 ->
    ~ AdjacentCoprime a i ->
    old_savings = committed + pending ÷ 2 ->
    PairSavingsScan a (i + 1) committed pending old_savings ->
    PairSavingsScan a ((i + 1) + 1) (committed + pending ÷ 2) 0
      ((committed + pending ÷ 2) + 0 ÷ 2) /\
    PairRunSuffix a ((i + 1) + 1) 0.
Proof.
  intros a i committed pending old_savings Hi Hibound Hnonone Hbreak
    Hold_savings Hscan.
  destruct Hscan as [Hsavings [Hpending Hprefix]].
  split.
  - unfold PairSavingsScan.
    split; [reflexivity |].
    split; [lia |].
    rewrite zero_quot_two__pair_scan_transitions.
    replace (committed + pending ÷ 2 + 0)
      with (committed + pending ÷ 2) by lia.
    rewrite <- Hold_savings.
    apply pair_savings_prefix_extend_noncoprime__pair_scan_transitions.
    + lia.
    + replace (i + 1 - 1) with i by lia. exact Hbreak.
    + exact Hprefix.
  - apply pair_run_suffix_restart_noncoprime__pair_scan_transitions.
    + lia.
    + exact Hnonone.
    + exact Hbreak.
Qed.
Lemma set_card_Z_as_sum__pair_scan_transitions :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_interval_empty__pair_scan_transitions :
  forall low high (P : Z -> Prop),
    high <= low ->
    #(fun z : Z => low <= z < high /\ P z) = 0.
Proof.
  intros low high P Hempty.
  rewrite set_card_Z_as_sum__pair_scan_transitions.
  apply SumLib.ZRange.sum_Z_range_empty.
  exact Hempty.
Qed.
Lemma set_card_interval_cons__pair_scan_transitions :
  forall low high (P : Z -> Prop),
    low < high ->
    #(fun z : Z => low <= z < high /\ P z) =
      (if prop_dec (P low) then 1 else 0) +
      #(fun z : Z => low + 1 <= z < high /\ P z).
Proof.
  intros low high P Hlt.
  rewrite !set_card_Z_as_sum__pair_scan_transitions.
  apply SumLib.ZRange.sum_Z_range_cons.
  exact Hlt.
Qed.
Lemma set_card_interval_split__pair_scan_transitions :
  forall low mid high (P : Z -> Prop),
    low <= mid <= high ->
    #(fun z : Z => low <= z < high /\ P z) =
      #(fun z : Z => low <= z < mid /\ P z) +
      #(fun z : Z => mid <= z < high /\ P z).
Proof.
  intros low mid high P Hbounds.
  rewrite !set_card_Z_as_sum__pair_scan_transitions.
  apply SumLib.ZRange.sum_Z_range_split.
  tauto.
Qed.
Lemma nat_ind2__pair_scan_transitions :
  forall (P : nat -> Prop),
    P O -> P (S O) ->
    (forall n, P n -> P (S n) -> P (S (S n))) ->
    forall n, P n.
Proof.
  intros P H0 H1 Hstep.
  assert (Hpair : forall n, P n /\ P (S n)).
  {
    induction n as [|n IH].
    - split; assumption.
    - destruct IH as [Hn HSn].
      split.
      + exact HSn.
      + apply Hstep; assumption.
  }
  intros n. exact (proj1 (Hpair n)).
Qed.
Lemma spaced_interval_card_upper__pair_scan_transitions :
  forall (n : nat) (lo : Z) (chosen : Z -> Prop),
    (forall x y, chosen x -> chosen y -> x <> y ->
      2 <= Z.abs (x - y)) ->
    #(fun x : Z => lo <= x < lo + Z.of_nat n /\ chosen x) <=
      (Z.of_nat n + 1) / 2.
Proof.
  apply (nat_ind2__pair_scan_transitions
    (fun n => forall lo chosen,
      (forall x y, chosen x -> chosen y -> x <> y ->
        2 <= Z.abs (x - y)) ->
      #(fun x : Z => lo <= x < lo + Z.of_nat n /\ chosen x) <=
        (Z.of_nat n + 1) / 2)).
  - intros lo chosen Hsep.
    rewrite set_card_interval_empty__pair_scan_transitions by lia.
    reflexivity.
  - intros lo chosen Hsep.
    rewrite set_card_interval_cons__pair_scan_transitions by lia.
    rewrite set_card_interval_empty__pair_scan_transitions by lia.
    change ((if prop_dec (chosen lo) then 1 else 0) + 0 <= 1).
    destruct (prop_dec (chosen lo)); lia.
  - intros n IHn IHSn lo chosen Hsep.
    rewrite set_card_interval_cons__pair_scan_transitions by lia.
    destruct (prop_dec (chosen lo)) as [Hlo | Hlo]; simpl.
    + assert (Hnext : ~ chosen (lo + 1)).
      {
        intros Hchosen.
        specialize (Hsep lo (lo + 1) Hlo Hchosen ltac:(lia)).
        rewrite Z.abs_neq in Hsep by lia.
        lia.
      }
      rewrite set_card_interval_cons__pair_scan_transitions by lia.
      destruct (prop_dec (chosen (lo + 1))) as [Hbad | _];
        [contradiction | simpl].
      specialize (IHn (lo + 2) chosen Hsep).
      match goal with
      | |- context [@set_card Z ?P ?FP] =>
          assert (Hcardeq :
            @set_card Z P FP =
            @set_card Z
              (fun x : Z => lo + 2 <= x < lo + 2 + Z.of_nat n /\ chosen x)
              (finite_Z_range' (lo + 2) (lo + 2 + Z.of_nat n) chosen));
          [ apply (@set_card_extensional__pair_scan_transitions Z P
              (fun x : Z => lo + 2 <= x < lo + 2 + Z.of_nat n /\ chosen x)
              FP (finite_Z_range' (lo + 2) (lo + 2 + Z.of_nat n) chosen));
            intros x; change
              ((lo + 1 + 1 <= x < lo + Z.of_nat (S (S n)) /\ chosen x) <->
               (lo + 2 <= x < lo + 2 + Z.of_nat n /\ chosen x));
            split; intros [Hx HP]; split; try exact HP; lia
          | rewrite Hcardeq;
            change
              (1 + @set_card Z
                (fun x : Z => lo + 2 <= x < lo + 2 + Z.of_nat n /\ chosen x)
                (finite_Z_range' (lo + 2) (lo + 2 + Z.of_nat n) chosen) <=
               (Z.of_nat (S (S n)) + 1) / 2) ]
      end.
      replace ((Z.of_nat (S (S n)) + 1) / 2)
        with ((Z.of_nat n + 1) / 2 + 1).
      * lia.
      * replace (Z.of_nat (S (S n)) + 1)
          with ((Z.of_nat n + 1) + 1 * 2) by lia.
        symmetry. apply Z_div_plus_full. lia.
    + specialize (IHSn (lo + 1) chosen Hsep).
      match goal with
      | |- context [@set_card Z ?P ?FP] =>
          assert (Hcardeq :
            @set_card Z P FP =
            @set_card Z
              (fun x : Z => lo + 1 <= x < lo + 1 + Z.of_nat (S n) /\ chosen x)
              (finite_Z_range' (lo + 1) (lo + 1 + Z.of_nat (S n)) chosen));
          [ apply (@set_card_extensional__pair_scan_transitions Z P
              (fun x : Z => lo + 1 <= x < lo + 1 + Z.of_nat (S n) /\ chosen x)
              FP (finite_Z_range' (lo + 1) (lo + 1 + Z.of_nat (S n)) chosen));
            intros x; change
              ((lo + 1 <= x < lo + Z.of_nat (S (S n)) /\ chosen x) <->
               (lo + 1 <= x < lo + 1 + Z.of_nat (S n) /\ chosen x));
            split; intros [Hx HP]; split; try exact HP; lia
          | rewrite Hcardeq ]
      end.
      eapply Z.le_trans; [exact IHSn |].
      apply Z.div_le_mono; lia.
Qed.
Lemma spaced_interval_canonical__pair_scan_transitions :
  forall (n : nat) (lo : Z),
    exists chosen : Z -> Prop,
      (forall x, chosen x -> lo <= x < lo + Z.of_nat n) /\
      (forall x y, chosen x -> chosen y -> x <> y ->
        2 <= Z.abs (x - y)) /\
      #(fun x : Z => lo <= x < lo + Z.of_nat n /\ chosen x) =
        (Z.of_nat n + 1) / 2.
Proof.
  apply (nat_ind2__pair_scan_transitions
    (fun n => forall lo,
      exists chosen : Z -> Prop,
        (forall x, chosen x -> lo <= x < lo + Z.of_nat n) /\
        (forall x y, chosen x -> chosen y -> x <> y ->
          2 <= Z.abs (x - y)) /\
        #(fun x : Z => lo <= x < lo + Z.of_nat n /\ chosen x) =
          (Z.of_nat n + 1) / 2)).
  - intros lo. exists (fun _ => False).
    split; [tauto |]. split; [tauto |].
    rewrite set_card_interval_empty__pair_scan_transitions by lia.
    reflexivity.
  - intros lo. exists (fun x => x = lo).
    split.
    + intros x ->. lia.
    + split.
      * intros x y -> -> Hneq. contradiction.
      * rewrite set_card_interval_cons__pair_scan_transitions by lia.
        destruct (prop_dec (lo = lo)) as [_ | Hbad]; [simpl | contradiction].
        rewrite set_card_interval_empty__pair_scan_transitions by lia.
        reflexivity.
  - intros n IHn IHSn lo.
    destruct (IHn (lo + 2)) as [tail [Htail_bounds [Htail_sep Htail_card]]].
    exists (fun x => x = lo \/ tail x).
    split.
    + intros x [-> | Htail].
      * lia.
      * specialize (Htail_bounds x Htail). lia.
    + split.
      * intros x y Hx Hy Hneq.
        destruct Hx as [-> | Hx]; destruct Hy as [-> | Hy].
        -- contradiction.
        -- specialize (Htail_bounds y Hy).
           rewrite Z.abs_neq by lia. lia.
        -- specialize (Htail_bounds x Hx).
           rewrite Z.abs_eq by lia. lia.
        -- apply Htail_sep; assumption.
      * rewrite set_card_interval_cons__pair_scan_transitions by lia.
        destruct (prop_dec (lo = lo \/ tail lo)) as [_ | Hbad];
          [simpl | exfalso; apply Hbad; left; reflexivity].
        rewrite set_card_interval_cons__pair_scan_transitions by lia.
        assert (Hnotnext : ~ (lo + 1 = lo \/ tail (lo + 1))).
        {
          intros [Heq | Htail]; [lia |].
          specialize (Htail_bounds (lo + 1) Htail). lia.
        }
        destruct (prop_dec (lo + 1 = lo \/ tail (lo + 1))) as [Hbad | _];
          [contradiction | simpl].
        match goal with
        | |- context [@set_card Z ?P ?FP] =>
            assert (Hcardeq :
              @set_card Z P FP =
              @set_card Z
                (fun x : Z => lo + 2 <= x < lo + 2 + Z.of_nat n /\ tail x)
                (finite_Z_range' (lo + 2) (lo + 2 + Z.of_nat n) tail));
            [ apply (@set_card_extensional__pair_scan_transitions Z P
                (fun x : Z => lo + 2 <= x < lo + 2 + Z.of_nat n /\ tail x)
                FP (finite_Z_range' (lo + 2) (lo + 2 + Z.of_nat n) tail));
              intros x; change
                ((lo + 1 + 1 <= x < lo + Z.of_nat (S (S n)) /\
                    (x = lo \/ tail x)) <->
                 (lo + 2 <= x < lo + 2 + Z.of_nat n /\ tail x));
              split;
                [ intros [Hx [Heq | Htail]]; [lia | split; [lia | exact Htail]]
                | intros [Hx Htail]; split; [lia | right; exact Htail] ]
            | rewrite Hcardeq;
              change
                (1 + @set_card Z
                  (fun x : Z => lo + 2 <= x < lo + 2 + Z.of_nat n /\ tail x)
                  (finite_Z_range' (lo + 2) (lo + 2 + Z.of_nat n) tail) =
                 (Z.of_nat (S (S n)) + 1) / 2) ]
        end.
        rewrite Htail_card.
        replace (Z.of_nat (S (S n)) + 1)
          with ((Z.of_nat n + 1) + 1 * 2) by lia.
        rewrite Z_div_plus_full by lia.
        lia.
Qed.
Lemma pair_run_suffix_start_excluded__pair_scan_transitions :
  forall a hi pending target_hi center,
    PairRunSuffix a hi pending ->
    NonOnePairCenter a target_hi center ->
    center <> hi - pending - 1.
Proof.
  intros a hi pending target_hi center Hsuffix Hcenter Heq.
  unfold PairRunSuffix in Hsuffix.
  destruct Hsuffix as [Hstart [Hvalues [Hedges Hleft]]].
  unfold NonOnePairCenter in Hcenter.
  destruct Hcenter as [Hrange [Hprev [Hcur [Hnext [Hedgeprev Hedgecur]]]]].
  destruct Hleft as [Hzero | [Hone | Hbreak]].
  - lia.
  - apply Hprev. rewrite Heq. exact Hone.
  - apply Hbreak. rewrite <- Heq. exact Hedgeprev.
Qed.
Lemma pair_run_suffix_inner_center__pair_scan_transitions :
  forall a hi pending center,
    PairRunSuffix a hi pending ->
    hi - pending <= center < hi - 1 ->
    NonOnePairCenter a hi center.
Proof.
  intros a hi pending center Hsuffix Hrange.
  unfold PairRunSuffix in Hsuffix.
  destruct Hsuffix as [Hstart [Hvalues [Hedges Hleft]]].
  unfold NonOnePairCenter.
  split; [lia |].
  split.
  - apply Hvalues. lia.
  - split.
    + apply Hvalues. lia.
    + split.
      * apply Hvalues. lia.
      * split; apply Hedges; lia.
Qed.
Lemma pair_center_selection_suffix_replace__pair_scan_transitions :
  forall a old_hi pending target_hi chosen suffix,
    PairRunSuffix a old_hi pending ->
    PairCenterSelection a target_hi chosen ->
    (forall x, suffix x ->
      old_hi - pending <= x < target_hi - 1 /\
      NonOnePairCenter a target_hi x) ->
    (forall x y, suffix x -> suffix y -> x <> y ->
      2 <= Z.abs (x - y)) ->
    PairCenterSelection a target_hi
      (fun x => (chosen x /\ x < old_hi - pending) \/ suffix x).
Proof.
  intros a old_hi pending target_hi chosen suffix Hrun
    [Hchosen_valid Hchosen_sep] Hsuffix_valid Hsuffix_sep.
  unfold PairCenterSelection.
  split.
  - intros x [[Hx _] | Hx].
    + apply Hchosen_valid. exact Hx.
    + exact (proj2 (Hsuffix_valid x Hx)).
  - intros x y Hx Hy Hneq.
    destruct Hx as [[Hx Hxbound] | Hx];
      destruct Hy as [[Hy Hybound] | Hy].
    + apply Hchosen_sep; assumption.
    + destruct (Hsuffix_valid y Hy) as [Hyrange _].
      assert (Hxstart : x <> old_hi - pending - 1).
      {
        eapply pair_run_suffix_start_excluded__pair_scan_transitions;
          [exact Hrun | apply Hchosen_valid; exact Hx].
      }
      rewrite Z.abs_neq by lia. lia.
    + destruct (Hsuffix_valid x Hx) as [Hxrange _].
      assert (Hystart : y <> old_hi - pending - 1).
      {
        eapply pair_run_suffix_start_excluded__pair_scan_transitions;
          [exact Hrun | apply Hchosen_valid; exact Hy].
      }
      rewrite Z.abs_eq by lia. lia.
    + apply Hsuffix_sep; assumption.
Qed.
Lemma pair_center_count_suffix_replace__pair_scan_transitions :
  forall old_hi pending target_hi chosen suffix,
    1 <= old_hi - pending <= target_hi - 1 ->
    (forall x, suffix x ->
      old_hi - pending <= x < target_hi - 1) ->
    #(fun x : Z => 1 <= x < target_hi - 1 /\
        ((chosen x /\ x < old_hi - pending) \/ suffix x)) =
      #(fun x : Z => 1 <= x < old_hi - pending /\ chosen x) +
      #(fun x : Z => old_hi - pending <= x < target_hi - 1 /\ suffix x).
Proof.
  intros old_hi pending target_hi chosen suffix Hmid Hsuffix.
  rewrite (set_card_interval_split__pair_scan_transitions
    1 (old_hi - pending) (target_hi - 1)
    (fun x => (chosen x /\ x < old_hi - pending) \/ suffix x)) by exact Hmid.
  f_equal.
  - eapply set_card_extensional__pair_scan_transitions.
    intros x. split.
    + intros [Hrange [[Hchosen _] | Hsuf]].
      * split; assumption.
      * specialize (Hsuffix x Hsuf). lia.
    + intros [Hrange Hchosen].
      split; [exact Hrange | left; split; [exact Hchosen | lia]].
  - eapply set_card_extensional__pair_scan_transitions.
    intros x. split.
    + intros [Hrange [[_ Hlt] | Hsuf]].
      * lia.
      * split; assumption.
    + intros [Hrange Hsuf].
      split; [exact Hrange | right; exact Hsuf].
Qed.
Lemma spaced_interval_card_upper_between__pair_scan_transitions :
  forall low high (chosen : Z -> Prop),
    low <= high ->
    (forall x y, chosen x -> chosen y -> x <> y ->
      2 <= Z.abs (x - y)) ->
    #(fun x : Z => low <= x < high /\ chosen x) <=
      (high - low + 1) / 2.
Proof.
  intros low high chosen Hbounds Hsep.
  pose proof (spaced_interval_card_upper__pair_scan_transitions
    (Z.to_nat (high - low)) low chosen Hsep) as Hupper.
  rewrite Z2Nat.id in Hupper by lia.
  match type of Hupper with
  | @set_card Z ?P ?FP <= _ =>
      assert (Hcardeq :
        @set_card Z P FP =
        @set_card Z (fun x : Z => low <= x < high /\ chosen x)
          (finite_Z_range' low high chosen));
      [ apply (@set_card_extensional__pair_scan_transitions Z P
          (fun x : Z => low <= x < high /\ chosen x)
          FP (finite_Z_range' low high chosen));
        intros x; change
          ((low <= x < low + (high - low) /\ chosen x) <->
           (low <= x < high /\ chosen x));
        split; intros [Hx HP]; split; try exact HP; lia
      | rewrite Hcardeq in Hupper ]
  end.
  exact Hupper.
Qed.
Lemma spaced_interval_canonical_between__pair_scan_transitions :
  forall low high,
    low <= high ->
    exists chosen : Z -> Prop,
      (forall x, chosen x -> low <= x < high) /\
      (forall x y, chosen x -> chosen y -> x <> y ->
        2 <= Z.abs (x - y)) /\
      #(fun x : Z => low <= x < high /\ chosen x) =
        (high - low + 1) / 2.
Proof.
  intros low high Hbounds.
  destruct (spaced_interval_canonical__pair_scan_transitions
    (Z.to_nat (high - low)) low) as
      [chosen [Hchosen_bounds [Hchosen_sep Hchosen_card]]].
  rewrite Z2Nat.id in Hchosen_bounds by lia.
  rewrite Z2Nat.id in Hchosen_card by lia.
  exists chosen.
  split.
  - intros x Hx. specialize (Hchosen_bounds x Hx). lia.
  - split; [exact Hchosen_sep |].
    match type of Hchosen_card with
    | @set_card Z ?P ?FP = _ =>
        assert (Hcardeq :
          @set_card Z P FP =
          @set_card Z (fun x : Z => low <= x < high /\ chosen x)
            (finite_Z_range' low high chosen));
        [ apply (@set_card_extensional__pair_scan_transitions Z P
            (fun x : Z => low <= x < high /\ chosen x)
            FP (finite_Z_range' low high chosen));
          intros x; change
            ((low <= x < low + (high - low) /\ chosen x) <->
             (low <= x < high /\ chosen x));
          split; intros [Hx HP]; split; try exact HP; lia
        | rewrite <- Hcardeq ]
    end.
    exact Hchosen_card.
Qed.
Lemma pair_center_selection_left_restrict__pair_scan_transitions :
  forall a source_hi target_hi cutoff chosen,
    PairCenterSelection a source_hi chosen ->
    cutoff <= target_hi - 1 ->
    PairCenterSelection a target_hi
      (fun x => chosen x /\ x < cutoff).
Proof.
  intros a source_hi target_hi cutoff chosen
    [Hvalid Hsep] Hcutoff.
  unfold PairCenterSelection.
  split.
  - intros x [Hx Hxcut].
    specialize (Hvalid x Hx).
    unfold NonOnePairCenter in *.
    destruct Hvalid as [Hrange Hrest].
    split; [lia | exact Hrest].
  - intros x y [Hx _] [Hy _] Hneq.
    apply Hsep; assumption.
Qed.
Lemma pair_center_selection_hi_extend__pair_scan_transitions :
  forall a source_hi target_hi chosen,
    source_hi <= target_hi ->
    PairCenterSelection a source_hi chosen ->
    PairCenterSelection a target_hi chosen.
Proof.
  intros a source_hi target_hi chosen Hhi [Hvalid Hsep].
  unfold PairCenterSelection.
  split; [| exact Hsep].
  intros x Hx.
  specialize (Hvalid x Hx).
  unfold NonOnePairCenter in *.
  destruct Hvalid as [Hrange Hrest].
  split; [lia | exact Hrest].
Qed.
Lemma pair_savings_prefix_extend_coprime_positive__pair_scan_transitions :
  forall a old_hi pending old_savings,
    0 < pending ->
    PairRunSuffix a old_hi pending ->
    PairRunSuffix a (old_hi + 1) (pending + 1) ->
    PairSavingsPrefix a old_hi old_savings ->
    PairSavingsPrefix a (old_hi + 1)
      (old_savings - pending / 2 + (pending + 1) / 2).
Proof.
  intros a old_hi pending old_savings Hpending Hrun Hrunnew Hprefix.
  assert (Hmidold : 1 <= old_hi - pending <= old_hi - 1).
  {
    unfold PairRunSuffix in Hrun.
    destruct Hrun as [Hstart _]. lia.
  }
  assert (Hmidnew : 1 <= old_hi - pending <= old_hi + 1 - 1) by lia.
  destruct (spaced_interval_canonical_between__pair_scan_transitions
    (old_hi - pending) (old_hi - 1) ltac:(lia)) as
      [oldcanon [Holdcanon_bounds [Holdcanon_sep Holdcanon_card]]].
  destruct (spaced_interval_canonical_between__pair_scan_transitions
    (old_hi - pending) old_hi ltac:(lia)) as
      [newcanon [Hnewcanon_bounds [Hnewcanon_sep Hnewcanon_card]]].
  replace (old_hi - 1 - (old_hi - pending) + 1) with pending
    in Holdcanon_card by lia.
  replace (old_hi - (old_hi - pending) + 1) with (pending + 1)
    in Hnewcanon_card by lia.
  assert (Holdcanon_valid : forall x, oldcanon x ->
    old_hi - pending <= x < old_hi - 1 /\
    NonOnePairCenter a old_hi x).
  {
    intros x Hx. split.
    - apply Holdcanon_bounds. exact Hx.
    - apply pair_run_suffix_inner_center__pair_scan_transitions
        with (pending := pending); [exact Hrun |].
      apply Holdcanon_bounds. exact Hx.
  }
  assert (Hnewcanon_valid : forall x, newcanon x ->
    old_hi - pending <= x < old_hi + 1 - 1 /\
    NonOnePairCenter a (old_hi + 1) x).
  {
    intros x Hx. split.
    - specialize (Hnewcanon_bounds x Hx). lia.
    - apply pair_run_suffix_inner_center__pair_scan_transitions
        with (pending := pending + 1); [exact Hrunnew |].
      specialize (Hnewcanon_bounds x Hx). lia.
  }
  unfold PairSavingsPrefix, max_value_of_subset, max_object_of_subset in *.
  destruct Hprefix as [best [[Hbest_selected Hbest_max] Hbest_value]].
  assert (Hbest_split :
    #(fun x : Z => 1 <= x < old_hi - 1 /\ best x) =
      #(fun x : Z => 1 <= x < old_hi - pending /\ best x) +
      #(fun x : Z => old_hi - pending <= x < old_hi - 1 /\ best x)).
  {
    apply set_card_interval_split__pair_scan_transitions. exact Hmidold.
  }
  assert (Hbest_suffix_upper :
    #(fun x : Z => old_hi - pending <= x < old_hi - 1 /\ best x)
      <= pending / 2).
  {
    pose proof (spaced_interval_card_upper_between__pair_scan_transitions
      (old_hi - pending) (old_hi - 1) best ltac:(lia)
      (proj2 Hbest_selected)) as Hupper.
    replace (old_hi - 1 - (old_hi - pending) + 1) with pending
      in Hupper by lia.
    exact Hupper.
  }
  assert (Holdcombined_selected : PairCenterSelection a old_hi
    (fun x => (best x /\ x < old_hi - pending) \/ oldcanon x)).
  {
    eapply pair_center_selection_suffix_replace__pair_scan_transitions;
      eauto.
  }
  assert (Holdcombined_count :
    #(fun x : Z => 1 <= x < old_hi - 1 /\
       ((best x /\ x < old_hi - pending) \/ oldcanon x)) =
      #(fun x : Z => 1 <= x < old_hi - pending /\ best x) + pending / 2).
  {
    rewrite pair_center_count_suffix_replace__pair_scan_transitions
      by (try exact Hmidold; intros x Hx; apply Holdcanon_bounds; exact Hx).
    rewrite Holdcanon_card. reflexivity.
  }
  pose proof (Hbest_max _ Holdcombined_selected) as Hbest_max_old.
  match type of Hbest_max_old with
  | @set_card Z ?P ?FP <= _ =>
      assert (Hcardeq :
        @set_card Z P FP =
        #(fun x : Z => 1 <= x < old_hi - pending /\ best x) +
          pending / 2);
      [ etransitivity;
        [ apply (@set_card_extensional__pair_scan_transitions Z P
            (fun x : Z => 1 <= x < old_hi - 1 /\
              ((best x /\ x < old_hi - pending) \/ oldcanon x))
            FP (finite_Z_range' 1 (old_hi - 1)
              (fun x => (best x /\ x < old_hi - pending) \/ oldcanon x)));
          intros x; cbn; tauto
        | exact Holdcombined_count ]
      | assert (Hbest_max_numeric :
          #(fun x : Z => 1 <= x < old_hi - pending /\ best x) +
            pending / 2 <=
          #(fun x : Z => 1 <= x < old_hi - 1 /\ best x));
        [ rewrite <- Hcardeq; exact Hbest_max_old |] ]
  end.
  assert (Hbest_total_value :
    #(fun x : Z => 1 <= x < old_hi - 1 /\ best x) = old_savings)
    by exact Hbest_value.
  rewrite Hbest_split in Hbest_value.
  assert (Hbest_left_exact :
    #(fun x : Z => 1 <= x < old_hi - pending /\ best x) + pending / 2 =
      old_savings) by lia.
  assert (Hnewcanon_card_target :
    #(fun x : Z => old_hi - pending <= x < old_hi + 1 - 1 /\ newcanon x) =
      (pending + 1) / 2).
  {
    replace (old_hi + 1 - 1) with old_hi by lia.
    exact Hnewcanon_card.
  }
  exists (fun x => (best x /\ x < old_hi - pending) \/ newcanon x).
  split.
  - split.
    + eapply pair_center_selection_suffix_replace__pair_scan_transitions;
        [ exact Hrun
        | apply (pair_center_selection_hi_extend__pair_scan_transitions
            a old_hi (old_hi + 1) best);
          [lia | exact Hbest_selected]
        | exact Hnewcanon_valid
        | exact Hnewcanon_sep ].
    + intros other Hother_selected.
      assert (Hother_split :
        #(fun x : Z => 1 <= x < old_hi + 1 - 1 /\ other x) =
          #(fun x : Z => 1 <= x < old_hi - pending /\ other x) +
          #(fun x : Z => old_hi - pending <= x < old_hi + 1 - 1 /\ other x)).
      {
        apply set_card_interval_split__pair_scan_transitions. exact Hmidnew.
      }
      assert (Hother_suffix_upper :
        #(fun x : Z => old_hi - pending <= x < old_hi + 1 - 1 /\ other x)
          <= (pending + 1) / 2).
      {
        pose proof (spaced_interval_card_upper_between__pair_scan_transitions
          (old_hi - pending) (old_hi + 1 - 1) other ltac:(lia)
          (proj2 Hother_selected)) as Hupper.
        replace (old_hi + 1 - 1 - (old_hi - pending) + 1)
          with (pending + 1) in Hupper by lia.
        exact Hupper.
      }
      assert (Hother_left_selected : PairCenterSelection a old_hi
        (fun x => other x /\ x < old_hi - pending)).
      {
        eapply pair_center_selection_left_restrict__pair_scan_transitions;
          [exact Hother_selected | lia].
      }
      assert (Hother_oldcombined_selected : PairCenterSelection a old_hi
        (fun x =>
          ((other x /\ x < old_hi - pending) /\ x < old_hi - pending) \/
          oldcanon x)).
      {
        eapply pair_center_selection_suffix_replace__pair_scan_transitions;
          eauto.
      }
      pose proof (Hbest_max _ Hother_oldcombined_selected) as Hother_old_max.
      assert (Hleft_card :
        #(fun x : Z => 1 <= x < old_hi - pending /\
          (other x /\ x < old_hi - pending)) =
        #(fun x : Z => 1 <= x < old_hi - pending /\ other x)).
      {
        eapply set_card_extensional__pair_scan_transitions.
        intros x. tauto.
      }
      assert (Hother_oldcombined_count :
        #(fun x : Z => 1 <= x < old_hi - 1 /\
          (((other x /\ x < old_hi - pending) /\
              x < old_hi - pending) \/ oldcanon x)) =
        #(fun x : Z => 1 <= x < old_hi - pending /\ other x) +
          pending / 2).
      {
        rewrite pair_center_count_suffix_replace__pair_scan_transitions
          by (try exact Hmidold; intros x Hx;
            apply Holdcanon_bounds; exact Hx).
        rewrite Holdcanon_card, Hleft_card. reflexivity.
      }
      match type of Hother_old_max with
      | @set_card Z ?PL ?FL <= @set_card Z ?PR ?FR =>
          assert (Heqleft : @set_card Z PL FL =
            #(fun x : Z => 1 <= x < old_hi - pending /\ other x) +
              pending / 2);
          [ etransitivity;
            [ apply (@set_card_extensional__pair_scan_transitions Z PL
                (fun x : Z => 1 <= x < old_hi - 1 /\
                  (((other x /\ x < old_hi - pending) /\
                    x < old_hi - pending) \/ oldcanon x))
                FL (finite_Z_range' 1 (old_hi - 1)
                  (fun x => ((other x /\ x < old_hi - pending) /\
                    x < old_hi - pending) \/ oldcanon x)));
              intros x; cbn; tauto
            | exact Hother_oldcombined_count ]
          | assert (Heqright : @set_card Z PR FR = old_savings);
            [ etransitivity;
              [ apply (@set_card_extensional__pair_scan_transitions Z PR
                  (fun x : Z => 1 <= x < old_hi - 1 /\ best x)
                  FR (finite_Z_range' 1 (old_hi - 1) best));
                intros x; cbn; tauto
              | exact Hbest_total_value ]
            | assert (Hother_old_max_numeric :
                #(fun x : Z => 1 <= x < old_hi - pending /\ other x) +
                  pending / 2 <= old_savings);
              [ rewrite <- Heqright, <- Heqleft; exact Hother_old_max |] ] ]
      end.
      rewrite Hother_split.
      rewrite pair_center_count_suffix_replace__pair_scan_transitions
        by (try exact Hmidnew; intros x Hx;
          specialize (Hnewcanon_bounds x Hx); lia).
      rewrite Hnewcanon_card_target.
      lia.
  - rewrite pair_center_count_suffix_replace__pair_scan_transitions
      by (try exact Hmidnew; intros x Hx;
        specialize (Hnewcanon_bounds x Hx); lia).
    rewrite Hnewcanon_card_target. lia.
Qed.
Lemma non_one_pair_center_extend_zero_suffix__pair_scan_transitions :
  forall a hi center,
    PairRunSuffix a hi 0 ->
    (NonOnePairCenter a (hi + 1) center <->
     NonOnePairCenter a hi center).
Proof.
  intros a hi center Hrun.
  split.
  - intros Hcenter.
    assert (Hneq : center <> hi - 1).
    {
      pose proof (pair_run_suffix_start_excluded__pair_scan_transitions
        a hi 0 (hi + 1) center Hrun Hcenter) as Hexcluded.
      lia.
    }
    unfold NonOnePairCenter in *.
    destruct Hcenter as [Hrange Hrest].
    split; [lia | exact Hrest].
  - intros Hcenter.
    unfold NonOnePairCenter in *.
    destruct Hcenter as [Hrange Hrest].
    split; [lia | exact Hrest].
Qed.
Lemma pair_center_selection_extend_zero_suffix__pair_scan_transitions :
  forall a hi chosen,
    PairRunSuffix a hi 0 ->
    (PairCenterSelection a (hi + 1) chosen <->
     PairCenterSelection a hi chosen).
Proof.
  intros a hi chosen Hrun.
  unfold PairCenterSelection.
  split; intros [Hvalid Hsep]; split; try exact Hsep;
    intros center Hchosen.
  - apply (proj1
      (non_one_pair_center_extend_zero_suffix__pair_scan_transitions
        a hi center Hrun)).
    apply Hvalid. exact Hchosen.
  - apply (proj2
      (non_one_pair_center_extend_zero_suffix__pair_scan_transitions
        a hi center Hrun)).
    apply Hvalid. exact Hchosen.
Qed.
Lemma pair_center_count_extend_zero_suffix__pair_scan_transitions :
  forall a hi chosen,
    PairRunSuffix a hi 0 ->
    (PairCenterSelection a hi chosen \/
     PairCenterSelection a (hi + 1) chosen) ->
    #(fun center : Z => 1 <= center < hi - 1 /\ chosen center) =
    #(fun center : Z => 1 <= center < hi + 1 - 1 /\ chosen center).
Proof.
  intros a hi chosen Hrun Hselection.
  eapply set_card_extensional__pair_scan_transitions.
  intros center. split.
  - intros [Hrange Hchosen]. split; [lia | exact Hchosen].
  - intros [Hrange Hchosen]. split; [| exact Hchosen].
    assert (Hneq : center <> hi - 1).
    {
      destruct Hselection as [Hold | Hnew].
      - pose proof (proj2
          (non_one_pair_center_extend_zero_suffix__pair_scan_transitions
            a hi center Hrun) ((proj1 Hold) center Hchosen)) as Hcenter.
        pose proof (pair_run_suffix_start_excluded__pair_scan_transitions
          a hi 0 (hi + 1) center Hrun Hcenter) as Hexcluded.
        lia.
      - pose proof (pair_run_suffix_start_excluded__pair_scan_transitions
          a hi 0 (hi + 1) center Hrun ((proj1 Hnew) center Hchosen))
          as Hexcluded.
        lia.
    }
    lia.
Qed.
Lemma pair_savings_prefix_extend_zero_suffix__pair_scan_transitions :
  forall a hi savings,
    PairRunSuffix a hi 0 ->
    PairSavingsPrefix a hi savings ->
    PairSavingsPrefix a (hi + 1) savings.
Proof.
  intros a hi savings Hrun Hprefix.
  unfold PairSavingsPrefix, max_value_of_subset, max_object_of_subset in *.
  destruct Hprefix as [chosen [[Hselected Hmax] Hvalue]].
  exists chosen. split.
  - split.
    + apply (proj2
        (pair_center_selection_extend_zero_suffix__pair_scan_transitions
          a hi chosen Hrun)). exact Hselected.
    + intros other Hother.
      pose proof (proj1
        (pair_center_selection_extend_zero_suffix__pair_scan_transitions
          a hi other Hrun) Hother) as Hotherold.
      specialize (Hmax other Hotherold).
      rewrite <- (pair_center_count_extend_zero_suffix__pair_scan_transitions
        a hi other Hrun (or_intror Hother)).
      rewrite <- (pair_center_count_extend_zero_suffix__pair_scan_transitions
        a hi chosen Hrun (or_introl Hselected)).
      exact Hmax.
  - rewrite <- (pair_center_count_extend_zero_suffix__pair_scan_transitions
      a hi chosen Hrun (or_introl Hselected)).
    exact Hvalue.
Qed.
Lemma pair_scan_coprime_step__pair_scan_transitions :
  forall a i committed pending old_savings,
    0 <= i ->
    i + 1 < Zlength a ->
    Znth (i + 1) a 0 <> 1 ->
    AdjacentCoprime a i ->
    old_savings = committed + pending ÷ 2 ->
    PairRunSuffix a (i + 1) pending ->
    PairSavingsScan a (i + 1) committed pending old_savings ->
    PairSavingsScan a ((i + 1) + 1) committed (pending + 1)
      (committed + (pending + 1) ÷ 2) /\
    PairRunSuffix a ((i + 1) + 1) (pending + 1).
Proof.
  intros a i committed pending old_savings Hi Hibound Hnonone Hedge
    Hold_savings Hrun Hscan.
  assert (Hrunnew : PairRunSuffix a ((i + 1) + 1) (pending + 1)).
  {
    eapply pair_run_suffix_extend_coprime_nonone__pair_scan_transitions;
      eauto.
  }
  destruct Hscan as [Hscan_value [Hpending_bounds Hprefix]].
  assert (Hpending_div : pending ÷ 2 = pending / 2).
  {
    apply Z.quot_div_nonneg; lia.
  }
  assert (Hnext_div : (pending + 1) ÷ 2 = (pending + 1) / 2).
  {
    apply Z.quot_div_nonneg; lia.
  }
  split; [| exact Hrunnew].
  unfold PairSavingsScan.
  split.
  - rewrite Hnext_div. reflexivity.
  - split; [lia |].
    destruct (Z.eq_dec pending 0) as [Hzero | Hnonzero].
    + subst pending.
      apply pair_savings_prefix_extend_zero_suffix__pair_scan_transitions
        with (hi := i + 1).
      * exact Hrun.
      * replace (committed + (0 + 1) ÷ 2) with old_savings by
          (rewrite Hnext_div; cbn; exact Hscan_value).
        exact Hprefix.
    + replace (committed + (pending + 1) ÷ 2)
        with (old_savings - pending / 2 + (pending + 1) / 2).
      * apply pair_savings_prefix_extend_coprime_positive__pair_scan_transitions
          with (old_hi := i + 1) (pending := pending);
          [lia | exact Hrun | exact Hrunnew | exact Hprefix].
      * rewrite Hpending_div in Hold_savings.
        rewrite Hnext_div. lia.
Qed.
Lemma pair_run_suffix_coprime_step__pair_scan_steps :
  forall a i pending,
    PairRunSuffix a (i + 1) pending ->
    Znth (i + 1) a 0 <> 1 ->
    AdjacentCoprime a i ->
    PairRunSuffix a ((i + 1) + 1) (pending + 1).
Proof.
  intros a i pending Hrun Hnonone Hedge.
  eapply pair_run_suffix_extend_coprime_nonone__pair_scan_transitions;
    eauto.
Qed.
Lemma pair_savings_scan_step__pair_scan_steps :
  forall a i committed pending old_savings,
    0 <= i ->
    i + 1 < Zlength a ->
    Znth (i + 1) a 0 <> 1 ->
    old_savings = committed + pending ÷ 2 ->
    PairRunSuffix a (i + 1) pending ->
    PairSavingsScan a (i + 1) committed pending old_savings ->
    (AdjacentCoprime a i ->
      PairSavingsScan a ((i + 1) + 1) committed (pending + 1)
        (committed + (pending + 1) ÷ 2)) /\
    (~ AdjacentCoprime a i ->
      PairSavingsScan a ((i + 1) + 1) (committed + pending ÷ 2) 0
        ((committed + pending ÷ 2) + 0 ÷ 2)).
Proof.
  intros a i committed pending old_savings Hi Hibound Hnonone
    Hold_savings Hrun Hscan.
  split; intro Hedge.
  - exact (proj1 (pair_scan_coprime_step__pair_scan_transitions
      a i committed pending old_savings Hi Hibound Hnonone Hedge
      Hold_savings Hrun Hscan)).
  - exact (proj1 (pair_scan_break_step__pair_scan_transitions
      a i committed pending old_savings Hi Hibound Hnonone Hedge
      Hold_savings Hscan)).
Qed.
Lemma set_card_extensional__pair_scan_entry :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros x.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
            1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma non_one_pair_center_extend_isolated_nonone__pair_scan_entry :
  forall a hi center,
    0 <= hi ->
    (hi = 0 \/ Znth (hi - 1) a 0 = 1) ->
    (NonOnePairCenter a (hi + 1) center <->
     NonOnePairCenter a hi center).
Proof.
  intros a hi center Hhi Hboundary.
  unfold NonOnePairCenter.
  destruct Hboundary as [-> | Hboundary].
  - split; intros H; destruct H as [? [? [? [? [? ?]]]]]; lia.
  - split.
    + intros H.
      destruct H as [Hrange [Hleft [Hcenter [Hright [Hedge1 Hedge2]]]]].
      split.
      * destruct (Z.eq_dec center (hi - 1)) as [-> | Hneq].
        -- contradiction.
        -- lia.
      * exact (conj Hleft (conj Hcenter (conj Hright (conj Hedge1 Hedge2)))).
    + intros H.
      destruct H as [Hrange [Hleft [Hcenter [Hright [Hedge1 Hedge2]]]]].
      split; [lia | exact (conj Hleft (conj Hcenter (conj Hright (conj Hedge1 Hedge2))))].
Qed.
Lemma pair_center_selection_extend_isolated_nonone__pair_scan_entry :
  forall a hi chosen,
    0 <= hi ->
    (hi = 0 \/ Znth (hi - 1) a 0 = 1) ->
    (PairCenterSelection a (hi + 1) chosen <->
     PairCenterSelection a hi chosen).
Proof.
  intros a hi chosen Hhi Hboundary.
  unfold PairCenterSelection.
  split; intros [Hvalid Hsep]; split; try exact Hsep;
    intros center Hchosen;
    apply (non_one_pair_center_extend_isolated_nonone__pair_scan_entry
      a hi center Hhi Hboundary);
    auto.
Qed.
Lemma pair_center_count_extend_isolated_nonone__pair_scan_entry :
  forall a hi chosen,
    0 <= hi ->
    (hi = 0 \/ Znth (hi - 1) a 0 = 1) ->
    (PairCenterSelection a hi chosen \/ PairCenterSelection a (hi + 1) chosen) ->
    #(fun center : Z => 1 <= center < hi - 1 /\ chosen center) =
    #(fun center : Z => 1 <= center < hi + 1 - 1 /\ chosen center).
Proof.
  intros a hi chosen Hhi Hboundary Hselection.
  eapply set_card_extensional__pair_scan_entry.
  intros center.
  split.
  - intros [Hrange Hchosen]. split; [lia | exact Hchosen].
  - intros [Hrange Hchosen].
    split; [| exact Hchosen].
    destruct Hselection as [Hselection | Hselection].
    + destruct Hselection as [Hvalid _].
      specialize (Hvalid center Hchosen).
      unfold NonOnePairCenter in Hvalid. tauto.
    + destruct Hselection as [Hvalid _].
      specialize (Hvalid center Hchosen).
      pose proof
        (proj1
          (non_one_pair_center_extend_isolated_nonone__pair_scan_entry
            a hi center Hhi Hboundary) Hvalid) as Hold.
      unfold NonOnePairCenter in Hold. tauto.
Qed.
Lemma pair_savings_prefix_extend_isolated_nonone__pair_scan_entry :
  forall a hi savings,
    0 <= hi ->
    (hi = 0 \/ Znth (hi - 1) a 0 = 1) ->
    PairSavingsPrefix a hi savings ->
    PairSavingsPrefix a (hi + 1) savings.
Proof.
  intros a hi savings Hhi Hboundary Hprefix.
  unfold PairSavingsPrefix, max_value_of_subset, max_object_of_subset in *.
  destruct Hprefix as [chosen [[Hselected Hmax] Hvalue]].
  exists chosen.
  split.
  - split.
    + apply (proj2
        (pair_center_selection_extend_isolated_nonone__pair_scan_entry
          a hi chosen Hhi Hboundary)).
      exact Hselected.
    + intros other Hother.
      pose proof
        (proj1
          (pair_center_selection_extend_isolated_nonone__pair_scan_entry
            a hi other Hhi Hboundary) Hother) as Hother_old.
      specialize (Hmax other Hother_old).
      rewrite <-
        (pair_center_count_extend_isolated_nonone__pair_scan_entry
          a hi other Hhi Hboundary (or_intror Hother)).
      rewrite <-
        (pair_center_count_extend_isolated_nonone__pair_scan_entry
          a hi chosen Hhi Hboundary (or_introl Hselected)).
      exact Hmax.
  - rewrite <-
      (pair_center_count_extend_isolated_nonone__pair_scan_entry
        a hi chosen Hhi Hboundary (or_introl Hselected)).
    exact Hvalue.
Qed.
Lemma pair_run_suffix_zero_at_nonone_boundary__pair_scan_entry :
  forall a i,
    0 <= i < Zlength a ->
    Znth i a 0 <> 1 ->
    (i = 0 \/ Znth (i - 1) a 0 = 1) ->
    PairRunSuffix a (i + 1) 0.
Proof.
  intros a i Hibounds Hnonone Hboundary.
  unfold PairRunSuffix; simpl.
  replace (i + 1 - 0 - 1) with i by lia.
  split; [lia |].
  split.
  - intros j Hj. assert (j = i) by lia. subst j. exact Hnonone.
  - split.
    + intros j Hj. lia.
    + destruct Hboundary as [Hboundary | Hboundary].
      * left; exact Hboundary.
      * right; left; exact Hboundary.
Qed.
Lemma pair_savings_scan_start_nonone__pair_scan_entry :
  forall a i committed,
    0 <= i < Zlength a ->
    Znth i a 0 <> 1 ->
    (i = 0 \/ Znth (i - 1) a 0 = 1) ->
    PairSavingsPrefix a i committed ->
    PairSavingsScan a (i + 1) committed 0 committed /\
    PairRunSuffix a (i + 1) 0.
Proof.
  intros a i committed Hibounds Hnonone Hboundary Hprefix.
  split.
  - unfold PairSavingsScan.
    split; [rewrite Z.div_0_l by lia; lia |].
    split; [lia |].
    apply pair_savings_prefix_extend_isolated_nonone__pair_scan_entry.
    + lia.
    + exact Hboundary.
    + exact Hprefix.
  - eapply pair_run_suffix_zero_at_nonone_boundary__pair_scan_entry; eauto.
Qed.
Lemma pair_selection_count_bound__pair_scan_exits :
  forall a hi chosen,
    0 <= hi ->
    PairCenterSelection a hi chosen ->
    2 * #(fun center : Z =>
      1 <= center < hi - 1 /\ chosen center) <= hi.
Proof.
  intros a hi chosen Hhi [Hvalid Hseparated].
  set (P := fun center : Z =>
    1 <= center < hi - 1 /\ chosen center).
  set (B := fun bit : Z => 0 <= bit < 2).
  set (Q := fun index : Z => 0 <= index < hi).
  pose proof
    (@set_card_injection_le__pair_scan_exits
      (Z * Z) Z
      (fun p => P (fst p) /\ B (snd p)) Q
      (@Finite_prod Z Z P B
        (finite_Z_range' 1 (hi - 1) chosen)
        (finite_Z_range 0 2))
      (finite_Z_range 0 hi)
      (fun p => fst p + snd p)) as Hinject.
  assert (Hmaps : forall p : Z * Z,
      (P (fst p) /\ B (snd p)) -> Q (fst p + snd p)).
  {
    intros [center bit] [[Hcenter _] Hbit].
    unfold Q, B in *; simpl in *; lia.
  }
  assert (Hone : forall x y : Z * Z,
      (P (fst x) /\ B (snd x)) ->
      (P (fst y) /\ B (snd y)) ->
      fst x + snd x = fst y + snd y -> x = y).
  {
    intros xpair ypair Hxpair Hypair Heq.
    destruct xpair as (x, bx).
    destruct ypair as (y, yb).
    destruct Hxpair as [[Hxrange Hx] Hbx].
    destruct Hypair as [[Hyrange Hy] Hby].
    unfold B in Hbx, Hby.
    simpl in *.
    destruct (Z.eq_dec x y) as [-> | Hxy].
    - f_equal; lia.
    - specialize (Hseparated x y Hx Hy Hxy).
      destruct (Z_le_gt_dec 0 (x - y)) as [Hdiff | Hdiff].
      + rewrite Z.abs_eq in Hseparated by exact Hdiff.
        exfalso; lia.
      + rewrite Z.abs_neq in Hseparated by lia.
        exfalso; lia.
  }
  specialize (Hinject Hmaps Hone).
  unfold P, B, Q in Hinject.
  rewrite (@set_card_product__pair_scan_exits
    Z Z
    (fun center : Z => 1 <= center < hi - 1 /\ chosen center)
    (fun bit : Z => 0 <= bit < 2)
    (finite_Z_range' 1 (hi - 1) chosen)
    (finite_Z_range 0 2)) in Hinject.
  rewrite (set_card_Z_range__pair_scan_exits 0 2) in Hinject by lia.
  rewrite (set_card_Z_range__pair_scan_exits 0 hi) in Hinject by lia.
  unfold P.
  lia.
Qed.
Lemma pair_savings_prefix_bounds__pair_scan_exits :
  forall a hi savings,
    0 <= hi ->
    PairSavingsPrefix a hi savings ->
    0 <= savings /\ 2 * savings <= hi.
Proof.
  intros a hi savings Hhi Hprefix.
  unfold PairSavingsPrefix, max_value_of_subset,
    max_object_of_subset in Hprefix.
  destruct Hprefix as [chosen [[Hselected Hmax] Hvalue]].
  subst savings.
  split.
  - apply set_card_nonnegative__pair_scan_exits.
  - exact (pair_selection_count_bound__pair_scan_exits
      a hi chosen Hhi Hselected).
Qed.
Lemma pair_scan_finish__pair_scan_exit :
  forall a hi committed pending savings,
    0 <= hi ->
    PairSavingsScan a hi committed pending savings ->
    savings = committed + pending / 2 /\
    PairSavingsPrefix a hi savings /\
    0 <= savings /\ 2 * savings <= hi.
Proof.
  intros a hi committed pending savings Hhi Hscan.
  unfold PairSavingsScan in Hscan.
  destruct Hscan as [Hvalue [Hpending Hprefix]].
  pose proof
    (pair_savings_prefix_bounds__pair_scan_exits
      a hi savings Hhi Hprefix) as Hbounds.
  tauto.
Qed.
Lemma non_one_pair_center_cross_one__pair_scan_exit :
  forall a hi center,
    Znth hi a 0 = 1 ->
    (NonOnePairCenter a (hi + 1) center <->
     NonOnePairCenter a hi center).
Proof.
  intros a hi center Hone.
  unfold NonOnePairCenter.
  split.
  - intros [Hrange [Hleft [Hcenter [Hright [Hedge1 Hedge2]]]]].
    split.
    + destruct (Z.eq_dec center (hi - 1)) as [Heq | Hneq].
      * exfalso. apply Hright. rewrite Heq. replace (hi - 1 + 1) with hi by lia.
        exact Hone.
      * lia.
    + exact (conj Hleft
        (conj Hcenter (conj Hright (conj Hedge1 Hedge2)))).
  - intros [Hrange Hrest].
    split; [lia | exact Hrest].
Qed.
Lemma pair_center_selection_cross_one__pair_scan_exit :
  forall a hi chosen,
    Znth hi a 0 = 1 ->
    (PairCenterSelection a (hi + 1) chosen <->
     PairCenterSelection a hi chosen).
Proof.
  intros a hi chosen Hone.
  unfold PairCenterSelection.
  split; intros [Hvalid Hsep]; split; try exact Hsep;
    intros center Hchosen.
  - apply (proj1
      (non_one_pair_center_cross_one__pair_scan_exit
        a hi center Hone)).
    apply Hvalid. exact Hchosen.
  - apply (proj2
      (non_one_pair_center_cross_one__pair_scan_exit
        a hi center Hone)).
    apply Hvalid. exact Hchosen.
Qed.
Lemma pair_center_count_cross_one__pair_scan_exit :
  forall a hi chosen,
    Znth hi a 0 = 1 ->
    (PairCenterSelection a hi chosen \/
     PairCenterSelection a (hi + 1) chosen) ->
    #(fun center : Z => 1 <= center < hi - 1 /\ chosen center) =
    #(fun center : Z => 1 <= center < hi + 1 - 1 /\ chosen center).
Proof.
  intros a hi chosen Hone Hselection.
  apply set_card_iff__exam_bridge.
  intros center.
  split.
  - intros [Hrange Hchosen]. split; [lia | exact Hchosen].
  - intros [Hrange Hchosen].
    split; [| exact Hchosen].
    destruct Hselection as [Hselection | Hselection].
    + specialize ((proj1 Hselection) center Hchosen) as Hold.
      unfold NonOnePairCenter in Hold. tauto.
    + specialize ((proj1 Hselection) center Hchosen) as Hnew.
      pose proof (proj1
        (non_one_pair_center_cross_one__pair_scan_exit
          a hi center Hone) Hnew) as Hold.
      unfold NonOnePairCenter in Hold. tauto.
Qed.
Lemma pair_prefix_cross_one__pair_scan_exit :
  forall a hi savings,
    Znth hi a 0 = 1 ->
    PairSavingsPrefix a hi savings ->
    PairSavingsPrefix a (hi + 1) savings.
Proof.
  intros a hi savings Hone Hprefix.
  unfold PairSavingsPrefix, max_value_of_subset, max_object_of_subset in *.
  destruct Hprefix as [chosen [[Hselected Hmax] Hvalue]].
  exists chosen.
  split.
  - split.
    + apply (proj2
        (pair_center_selection_cross_one__pair_scan_exit
          a hi chosen Hone)). exact Hselected.
    + intros other Hother.
      pose proof (proj1
        (pair_center_selection_cross_one__pair_scan_exit
          a hi other Hone) Hother) as Hotherold.
      specialize (Hmax other Hotherold).
      rewrite <- (pair_center_count_cross_one__pair_scan_exit
        a hi other Hone (or_intror Hother)).
      rewrite <- (pair_center_count_cross_one__pair_scan_exit
        a hi chosen Hone (or_introl Hselected)).
      exact Hmax.
  - rewrite <- (pair_center_count_cross_one__pair_scan_exit
      a hi chosen Hone (or_introl Hselected)).
    exact Hvalue.
Qed.
Lemma pair_selection_coprime_edge_bound__block_scan_init :
  forall a chosen,
    PairCenterSelection a (Zlength a) chosen ->
    2 * #(fun center : Z =>
      1 <= center < Zlength a - 1 /\ chosen center) <=
    #(fun edge : Z =>
      0 <= edge < Zlength a - 1 /\ AdjacentCoprime a edge).
Proof.
  intros a chosen [Hvalid Hseparated].
  set (P := fun center : Z =>
    1 <= center < Zlength a - 1 /\ chosen center).
  set (B := fun bit : Z => 0 <= bit < 2).
  set (Q := fun edge : Z =>
    0 <= edge < Zlength a - 1 /\ AdjacentCoprime a edge).
  pose proof
    (@set_card_injection_le__pair_scan_exits
      (Z * Z) Z
      (fun p => P (fst p) /\ B (snd p)) Q
      (@Finite_prod Z Z P B
        (finite_Z_range' 1 (Zlength a - 1) chosen)
        (finite_Z_range 0 2))
      (finite_Z_range' 0 (Zlength a - 1) (AdjacentCoprime a))
      (fun p => fst p - 1 + snd p)) as Hinject.
  assert (Hmaps : forall p : Z * Z,
      (P (fst p) /\ B (snd p)) -> Q (fst p - 1 + snd p)).
  {
    intros [center bit] [[Hrange Hchosen] Hbit].
    unfold Q, B in *; simpl in *.
    specialize (Hvalid center Hchosen).
    unfold NonOnePairCenter in Hvalid.
    destruct Hvalid as [_ [_ [_ [_ [Hleft Hright]]]]].
    destruct (Z.eq_dec bit 0) as [-> | Hbit0].
    - replace (center - 1 + 0) with (center - 1) by lia.
      split; [lia | exact Hleft].
    - assert (bit = 1) by lia. subst bit.
      replace (center - 1 + 1) with center by lia.
      split; [lia | exact Hright].
  }
  assert (Hone : forall x y : Z * Z,
      (P (fst x) /\ B (snd x)) ->
      (P (fst y) /\ B (snd y)) ->
      fst x - 1 + snd x = fst y - 1 + snd y -> x = y).
  {
    intros [x bx] [y b_y] [[Hxrange Hx] Hbx] [[Hyrange Hy] Hb_y] Heq.
    unfold B in Hbx, Hb_y; simpl in *.
    destruct (Z.eq_dec x y) as [-> | Hxy].
    - f_equal; lia.
    - specialize (Hseparated x y Hx Hy Hxy).
      destruct (Z_le_gt_dec 0 (x - y)) as [Hdiff | Hdiff].
      + rewrite Z.abs_eq in Hseparated by exact Hdiff.
        exfalso; lia.
      + rewrite Z.abs_neq in Hseparated by lia.
        exfalso; lia.
  }
  specialize (Hinject Hmaps Hone).
  unfold P, B, Q in Hinject.
  rewrite (@set_card_product__pair_scan_exits
    Z Z
    (fun center : Z => 1 <= center < Zlength a - 1 /\ chosen center)
    (fun bit : Z => 0 <= bit < 2)
    (finite_Z_range' 1 (Zlength a - 1) chosen)
    (finite_Z_range 0 2)) in Hinject.
  rewrite (set_card_Z_range__pair_scan_exits 0 2) in Hinject by lia.
  rewrite Z.mul_comm.
  exact Hinject.
Qed.
Lemma canonical_interior_one_run_prefix_empty__block_scan_init :
  forall a, CanonicalInteriorOneRunPrefix a 0 (@nil Z).
Proof.
  intros a.
  unfold CanonicalInteriorOneRunPrefix.
  exists (@nil Z).
  split; [reflexivity |].
  split; [apply mono_inc_nil |].
  split.
  - intros q Hq. rewrite Zlength_nil in Hq. lia.
  - intros lo hi Hblock Hhi.
    unfold InteriorOneBlock in Hblock. lia.
Qed.
Lemma joint_pair_block_empty__block_scan_init :
  forall a base_sad pair_savings,
    CoprimeEdgePrefixCount a (Zlength a - 1) base_sad ->
    PairSavingsPrefix a (Zlength a) pair_savings ->
    0 <= pair_savings ->
    JointPairBlockPrefix a 0 base_sad pair_savings (@nil Z).
Proof.
  intros a base_sad pair_savings Hsad Hpair Hnonneg.
  unfold PairSavingsPrefix, max_value_of_subset,
    max_object_of_subset in Hpair.
  destruct Hpair as [chosen [[Hselection Hmax] Hvalue]].
  unfold CoprimeEdgePrefixCount in Hsad.
  assert (Hbound : 2 * pair_savings <= base_sad).
  {
    rewrite Hsad, <- Hvalue.
    exact (pair_selection_coprime_edge_bound__block_scan_init
      a chosen Hselection).
  }
  unfold JointPairBlockPrefix.
  split.
  - unfold PairSavingsPrefix, max_value_of_subset, max_object_of_subset.
    exists chosen. split; [split; assumption | exact Hvalue].
  - split.
    + apply canonical_interior_one_run_prefix_projects.
      apply canonical_interior_one_run_prefix_empty__block_scan_init.
    + split; [exact Hnonneg |].
      split; [constructor |].
      split.
      * unfold ListLib.sum. cbn.
        rewrite Z.add_0_r. cbn in Hbound. exact Hbound.
      *
      exists chosen, (@nil Z).
      split; [exact Hselection |].
      split; [exact Hvalue |].
      split; [reflexivity |].
      split; [exact I |].
      split.
      -- intros q [Hq0 Hq1]. rewrite Zlength_nil in Hq1. lia.
      -- intros center q Hchosen [Hq0 Hq1].
        rewrite Zlength_nil in Hq1. lia.
Qed.
Lemma canonical_block_prefix_advance_nonone__block_scan_init :
  forall a limit lengths,
    CanonicalInteriorOneRunPrefix a limit lengths ->
    Znth limit a 0 <> 1 ->
    CanonicalInteriorOneRunPrefix a (limit + 1) lengths.
Proof.
  intros a limit lengths Hprefix Hnonone.
  destruct Hprefix as
      [starts [Hlength [Hincreasing [Hblocks Hcomplete]]]].
  exists starts.
  split; [exact Hlength |].
  split; [exact Hincreasing |].
  split.
  - intros q Hq.
    specialize (Hblocks q Hq).
    destruct Hblocks as [Hblock Hend].
    split; [exact Hblock | lia].
  - intros lo hi Hblock Hend.
    destruct (Z_lt_ge_dec limit hi) as [Hlt | Hle].
    + assert (hi = limit + 1) by lia.
      subst hi.
      exfalso.
      apply Hnonone.
      destruct Hblock as [Hlo [_ [_ [_ Hallone]]]].
      apply Hallone.
      lia.
    + apply Hcomplete; [exact Hblock | lia].
Qed.
Lemma canonical_one_run_scan_state_step__block_scan_init :
  forall a lo next lengths,
    CanonicalOneRunScanState a lo next lengths ->
    Znth next a 0 = 1 ->
    CanonicalOneRunScanState a lo (next + 1) lengths.
Proof.
  intros a lo next lengths [Hprefix Hscan] Hnext.
  split.
  - exact Hprefix.
  - intros j Hj.
    destruct (Z.eq_dec j next) as [-> | Hneq].
    + exact Hnext.
    + apply Hscan. lia.
Qed.
Lemma in_as_Znth__block_scan_steps_a :
  forall {A : Type} (l : list A) (x d : A),
    In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  destruct (In_nth l x d Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma canonical_run_append_closed__block_scan_steps_a :
  forall a lo hi lengths,
    0 < lo < hi ->
    hi < Zlength a ->
    Znth (lo - 1) a 0 <> 1 ->
    Znth hi a 0 <> 1 ->
    CanonicalOneRunScanState a lo hi lengths ->
    CanonicalInteriorOneRunPrefix a hi (lengths ++ [hi - lo]).
Proof.
  intros a lo hi lengths Hlohi Hhibound Hleft Hright Hstate.
  destruct Hstate as [Hprefix Hones].
  unfold CanonicalInteriorOneRunPrefix in *.
  destruct Hprefix as [starts [Hlen [Hinc [Hblocks Hcomplete]]]].
  exists (starts ++ [lo]).
  split.
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
  - split.
    + apply (proj2 (mono_inc_iff_ind (starts ++ [lo]))).
      apply (proj2 (mono_inc_ind_app starts [lo])).
      split.
      * apply (proj1 (mono_inc_iff_ind starts)). exact Hinc.
      * split.
        -- apply (proj1 (mono_inc_iff_ind [lo])). apply mono_inc_single.
        -- intros x y Hxin Hyin.
           simpl in Hyin. destruct Hyin as [-> | []].
           destruct (in_as_Znth__block_scan_steps_a starts x 0 Hxin)
             as [q [Hq Hqx]].
           assert (0 <= q < Zlength lengths) by lia.
           specialize (Hblocks q H) as [Hblock Hend].
           unfold InteriorOneBlock in Hblock.
           rewrite Hqx in Hblock, Hend. lia.
    + split.
      * intros q Hq.
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
        destruct (Z_lt_ge_dec q (Zlength lengths)) as [Holdq | Hnewq].
        -- rewrite !app_Znth1 by lia.
           specialize (Hblocks q ltac:(lia)) as [Hblock Hend].
           split; [exact Hblock | lia].
        -- assert (q = Zlength lengths) by lia. subst q.
           rewrite !app_Znth2 by lia.
           replace (Zlength lengths - Zlength starts) with 0 by lia.
           replace (Zlength lengths - Zlength lengths) with 0 by lia.
           rewrite !Znth0_cons.
           split.
           ++ unfold InteriorOneBlock.
              split; [lia |].
              split; [lia |].
              split; [exact Hleft |].
              split.
              ** replace (lo + (hi - lo)) with hi by lia. exact Hright.
              ** intros j Hj. apply Hones. lia.
           ++ lia.
      * intros block_lo block_hi Hblock Hlimit.
        destruct (Z_le_gt_dec block_hi lo) as [Hold | Hnew].
        -- destruct (Hcomplete block_lo block_hi Hblock Hold)
             as [q [Hq [Hstart Hlength]]].
           exists q.
           rewrite Zlength_app, Zlength_cons, Zlength_nil.
           split; [lia |].
           rewrite !app_Znth1 by lia. auto.
        -- assert (Hsame_lo : block_lo = lo).
           {
             unfold InteriorOneBlock in Hblock.
             destruct Hblock as
               [Hblockbounds [Hblockhi [Hblockleft [Hblockright Hblockones]]]].
             destruct (Z_lt_ge_dec block_lo lo) as [Hlt | Hge].
             - exfalso. apply Hleft. apply Hblockones. lia.
             - destruct (Z.eq_dec block_lo lo) as [Heq | Hneq]; auto.
               exfalso. apply Hblockleft. apply Hones. lia.
           }
           assert (Hsame_hi : block_hi = hi).
           {
             subst block_lo.
             unfold InteriorOneBlock in Hblock.
             destruct Hblock as
               [Hblockbounds [Hblockhi [Hblockleft [Hblockright Hblockones]]]].
             destruct (Z.eq_dec block_hi hi) as [Heq | Hneq]; auto.
             exfalso. apply Hblockright. apply Hones. lia.
           }
           subst block_lo block_hi.
           exists (Zlength lengths).
           rewrite Zlength_app, Zlength_cons, Zlength_nil.
           pose proof (Zlength_nonneg lengths).
           split; [lia |].
           rewrite !app_Znth2 by lia.
           replace (Zlength lengths - Zlength starts) with 0 by lia.
           replace (Zlength lengths - Zlength lengths) with 0 by lia.
           rewrite !Znth0_cons. auto.
Qed.
Lemma canonical_run_nonone_step__block_scan_steps_a :
  forall a limit lengths,
    CanonicalInteriorOneRunPrefix a limit lengths ->
    Znth limit a 0 <> 1 ->
    CanonicalInteriorOneRunPrefix a (limit + 1) lengths.
Proof.
  intros a limit lengths Hprefix Hnonone.
  destruct Hprefix as [starts [Hlength [Hinc [Hblocks Hcomplete]]]].
  exists starts.
  split; [exact Hlength |].
  split; [exact Hinc |].
  split.
  - intros q Hq.
    specialize (Hblocks q Hq) as [Hblock Hend].
    split; [exact Hblock | lia].
  - intros lo hi Hblock Hend.
    destruct (Z_lt_ge_dec limit hi) as [Hlt | Hle].
    + assert (hi = limit + 1) by lia. subst hi.
      exfalso. apply Hnonone.
      destruct Hblock as [Hlo [_ [_ [_ Hallone]]]].
      apply Hallone. lia.
    + apply Hcomplete; [exact Hblock | lia].
Qed.
Lemma canonical_run_trailing_close__block_scan_steps_a :
  forall a lo next lengths,
    lo <= next ->
    Zlength a <= next ->
    CanonicalOneRunScanState a lo next lengths ->
    CanonicalInteriorOneRunPrefix a next lengths.
Proof.
  intros a lo next lengths Hlo Hend Hscan.
  destruct Hscan as [Hprefix Hones].
  destruct Hprefix as [starts [Hlength [Hinc [Hsound Hcomplete]]]].
  exists starts.
  split; [exact Hlength |].
  split; [exact Hinc |].
  split.
  - intros q Hq. specialize (Hsound q Hq) as [Hblock Hlimit].
    split; [exact Hblock | lia].
  - intros block_lo block_hi Hblock Hhi.
    destruct (Z_le_gt_dec block_hi lo) as [Hbefore | Hafter].
    + apply Hcomplete; assumption.
    + exfalso.
      destruct Hblock as
        [[Hblock_lo_pos Hblock_nonempty]
         [Hblock_hi_len [Hleft_boundary [Hright_boundary Hall_ones]]]].
      apply Hright_boundary. apply Hones. lia.
Qed.
Lemma canonical_run_leading_close__block_scan_steps_a :
  forall a lo next lengths,
    lo <= next ->
    lo <= 0 ->
    CanonicalOneRunScanState a lo next lengths ->
    CanonicalInteriorOneRunPrefix a next lengths.
Proof.
  intros a lo next lengths Hlo Hleading Hscan.
  destruct Hscan as [Hprefix Hones].
  destruct Hprefix as [starts [Hlength [Hinc [Hsound Hcomplete]]]].
  exists starts.
  split; [exact Hlength |].
  split; [exact Hinc |].
  split.
  - intros q Hq. specialize (Hsound q Hq) as [Hblock Hlimit].
    split; [exact Hblock | lia].
  - intros block_lo block_hi Hblock Hhi.
    destruct (Z_le_gt_dec block_hi lo) as [Hbefore | Hafter].
    + apply Hcomplete; assumption.
    + exfalso.
      destruct Hblock as
        [[Hblock_lo_pos Hblock_nonempty]
         [Hblock_hi_len [Hleft_boundary [Hright_boundary Hall_ones]]]].
      apply Hleft_boundary. apply Hones. lia.
Qed.
Lemma canonical_run_state_step__block_scan_steps_a :
  forall a lo next lengths,
    CanonicalOneRunScanState a lo next lengths ->
    Znth next a 0 = 1 ->
    CanonicalOneRunScanState a lo (next + 1) lengths.
Proof.
  intros a lo next lengths [Hprefix Hscan] Hnext.
  split; [exact Hprefix |].
  intros j Hj.
  destruct (Z.eq_dec j next) as [-> | Hneq].
  - exact Hnext.
  - apply Hscan. lia.
Qed.
Lemma canonical_run_full_completion_fuel__block_scan_steps_a :
  forall (fuel : nat) a n lo next lengths,
    n = Zlength a ->
    0 <= lo -> lo <= next -> next <= n ->
    (lo = 0 \/ Znth (lo - 1) a 0 <> 1) ->
    CanonicalOneRunScanState a lo next lengths ->
    (Z.to_nat (n - next) <= fuel)%nat ->
    exists future,
      CanonicalInteriorOneRunPrefix a n (lengths ++ future).
Proof.
  induction fuel as [|fuel IH];
    intros a n lo next lengths Hn Hlo Hlonext Hnextn Hleft Hscan Hfuel.
  - destruct (Z.eq_dec next n) as [-> | Hneq].
    + exists nil. rewrite app_nil_r.
      eapply canonical_run_trailing_close__block_scan_steps_a; eauto. lia.
    + assert (next < n) by lia.
      assert ((0 < Z.to_nat (n - next))%nat).
      { apply Nat2Z.inj_lt. simpl. rewrite Z2Nat.id by lia. lia. }
      lia.
  - destruct (Z.eq_dec next n) as [-> | Hneq].
    + exists nil. rewrite app_nil_r.
      eapply canonical_run_trailing_close__block_scan_steps_a; eauto. lia.
    + assert (Hnextlt : next < n) by lia.
      assert (Hfuel' : (Z.to_nat (n - (next + 1)) <= fuel)%nat).
      {
        apply Nat2Z.inj_le.
        rewrite Z2Nat.id by lia.
        pose proof ((proj1 (Nat2Z.inj_le _ _)) Hfuel) as H.
        rewrite Z2Nat.id in H by lia.
        rewrite Nat2Z.inj_succ in H. lia.
      }
      destruct (Z.eq_dec (Znth next a 0) 1) as [Hone | Hnonone].
      * eapply IH with (lo := lo) (next := next + 1)
          (lengths := lengths); eauto; try lia.
        eapply canonical_run_state_step__block_scan_steps_a; eauto.
      * destruct Hscan as [Hprefix Hones].
        destruct (Z.eq_dec lo 0) as [-> | Hlozero].
        -- assert (Hclosed : CanonicalInteriorOneRunPrefix a next lengths).
           {
             eapply canonical_run_leading_close__block_scan_steps_a
               with (lo := 0); eauto; try lia. split; assumption.
           }
           assert (Hnextprefix :
             CanonicalInteriorOneRunPrefix a (next + 1) lengths).
           { eapply canonical_run_nonone_step__block_scan_steps_a; eauto. }
           eapply IH with (lo := next + 1) (next := next + 1)
             (lengths := lengths); eauto; try lia.
           ++ right. replace (next + 1 - 1) with next by lia. exact Hnonone.
           ++ split; [exact Hnextprefix |]. intros j Hj. lia.
        -- destruct (Z.eq_dec lo next) as [-> | Hloneq].
           ++ assert (Hnextprefix :
                CanonicalInteriorOneRunPrefix a (next + 1) lengths).
              { eapply canonical_run_nonone_step__block_scan_steps_a; eauto. }
              eapply IH with (lo := next + 1) (next := next + 1)
                (lengths := lengths); eauto; try lia.
              ** right. replace (next + 1 - 1) with next by lia. exact Hnonone.
              ** split; [exact Hnextprefix |]. intros j Hj. lia.
           ++ assert (Hclosed : CanonicalInteriorOneRunPrefix a next
                (lengths ++ [next - lo])).
              {
                eapply canonical_run_append_closed__block_scan_steps_a.
                - lia.
                - lia.
                - destruct Hleft as [Heq | Hleft]; [contradiction | exact Hleft].
                - exact Hnonone.
                - split; assumption.
              }
              assert (Hnextprefix : CanonicalInteriorOneRunPrefix a (next + 1)
                (lengths ++ [next - lo])).
              { eapply canonical_run_nonone_step__block_scan_steps_a; eauto. }
              destruct (IH a n (next + 1) (next + 1)
                (lengths ++ [next - lo]) Hn ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(right; replace (next + 1 - 1) with next by lia;
                  exact Hnonone)
                ltac:(split; [exact Hnextprefix |]; intros j Hj; lia)
                Hfuel') as [future Hfuture].
              exists ((next - lo) :: future).
              rewrite <- app_assoc in Hfuture. simpl in Hfuture. exact Hfuture.
Qed.
Lemma canonical_run_full_completion__block_scan_steps_a :
  forall a n lo next lengths,
    n = Zlength a ->
    0 <= lo -> lo <= next -> next <= n ->
    (lo = 0 \/ Znth (lo - 1) a 0 <> 1) ->
    CanonicalOneRunScanState a lo next lengths ->
    exists future,
      CanonicalInteriorOneRunPrefix a n (lengths ++ future).
Proof.
  intros a n lo next lengths Hn Hlo Hlonext Hnextn Hleft Hscan.
  eapply canonical_run_full_completion_fuel__block_scan_steps_a
    with (fuel := Z.to_nat (n - next)); eauto.
Qed.
Lemma joint_run_close_no_record__block_scan_steps_a :
  forall a lo next base_sad pair_savings block_lengths,
    lo <= next ->
    (lo <= 0 \/ Zlength a <= next) ->
    CanonicalOneRunScanState a lo next block_lengths ->
    JointPairBlockPrefix a lo base_sad pair_savings block_lengths ->
    JointPairBlockPrefix a next base_sad pair_savings block_lengths.
Proof.
  intros a lo next base_sad pair_savings block_lengths Hlo Hboundary Hscan Hjoint.
  destruct Hjoint as
    [Hpair [Hprefix [Hpair_nonneg [Hlengths_pos [Hbound
      [centres [starts [Hselection [Hcard [Hlen [Hinc [Hsound Hdisjoint]]]]]]]]]]]].
  repeat split; try assumption.
  - apply canonical_interior_one_run_prefix_projects.
    destruct Hboundary as [Hleading | Hend].
    + exact (canonical_run_leading_close__block_scan_steps_a
        a lo next block_lengths Hlo Hleading Hscan).
    + exact (canonical_run_trailing_close__block_scan_steps_a
        a lo next block_lengths Hlo Hend Hscan).
  - exists centres, starts.
    split; [exact Hselection |].
    split; [exact Hcard |].
    split; [exact Hlen |].
    split; [exact Hinc |].
    split.
    + intros q Hq. specialize (Hsound q Hq) as [Hblock Hlimit].
      split; [exact Hblock | lia].
    + exact Hdisjoint.
Qed.
Lemma joint_run_completed_append__block_scan_steps_a :
  forall a lo hi base_sad pair_savings block_lengths,
    0 < lo < hi ->
    hi < Zlength a ->
    Znth (lo - 1) a 0 <> 1 ->
    Znth hi a 0 <> 1 ->
    CanonicalOneRunScanState a lo hi block_lengths ->
    JointPairBlockPrefix a lo base_sad pair_savings block_lengths ->
    CanonicalExamBlockCollectionCertificate
      a base_sad pair_savings block_lengths ->
    JointPairBlockPrefix a hi base_sad pair_savings
      (block_lengths ++ [hi - lo]).
Proof.
  intros a lo hi base_sad pair_savings block_lengths Hlohi Hhibound
    Hleft Hright Hscan Hjoint Hcert.
  assert (Hnewcanonical : CanonicalInteriorOneRunPrefix a hi
    (block_lengths ++ [hi - lo])).
  { eapply canonical_run_append_closed__block_scan_steps_a; eauto. }
  assert (Hnextprefix : CanonicalInteriorOneRunPrefix a (hi + 1)
    (block_lengths ++ [hi - lo])).
  { eapply canonical_run_nonone_step__block_scan_steps_a; eauto. }
  assert (Hnextscan : CanonicalOneRunScanState a (hi + 1) (hi + 1)
    (block_lengths ++ [hi - lo])).
  { split; [exact Hnextprefix |]. intros j Hj. lia. }
  destruct (canonical_run_full_completion__block_scan_steps_a
    a (Zlength a) (hi + 1) (hi + 1)
    (block_lengths ++ [hi - lo]) eq_refl ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(right; replace (hi + 1 - 1) with hi by lia;
      exact Hright) Hnextscan) as [future Hfullprofile].
  pose proof (canonical_exam_block_collection_certificate_append
    a base_sad pair_savings block_lengths (hi - lo) Hcert) as Hnewcert.
  specialize (Hnewcert future Hfullprofile).
  destruct Hnewcert as [Hfulljoint Hexchange].
  destruct Hfulljoint as [_ [_ [_ [Hfullpositive [Hfullbound _]]]]].
  apply Forall_app in Hfullpositive.
  destruct Hfullpositive as [Hnewpositive Hfuturepositive].
  rewrite map_app, ListLib.sum_app in Hfullbound.
  assert (Hfuture_nonnegative :
    0 <= ListLib.sum (map (fun len : Z => len + 1) future)).
  {
    assert (forall xs : list Z,
      Forall (fun len : Z => 1 <= len) xs ->
      0 <= ListLib.sum (map (fun len : Z => len + 1) xs))
      as Hsum_nonnegative.
    {
      intros xs Hpositive. induction Hpositive; simpl; lia.
    }
    apply Hsum_nonnegative. exact Hfuturepositive.
  }
  destruct Hjoint as
    [Hpair [Holdprefix [Hpair_nonneg [Holdpositive [Holdbound
      [centres [starts [Hselection [Hcard [Hlen [Hinc
        [Hsound Hdisjoint]]]]]]]]]]]].
  repeat split.
  - exact Hpair.
  - apply canonical_interior_one_run_prefix_projects. exact Hnewcanonical.
  - exact Hpair_nonneg.
  - exact Hnewpositive.
  - lia.
  - exists centres, (starts ++ [lo]).
    split; [exact Hselection |].
    split; [exact Hcard |].
    split.
    + rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
    + split.
      * apply (proj2 (increasing_app starts [lo])).
        split; [exact Hinc |].
        split.
        -- simpl; auto.
        -- intros x y Hxin Hyin.
           simpl in Hyin. destruct Hyin as [-> | []].
           destruct (in_as_Znth__block_scan_steps_a starts x 0 Hxin)
             as [q [Hq Hqx]].
           assert (0 <= q < Zlength block_lengths) by lia.
           specialize (Hsound q H) as [Hblock Hend].
           unfold InteriorOneBlock in Hblock.
           rewrite Hqx in Hblock, Hend. lia.
      * split.
        -- intros q Hq.
           rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
           destruct (Z_lt_ge_dec q (Zlength block_lengths))
             as [Holdq | Hnewq].
           ++ rewrite !app_Znth1 by lia.
              specialize (Hsound q ltac:(lia)) as [Hblock Hend].
              split; [exact Hblock | lia].
           ++ assert (q = Zlength block_lengths) by lia. subst q.
              rewrite !app_Znth2 by lia.
              replace (Zlength block_lengths - Zlength starts) with 0 by lia.
              replace (Zlength block_lengths - Zlength block_lengths)
                with 0 by lia.
              rewrite !Znth0_cons.
              split.
              ** unfold InteriorOneBlock.
                 split; [lia |]. split; [lia |]. split; [exact Hleft |].
                 split.
                 --- replace (lo + (hi - lo)) with hi by lia. exact Hright.
                 --- intros j Hj. destruct Hscan as [_ Hones]. apply Hones. lia.
              ** lia.
        -- intros center q Hcentre Hq.
           rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
           destruct (Z_lt_ge_dec q (Zlength block_lengths))
             as [Holdq | Hnewq].
           ++ rewrite !app_Znth1 by lia.
              apply Hdisjoint; [exact Hcentre | lia].
           ++ assert (q = Zlength block_lengths) by lia. subst q.
              rewrite !app_Znth2 by lia.
              replace (Zlength block_lengths - Zlength starts) with 0 by lia.
              replace (Zlength block_lengths - Zlength block_lengths)
                with 0 by lia.
              rewrite !Znth0_cons.
              replace (lo + (hi - lo)) with hi by lia.
              destruct (Z_lt_ge_dec center (lo - 1)) as [Hbefore | Hafter].
              ** left. exact Hbefore.
              ** destruct (Z_lt_ge_dec hi center) as [Hafterblock | Hinside].
                 --- right. exact Hafterblock.
                 --- exfalso.
                     destruct Hselection as [Hselected Hseparated].
                     specialize (Hselected center Hcentre).
                     unfold NonOnePairCenter in Hselected.
                     destruct Hselected as
                       [Hcenterbounds [Hcenterleft [Hcentervalue
                         [Hcenterright [Hedgeleft Hedgeright]]]]].
                     destruct Hscan as [_ Hones].
                     destruct (Z_lt_ge_dec center lo) as [Hatleft | Hmiddle].
                     +++ assert (center = lo - 1) by lia. subst center.
                         apply Hcenterright.
                         replace (lo - 1 + 1) with lo by lia. apply Hones. lia.
                     +++ destruct (Z_lt_ge_dec center hi) as [Hmiddle' | Hatright].
                         *** apply Hcentervalue. apply Hones. lia.
                         *** assert (center = hi) by lia. subst center.
                             apply Hcenterleft. apply Hones. lia.
Qed.
Lemma canonical_run_close_boundary_no_record__block_scan_steps_b :
  forall a lo next lengths,
    lo <= next ->
    (lo <= 0 \/ Zlength a <= next) ->
    CanonicalOneRunScanState a lo next lengths ->
    CanonicalInteriorOneRunPrefix a next lengths.
Proof.
  intros a lo next lengths Hlo_next Hboundary Hscan.
  unfold CanonicalOneRunScanState in Hscan.
  destruct Hscan as [Hprefix Hones].
  unfold CanonicalInteriorOneRunPrefix in Hprefix |- *.
  destruct Hprefix as [starts [Hlength [Hincreasing [Hsound Hcomplete]]]].
  exists starts.
  split; [exact Hlength |].
  split; [exact Hincreasing |].
  split.
  - intros q Hq.
    specialize (Hsound q Hq) as [Hblock Hend].
    split; [exact Hblock | lia].
  - intros block_lo block_hi Hblock Hhi.
    destruct (Z_le_gt_dec block_hi lo) as [Hbefore | Hafter].
    + apply Hcomplete; assumption.
    + unfold InteriorOneBlock in Hblock.
      destruct Hblock as
        [[Hblock_lo_pos Hblock_nonempty]
         [Hblock_hi_len
          [Hleft_boundary [Hright_boundary Hall_ones]]]].
      destruct Hboundary as [Hleading | Hat_end].
      * exfalso.
        apply Hleft_boundary.
        apply Hones.
        lia.
      * exfalso.
        apply Hright_boundary.
        apply Hones.
        lia.
Qed.
Lemma canonical_run_skip_nonone__block_scan_steps_b :
  forall a limit lengths,
    CanonicalInteriorOneRunPrefix a limit lengths ->
    Znth limit a 0 <> 1 ->
    CanonicalInteriorOneRunPrefix a (limit + 1) lengths.
Proof.
  intros a limit lengths Hprefix Hnonone.
  destruct Hprefix as
    [starts [Hlength [Hincreasing [Hblocks Hcomplete]]]].
  exists starts.
  split; [exact Hlength |].
  split; [exact Hincreasing |].
  split.
  - intros q Hq.
    specialize (Hblocks q Hq) as [Hblock Hend].
    split; [exact Hblock | lia].
  - intros lo hi Hblock Hend.
    destruct (Z_lt_ge_dec limit hi) as [Hlt | Hle].
    + assert (hi = limit + 1) by lia.
      subst hi.
      exfalso.
      apply Hnonone.
      destruct Hblock as [Hlo [_ [_ [_ Hallone]]]].
      apply Hallone.
      lia.
    + apply Hcomplete; [exact Hblock | lia].
Qed.
Lemma joint_pair_block_close_boundary_no_record__block_scan_steps_b :
  forall a lo next base_sad pair_savings block_lengths,
    lo <= next ->
    (lo <= 0 \/ Zlength a <= next) ->
    CanonicalOneRunScanState a lo next block_lengths ->
    JointPairBlockPrefix a lo base_sad pair_savings block_lengths ->
    JointPairBlockPrefix a next base_sad pair_savings block_lengths.
Proof.
  intros a lo next base_sad pair_savings block_lengths Hlo_next Hboundary
    Hscan Hjoint.
  pose proof
    (canonical_run_close_boundary_no_record__block_scan_steps_b
      a lo next block_lengths Hlo_next Hboundary Hscan) as Hcanonical.
  pose proof
    (canonical_interior_one_run_prefix_projects
      a next block_lengths Hcanonical) as Hprefix.
  destruct Hjoint as
    [Hpair [_ [Hpair_nonneg [Hlengths_pos [Hbound
      [centres [starts [Hselection [Hcard [Hlen [Hinc
        [Hsound Hdisjoint]]]]]]]]]]]].
  repeat split; try assumption.
  exists centres, starts.
  split; [exact Hselection |].
  split; [exact Hcard |].
  split; [exact Hlen |].
  split; [exact Hinc |].
  split.
  - intros q Hq.
    specialize (Hsound q Hq) as [Hblock Hend].
    split; [exact Hblock | lia].
  - exact Hdisjoint.
Qed.
Lemma joint_pair_block_skip_nonone__block_scan_steps_b :
  forall a limit base_sad pair_savings block_lengths,
    CanonicalInteriorOneRunPrefix a limit block_lengths ->
    JointPairBlockPrefix a limit base_sad pair_savings block_lengths ->
    Znth limit a 0 <> 1 ->
    JointPairBlockPrefix a (limit + 1)
      base_sad pair_savings block_lengths.
Proof.
  intros a limit base_sad pair_savings block_lengths Hcanonical Hjoint
    Hnonone.
  pose proof
    (canonical_run_skip_nonone__block_scan_steps_b
      a limit block_lengths Hcanonical Hnonone) as Hnewcanonical.
  pose proof
    (canonical_interior_one_run_prefix_projects
      a (limit + 1) block_lengths Hnewcanonical) as Hprefix.
  destruct Hjoint as
    [Hpair [_ [Hpair_nonneg [Hlengths_pos [Hbound
      [centres [starts [Hselection [Hcard [Hlen [Hinc
        [Hsound Hdisjoint]]]]]]]]]]]].
  repeat split; try assumption.
  exists centres, starts.
  split; [exact Hselection |].
  split; [exact Hcard |].
  split; [exact Hlen |].
  split; [exact Hinc |].
  split.
  - intros q Hq.
    specialize (Hsound q Hq) as [Hblock Hend].
    split; [exact Hblock | lia].
  - exact Hdisjoint.
Qed.
Lemma set_card_Z_range_bounds_exam__final_result :
  forall (low high : Z) (P : Z -> Prop),
    low <= high ->
    0 <= #(fun z : Z => low <= z < high /\ P z) <= high - low.
Proof.
  intros low high P Hrange.
  rewrite set_card_Z_as_sum_exam__final_result.
  pose proof (SumLib.ZRange.sum_Z_range_bounds low high
    (fun z => if prop_dec (P z) then 1 else 0) 0 1 Hrange) as Hbounds.
  assert (Hpoint : forall z, low <= z < high ->
    0 <= (if prop_dec (P z) then 1 else 0) <= 1).
  {
    intros z Hz.
    destruct (prop_dec (P z)); lia.
  }
  specialize (Hbounds Hpoint).
  nia.
Qed.
Lemma exam_sadness_bounds__final_result :
  forall a sadness,
    1 <= Zlength a ->
    ExamSadness a sadness ->
    0 <= sadness < Zlength a.
Proof.
  intros a sadness Hlen Hsad.
  unfold ExamSadness in Hsad.
  rewrite Hsad.
  pose proof (set_card_Z_range_bounds_exam__final_result
    0 (Zlength a - 1)
    (fun i => Z.gcd (Znth i a 0) (Znth (i + 1) a 0) = 1)) as Hbounds.
  specialize (Hbounds ltac:(lia)).
  lia.
Qed.
Lemma sum_permutation__greedy_transition :
  forall xs ys : list Z,
    Permutation xs ys ->
    ListLib.sum xs = ListLib.sum ys.
Proof.
  intros xs ys Hperm.
  induction Hperm.
  - reflexivity.
  - simpl. rewrite IHHperm. reflexivity.
  - simpl. lia.
  - etransitivity; eauto.
Qed.
Lemma forall_positive_lowerbound__greedy_transition :
  forall xs : list Z,
    Forall (fun x => 1 <= x) xs ->
    ListLib.lowerbound 1 xs.
Proof.
  intros xs Hxs.
  induction xs as [|x xs IH].
  - simpl. exact I.
  - inversion Hxs; subst.
    simpl. split; [assumption |].
    apply IH. assumption.
Qed.
Lemma sum_nonnegative_lowerbound__greedy_transition :
  forall xs : list Z,
    ListLib.lowerbound 0 xs ->
    0 <= ListLib.sum xs.
Proof.
  intros xs Hxs.
  induction xs as [|x xs IH].
  - simpl. lia.
  - simpl in Hxs |- *.
    destruct Hxs as [Hx Hxs].
    specialize (IH Hxs).
    lia.
Qed.
Lemma map_succ_lowerbound_nonnegative__greedy_transition :
  forall xs : list Z,
    ListLib.lowerbound 1 xs ->
    ListLib.lowerbound 0 (map (fun x => x + 1) xs).
Proof.
  intros xs Hxs.
  induction xs as [|x xs IH].
  - simpl. exact I.
  - simpl in Hxs |- *.
    destruct Hxs as [Hx Hxs].
    split; [lia |].
    apply IH. exact Hxs.
Qed.
Lemma optimization_safety_remaining_bound__greedy_transition :
  forall sorted blocks i base pair_savings use budget remaining sadness,
    0 <= i ->
    i < Zlength sorted ->
    Permutation blocks sorted ->
    OptimizationSafetyBounds base pair_savings blocks ->
    use <= pair_savings ->
    GreedyBlockState sorted i budget (base - 2 * use) remaining sadness ->
    0 <= sadness - (Znth i sorted 0 + 1).
Proof.
  intros sorted blocks i base pair_savings use budget remaining sadness
    Hi Hiend Hperm Hsafe Huse Hstate.
  destruct Hsafe as [Hpair_nonneg [Hblocks_pos Htotal]].
  unfold GreedyBlockState in Hstate.
  destruct Hstate as [Hibounds [Hremaining [Hsadness Haffordable]]].
  assert (Hmapped_perm :
    Permutation (map (fun x => x + 1) blocks)
      (map (fun x => x + 1) sorted)).
  { apply Permutation_map. exact Hperm. }
  pose proof (sum_permutation__greedy_transition _ _ Hmapped_perm)
    as Hsum_perm.
  pose proof (forall_positive_lowerbound__greedy_transition _ Hblocks_pos)
    as Hblocks_lower.
  pose proof (ListLib.lowerbound_perm 1 blocks sorted Hperm Hblocks_lower)
    as Hsorted_lower.
  assert (Hsuffix_lower :
    ListLib.lowerbound 1 (sublist (i + 1) (Zlength sorted) sorted)).
  {
    apply ListLib.lowerbound_sublist_intro; try lia.
    intros j Hj.
    apply (ListLib.lowerbound_Znth 1 sorted j Hsorted_lower).
    lia.
  }
  pose proof
    (map_succ_lowerbound_nonnegative__greedy_transition _ Hsuffix_lower)
    as Hsuffix_map_lower.
  pose proof
    (sum_nonnegative_lowerbound__greedy_transition _ Hsuffix_map_lower)
    as Hsuffix_sum_nonneg.
  assert (Hfull_split :
    sorted = sublist 0 (i + 1) sorted ++
      sublist (i + 1) (Zlength sorted) sorted).
  {
    pose proof
      (sublist_split 0 (Zlength sorted) (i + 1) sorted
        ltac:(lia) ltac:(lia)) as Hsplit.
    rewrite (sublist_self sorted (Zlength sorted) eq_refl) in Hsplit.
    exact Hsplit.
  }
  assert (Hprefix_cost_bound :
    ListLib.sum
      (map (fun x => x + 1) (sublist 0 (i + 1) sorted)) <=
    ListLib.sum (map (fun x => x + 1) sorted)).
  {
    pose proof
      (f_equal (map (fun x : Z => x + 1)) Hfull_split) as Hmap_split.
    rewrite map_app in Hmap_split.
    pose proof (f_equal ListLib.sum Hmap_split) as Hsum_split.
    rewrite ListLib.sum_app in Hsum_split.
    lia.
  }
  rewrite Hsadness.
  assert (ListLib.sum (map (fun x => x + 1) sorted) <= base - 2 * use)
    by lia.
  assert (Hprefix_step :
    sublist 0 (i + 1) sorted =
      sublist 0 i sorted ++ [Znth i sorted 0]).
  {
    rewrite (sublist_split 0 (i + 1) i sorted) by lia.
    rewrite (sublist_single 0 i sorted) by lia.
    reflexivity.
  }
  rewrite Hprefix_step in Hprefix_cost_bound.
  rewrite map_app, ListLib.sum_app in Hprefix_cost_bound.
  simpl in Hprefix_cost_bound.
  lia.
Qed.
Lemma greedy_block_state_step__greedy_transition :
  forall sorted blocks i base pair_savings use budget remaining sadness,
    0 <= i ->
    i < Zlength sorted ->
    Permutation blocks sorted ->
    OptimizationSafetyBounds base pair_savings blocks ->
    use <= pair_savings ->
    GreedyBlockState sorted i budget (base - 2 * use) remaining sadness ->
    Znth i sorted 0 <= remaining ->
    1 <= Znth i sorted 0 /\
    0 <= sadness - (Znth i sorted 0 + 1) /\
    GreedyBlockState sorted (i + 1) budget (base - 2 * use)
      (remaining - Znth i sorted 0)
      (sadness - (Znth i sorted 0 + 1)).
Proof.
  intros sorted blocks i base pair_savings use budget remaining sadness
    Hi Hiend Hperm Hsafe Huse Hstate Hguard.
  destruct Hsafe as [Hpair_nonneg [Hblocks_pos Htotal]].
  pose proof (forall_positive_lowerbound__greedy_transition _ Hblocks_pos)
    as Hblocks_lower.
  pose proof (ListLib.lowerbound_perm 1 blocks sorted Hperm Hblocks_lower)
    as Hsorted_lower.
  pose proof (ListLib.lowerbound_Znth 1 sorted i Hsorted_lower ltac:(lia))
    as Hcurrent_pos.
  assert (Hsafe : OptimizationSafetyBounds base pair_savings blocks).
  { repeat split; assumption. }
  pose proof
    (optimization_safety_remaining_bound__greedy_transition
      sorted blocks i base pair_savings use budget remaining sadness
      Hi Hiend Hperm Hsafe Huse Hstate) as Hnew_sad_nonneg.
  unfold GreedyBlockState in Hstate.
  destruct Hstate as [Hibounds [Hremaining [Hsadness Haffordable]]].
  split; [exact Hcurrent_pos |].
  split; [exact Hnew_sad_nonneg |].
  unfold GreedyBlockState.
  repeat split.
  - lia.
  - lia.
  - rewrite Hremaining.
    rewrite (sublist_split 0 (i + 1) i sorted) by lia.
    rewrite (sublist_single 0 i sorted) by lia.
    rewrite ListLib.sum_app. simpl. lia.
  - rewrite Hsadness.
    rewrite (sublist_split 0 (i + 1) i sorted) by lia.
    rewrite (sublist_single 0 i sorted) by lia.
    rewrite map_app, ListLib.sum_app. simpl. lia.
  - intros j Hj.
    destruct (Z_lt_dec j i) as [Hji | Hji].
    + apply Haffordable. lia.
    + assert (j = i) by lia. subst j.
      rewrite Hremaining in Hguard.
      exact Hguard.
Qed.
Lemma greedy_block_state_zero__greedy_setup :
  forall sorted budget initial_sad,
    GreedyBlockState sorted 0 budget initial_sad budget initial_sad.
Proof.
  intros sorted budget initial_sad.
  unfold GreedyBlockState.
  change (sublist 0 0 sorted) with (@nil Z).
  simpl.
  pose proof (Zlength_nonneg sorted).
  repeat split; intros; lia.
Qed.
Lemma greedy_block_state_step__greedy_loop :
  forall sorted blocks i base pair_savings use budget remaining sadness,
    0 <= i ->
    i < Zlength sorted ->
    Permutation blocks sorted ->
    OptimizationSafetyBounds base pair_savings blocks ->
    use <= pair_savings ->
    GreedyBlockState sorted i budget (base - 2 * use) remaining sadness ->
    Znth i sorted 0 <= remaining ->
    1 <= Znth i sorted 0 /\
    0 <= sadness - (Znth i sorted 0 + 1) /\
    GreedyBlockState sorted (i + 1) budget (base - 2 * use)
      (remaining - Znth i sorted 0)
      (sadness - (Znth i sorted 0 + 1)).
Proof.
  intros.
  eapply greedy_block_state_step__greedy_transition; eauto.
Qed.
Lemma greedy_final_result_from_scalar_updates__greedy_loop :
  forall remaining sadness out,
    (remaining <= sadness /\ out = sadness - remaining) \/
    (sadness < remaining /\ out = 0) ->
    FinalBudgetResult remaining sadness out.
Proof.
  intros remaining sadness out Hbranch.
  unfold FinalBudgetResult.
  destruct Hbranch as [[Hle ->] | [Hlt ->]].
  - rewrite Z.min_l by lia.
    rewrite Z.max_r by lia.
    lia.
  - rewrite Z.min_r by lia.
    rewrite Z.max_r by lia.
    lia.
Qed.
Lemma greedy_block_state_sadness_upper_bound__greedy_loop :
  forall sorted blocks next budget initial remaining sadness,
    Permutation blocks sorted ->
    Forall (fun len => 1 <= len) blocks ->
    GreedyBlockState sorted next budget initial remaining sadness ->
    sadness <= initial.
Proof.
  intros sorted blocks next budget initial remaining sadness
    Hperm Hpositive Hstate.
  pose proof Hstate as Hstate_copy.
  unfold GreedyBlockState in Hstate_copy.
  destruct Hstate_copy as [Hnext [_ [Hsadness _]]].
  pose proof (forall_positive_lowerbound__greedy_transition _ Hpositive)
    as Hblocks_lower.
  pose proof (ListLib.lowerbound_perm 1 blocks sorted Hperm Hblocks_lower)
    as Hsorted_lower.
  assert (Hprefix_lower :
    ListLib.lowerbound 1 (sublist 0 next sorted)).
  {
    apply ListLib.lowerbound_sublist_intro; try lia.
    intros j Hj.
    apply (ListLib.lowerbound_Znth 1 sorted j Hsorted_lower).
    lia.
  }
  pose proof
    (map_succ_lowerbound_nonnegative__greedy_transition _ Hprefix_lower)
    as Hmapped_lower.
  pose proof
    (sum_nonnegative_lowerbound__greedy_transition _ Hmapped_lower)
    as Hsum_nonnegative.
  lia.
Qed.
Lemma Zlength_repeat_Z__final_result :
  forall (v n : Z),
    0 <= n ->
    Zlength (repeat v (Z.to_nat n)) = n.
Proof.
  intros v n Hn.
  rewrite Zlength_correct.
  rewrite repeat_length.
  lia.
Qed.
Lemma spec_all_one_full_budget__final_result :
  forall a k,
    1 <= Zlength a ->
    k = Zlength a ->
    (forall i, 0 <= i < Zlength a -> Znth i a 0 = 1) ->
    Spec k a 0.
Proof.
  intros a k Hlen Hk Hall.
  set (zeros := repeat 0 (Z.to_nat (Zlength a))).
  assert (Hzeros_len : Zlength zeros = Zlength a).
  {
    unfold zeros.
    apply Zlength_repeat_Z__final_result.
    lia.
  }
  assert (Hzeros_at : forall i, Znth i zeros 0 = 0).
  {
    intros i.
    unfold zeros.
    apply Znth_repeat.
  }
  assert (Hzeros_sad : ExamSadness zeros 0).
  {
    unfold ExamSadness.
    symmetry.
    rewrite set_card_Z_as_sum_exam__final_result.
    apply SumLib.ZRange.sum_Z_range_eq_zero.
    intros i Hi.
    destruct (prop_dec
      (Z.gcd (Znth i zeros 0) (Znth (i + 1) zeros 0) = 1)) as [Hg | Hg].
    - rewrite !Hzeros_at in Hg.
      cbn in Hg.
      lia.
    - reflexivity.
  }
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (zeros, 0).
  split.
  - split.
    + split.
      * unfold SimplifiedExams.
        exists (fun i => 0 <= i < Zlength a).
        split.
        -- intros idx Hidx. exact Hidx.
        -- split.
           ++ pose proof (set_card_Z_range_bounds_exam__final_result
                0 (Zlength a) (fun idx => 0 <= idx < Zlength a)
                ltac:(lia)) as Hcard.
              lia.
           ++ split.
              ** exact Hzeros_len.
              ** intros idx Hidx.
                 rewrite Hzeros_at.
                 destruct (prop_dec (0 <= idx < Zlength a));
                   [reflexivity | tauto].
      * exact Hzeros_sad.
    + intros [result sadness] Hcandidate.
      simpl.
      destruct Hcandidate as (Hsimplified & Hsadness).
      unfold SimplifiedExams in Hsimplified.
      destruct Hsimplified as
        (chosen & Hchosen_bounds & Hchosen_count & Hresult_len & Hresult_values).
      simpl in Hsadness, Hresult_len.
      pose proof (exam_sadness_bounds__final_result result sadness
        ltac:(lia) Hsadness) as Hbounds.
      lia.
  - reflexivity.
Qed.
Lemma path_nonboth_sum_invariant_nat__final_result :
  forall (m : nat) (chosen : Z -> Prop),
    let n := Z.of_nat (S m) in
    (SumLib.Sum.sum (fun i : Z => 0 <= i < n)
       (fun i => if prop_dec (chosen i) then 1 else 0) = 0 /\
     SumLib.Sum.sum (fun i : Z => 0 <= i < n - 1)
       (fun i => if prop_dec (~ (chosen i /\ chosen (i + 1))) then 1 else 0)
       = n - 1) \/
    (1 <= SumLib.Sum.sum (fun i : Z => 0 <= i < n)
       (fun i => if prop_dec (chosen i) then 1 else 0) /\
     n - SumLib.Sum.sum (fun i : Z => 0 <= i < n)
       (fun i => if prop_dec (chosen i) then 1 else 0) <=
     SumLib.Sum.sum (fun i : Z => 0 <= i < n - 1)
       (fun i => if prop_dec (~ (chosen i /\ chosen (i + 1))) then 1 else 0)).
Proof.
  induction m as [|m IH]; intros chosen.
  - change
      ((SumLib.Sum.sum (fun i : Z => 0 <= i < 1)
          (fun i => if prop_dec (chosen i) then 1 else 0) = 0 /\
        SumLib.Sum.sum (fun i : Z => 0 <= i < 0)
          (fun i => if prop_dec (~ (chosen i /\ chosen (i + 1)))
                    then 1 else 0) = 0) \/
       (1 <= SumLib.Sum.sum (fun i : Z => 0 <= i < 1)
          (fun i => if prop_dec (chosen i) then 1 else 0) /\
        1 - SumLib.Sum.sum (fun i : Z => 0 <= i < 1)
          (fun i => if prop_dec (chosen i) then 1 else 0) <=
        SumLib.Sum.sum (fun i : Z => 0 <= i < 0)
          (fun i => if prop_dec (~ (chosen i /\ chosen (i + 1)))
                    then 1 else 0))).
    rewrite !SumLib.ZRange.sum_Z_range_single.
    rewrite !SumLib.ZRange.sum_Z_range_empty by lia.
    destruct (prop_dec (chosen 0)); [right | left]; simpl; lia.
  - replace (Z.of_nat (S (S m))) with (Z.of_nat (S m) + 1) by lia.
    set (n := Z.of_nat (S m)).
    assert (Hn : 1 <= n) by (unfold n; lia).
    specialize (IH chosen).
    fold n in IH.
    fold n.
    cbn beta zeta.
    rewrite !(SumLib.ZRange.sum_Z_range_extend_right 0 n
      (fun i => if prop_dec (chosen i) then 1 else 0)) by lia.
    replace (n + 1 - 1) with n by lia.
    replace n with ((n - 1) + 1) by lia.
    rewrite !(SumLib.ZRange.sum_Z_range_extend_right 0 (n - 1)
      (fun i => if prop_dec (~ (chosen i /\ chosen (i + 1)))
                then 1 else 0)) by lia.
    replace (n - 1 + 1) with n by lia.
    destruct IH as [(HCzero & HSzero) | (HCpos & HSlower)].
    + destruct (prop_dec (chosen n)) as [Hnew | Hnew].
      * assert (Hlastbit :
          (if prop_dec (chosen (n - 1)) then 1 else 0) = 0).
        {
          eapply (SumLib.Sum.sum_nonneg_eq_zero_elim
            (fun x : Z => 0 <= x < n)
            (fun x => if prop_dec (chosen x) then 1 else 0)).
          - intros x Hx.
            destruct (prop_dec (chosen x)); lia.
          - exact HCzero.
          - lia.
        }
        destruct (prop_dec (chosen (n - 1))) as [Hlast | Hlast];
          [simpl in Hlastbit; lia |].
        assert (Hnewbit : (if prop_dec (chosen n) then 1 else 0) = 1).
        { destruct (prop_dec (chosen n)); [reflexivity | contradiction]. }
        assert (Hedgebit :
          (if prop_dec (~ (chosen (n - 1) /\ chosen n)) then 1 else 0) = 1).
        { destruct (prop_dec (~ (chosen (n - 1) /\ chosen n)));
            [reflexivity | exfalso; tauto]. }
        try rewrite Hnewbit; try rewrite Hedgebit.
        right. lia.
      * assert (Hnewbit : (if prop_dec (chosen n) then 1 else 0) = 0).
        { destruct (prop_dec (chosen n)); [contradiction | reflexivity]. }
        assert (Hedgebit :
          (if prop_dec (~ (chosen (n - 1) /\ chosen n)) then 1 else 0) = 1).
        { destruct (prop_dec (~ (chosen (n - 1) /\ chosen n)));
            [reflexivity | exfalso; tauto]. }
        try rewrite Hnewbit; try rewrite Hedgebit.
        left. lia.
    + destruct (prop_dec (chosen n)) as [Hnew | Hnew].
      * assert (Hnewbit : (if prop_dec (chosen n) then 1 else 0) = 1).
        { destruct (prop_dec (chosen n)); [reflexivity | contradiction]. }
        assert (Hedgebit :
          0 <= (if prop_dec (~ (chosen (n - 1) /\ chosen n)) then 1 else 0)).
        { destruct (prop_dec (~ (chosen (n - 1) /\ chosen n))); lia. }
        try rewrite Hnewbit.
        right. lia.
      * assert (Hnewbit : (if prop_dec (chosen n) then 1 else 0) = 0).
        { destruct (prop_dec (chosen n)); [contradiction | reflexivity]. }
        assert (Hedgebit :
          (if prop_dec (~ (chosen (n - 1) /\ chosen n)) then 1 else 0) = 1).
        { destruct (prop_dec (~ (chosen (n - 1) /\ chosen n)));
            [reflexivity | exfalso; tauto]. }
        try rewrite Hnewbit; try rewrite Hedgebit.
        right. lia.
Qed.
Lemma path_nonboth_count_lower_bound__final_result :
  forall n k (chosen : Z -> Prop),
    1 <= k < n ->
    #(fun i : Z => 0 <= i < n /\ chosen i) <= k ->
    n - k <=
      #(fun i : Z => 0 <= i < n - 1 /\ ~ (chosen i /\ chosen (i + 1))).
Proof.
  intros n k chosen Hkn Hcount.
  assert (Hn : 1 <= n) by lia.
  set (m := Z.to_nat (n - 1)).
  assert (Hnm : n = Z.of_nat (S m)).
  {
    unfold m.
    lia.
  }
  pose proof (path_nonboth_sum_invariant_nat__final_result m chosen) as Hinv.
  cbn beta zeta in Hinv.
  rewrite <- Hnm in Hinv.
  rewrite <- !set_card_Z_as_sum_exam__final_result in Hinv.
  destruct Hinv as [(HCzero & HSzero) | (HCpos & HSlower)]; lia.
Qed.
Lemma simplified_selected_value__final_result :
  forall a result (chosen : Z -> Prop) i,
    (forall j, 0 <= j < Zlength a ->
      Znth j result 0 = if prop_dec (chosen j) then 0 else Znth j a 0) ->
    0 <= i < Zlength a ->
    chosen i ->
    Znth i result 0 = 0.
Proof.
  intros a result chosen i Hvalues Hi Hchosen.
  rewrite Hvalues by exact Hi.
  destruct (prop_dec (chosen i)); [reflexivity | contradiction].
Qed.
Lemma simplified_unselected_one__final_result :
  forall a result (chosen : Z -> Prop) i,
    (forall j, 0 <= j < Zlength a -> Znth j a 0 = 1) ->
    (forall j, 0 <= j < Zlength a ->
      Znth j result 0 = if prop_dec (chosen j) then 0 else Znth j a 0) ->
    0 <= i < Zlength a ->
    ~ chosen i ->
    Znth i result 0 = 1.
Proof.
  intros a result chosen i Hall Hvalues Hi Hchosen.
  rewrite Hvalues by exact Hi.
  destruct (prop_dec (chosen i)); [contradiction |].
  apply Hall. exact Hi.
Qed.
Lemma all_one_simplified_edge__final_result :
  forall a result (chosen : Z -> Prop) i,
    (forall j, 0 <= j < Zlength a -> Znth j a 0 = 1) ->
    (forall j, 0 <= j < Zlength a ->
      Znth j result 0 = if prop_dec (chosen j) then 0 else Znth j a 0) ->
    0 <= i < Zlength a - 1 ->
    (Z.gcd (Znth i result 0) (Znth (i + 1) result 0) = 1 <->
      ~ (chosen i /\ chosen (i + 1))).
Proof.
  intros a result chosen i Hall Hvalues Hi.
  destruct (prop_dec (chosen i)) as [Hleft | Hleft];
    destruct (prop_dec (chosen (i + 1))) as [Hright | Hright].
  - pose proof (simplified_selected_value__final_result
      a result chosen i Hvalues ltac:(lia) Hleft) as Hvleft.
    pose proof (simplified_selected_value__final_result
      a result chosen (i + 1) Hvalues ltac:(lia) Hright) as Hvright.
    rewrite Hvleft, Hvright.
    cbn.
    split; intros H.
    + lia.
    + exfalso. apply H. split; assumption.
  - pose proof (simplified_selected_value__final_result
      a result chosen i Hvalues ltac:(lia) Hleft) as Hvleft.
    pose proof (simplified_unselected_one__final_result
      a result chosen (i + 1) Hall Hvalues ltac:(lia) Hright) as Hvright.
    rewrite Hvleft, Hvright.
    cbn. split; intros H.
    + intro Hboth. tauto.
    + reflexivity.
  - pose proof (simplified_unselected_one__final_result
      a result chosen i Hall Hvalues ltac:(lia) Hleft) as Hvleft.
    pose proof (simplified_selected_value__final_result
      a result chosen (i + 1) Hvalues ltac:(lia) Hright) as Hvright.
    rewrite Hvleft, Hvright.
    cbn. split; intros H.
    + intro Hboth. tauto.
    + reflexivity.
  - pose proof (simplified_unselected_one__final_result
      a result chosen i Hall Hvalues ltac:(lia) Hleft) as Hvleft.
    pose proof (simplified_unselected_one__final_result
      a result chosen (i + 1) Hall Hvalues ltac:(lia) Hright) as Hvright.
    rewrite Hvleft, Hvright.
    cbn. split; intros H.
    + intro Hboth. tauto.
    + reflexivity.
Qed.
Lemma all_one_candidate_sadness_nonboth__final_result :
  forall a result sadness (chosen : Z -> Prop),
    (forall j, 0 <= j < Zlength a -> Znth j a 0 = 1) ->
    Zlength result = Zlength a ->
    (forall j, 0 <= j < Zlength a ->
      Znth j result 0 = if prop_dec (chosen j) then 0 else Znth j a 0) ->
    ExamSadness result sadness ->
    sadness =
      #(fun i : Z => 0 <= i < Zlength a - 1 /\
        ~ (chosen i /\ chosen (i + 1))).
Proof.
  intros a result sadness chosen Hall Hlen Hvalues Hsadness.
  unfold ExamSadness in Hsadness.
  rewrite Hsadness, Hlen.
  rewrite !set_card_Z_as_sum_exam__final_result.
  apply SumLib.ZRange.sum_Z_range_ext.
  intros i Hi.
  pose proof (all_one_simplified_edge__final_result
    a result chosen i Hall Hvalues Hi) as Hedge.
  destruct (prop_dec
    (Z.gcd (Znth i result 0) (Znth (i + 1) result 0) = 1));
    destruct (prop_dec (~ (chosen i /\ chosen (i + 1))));
    try reflexivity; exfalso; tauto.
Qed.
Lemma prefix_selected_card__final_result :
  forall n k,
    0 <= k <= n ->
    #(fun i : Z => 0 <= i < n /\ 0 <= i < k) = k.
Proof.
  intros n k Hkn.
  rewrite set_card_Z_as_sum_exam__final_result.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 k n) by lia.
  assert (Hleft :
    SumLib.Sum.sum (fun i : Z => 0 <= i < k)
      (fun i => if prop_dec (0 <= i < k) then 1 else 0) = k).
  {
    transitivity
      (SumLib.Sum.sum (fun i : Z => 0 <= i < k) (fun _ => 1)).
    - apply SumLib.ZRange.sum_Z_range_ext.
      intros i Hi.
      destruct (prop_dec (0 <= i < k)); [reflexivity | tauto].
    - rewrite SumLib.ZRange.sum_Z_range_const by lia.
      lia.
  }
  assert (Hright :
    SumLib.Sum.sum (fun i : Z => k <= i < n)
      (fun i => if prop_dec (0 <= i < k) then 1 else 0) = 0).
  {
    apply SumLib.ZRange.sum_Z_range_eq_zero.
    intros i Hi.
    destruct (prop_dec (0 <= i < k)); [exfalso; lia | reflexivity].
  }
  lia.
Qed.
Lemma prefix_selected_nonboth_card__final_result :
  forall n k,
    1 <= k < n ->
    #(fun i : Z => 0 <= i < n - 1 /\
      ~ ((0 <= i < k) /\ (0 <= i + 1 < k))) = n - k.
Proof.
  intros n k Hkn.
  rewrite set_card_Z_as_sum_exam__final_result.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 (k - 1) (n - 1)) by lia.
  assert (Hleft :
    SumLib.Sum.sum (fun i : Z => 0 <= i < k - 1)
      (fun i => if prop_dec (~ ((0 <= i < k) /\ (0 <= i + 1 < k)))
                then 1 else 0) = 0).
  {
    apply SumLib.ZRange.sum_Z_range_eq_zero.
    intros i Hi.
    destruct (prop_dec (~ ((0 <= i < k) /\ (0 <= i + 1 < k))));
      [exfalso; apply n0; lia | reflexivity].
  }
  assert (Hright :
    SumLib.Sum.sum (fun i : Z => k - 1 <= i < n - 1)
      (fun i => if prop_dec (~ ((0 <= i < k) /\ (0 <= i + 1 < k)))
                then 1 else 0) = n - k).
  {
    transitivity
      (SumLib.Sum.sum (fun i : Z => k - 1 <= i < n - 1) (fun _ => 1)).
    - apply SumLib.ZRange.sum_Z_range_ext.
      intros i Hi.
      destruct (prop_dec (~ ((0 <= i < k) /\ (0 <= i + 1 < k))));
        [reflexivity | exfalso; apply n0; lia].
    - rewrite SumLib.ZRange.sum_Z_range_const by lia.
      lia.
  }
  lia.
Qed.
Lemma bounded_set_card_iff__final_result :
  forall low high (P Q : Z -> Prop),
    (forall i, low <= i < high -> (P i <-> Q i)) ->
    #(fun i : Z => low <= i < high /\ P i) =
    #(fun i : Z => low <= i < high /\ Q i).
Proof.
  intros low high P Q Hequiv.
  rewrite !set_card_Z_as_sum_exam__final_result.
  apply SumLib.ZRange.sum_Z_range_ext.
  intros i Hi.
  specialize (Hequiv i Hi).
  destruct (prop_dec (P i)); destruct (prop_dec (Q i));
    try reflexivity; exfalso; tauto.
Qed.
Lemma spec_all_one_partial_budget__final_result :
  forall a k,
    1 <= k < Zlength a ->
    (forall i, 0 <= i < Zlength a -> Znth i a 0 = 1) ->
    Spec k a (Zlength a - k).
Proof.
  intros a k Hkn Hall.
  set (n := Zlength a).
  set (zeros := repeat 0 (Z.to_nat k)).
  set (ones := repeat 1 (Z.to_nat (n - k))).
  set (result := zeros ++ ones).
  assert (Hzeros_len : Zlength zeros = k).
  {
    unfold zeros.
    apply Zlength_repeat_Z__final_result.
    lia.
  }
  assert (Hones_len : Zlength ones = n - k).
  {
    unfold ones.
    apply Zlength_repeat_Z__final_result.
    lia.
  }
  assert (Hresult_len : Zlength result = Zlength a).
  {
    unfold result.
    rewrite Zlength_app, Hzeros_len, Hones_len.
    unfold n. lia.
  }
  assert (Hresult_values : forall i, 0 <= i < Zlength a ->
    Znth i result 0 =
      if prop_dec (0 <= i < k) then 0 else Znth i a 0).
  {
    intros i Hi.
    destruct (prop_dec (0 <= i < k)) as [Hselected | Hunselected].
    - unfold result.
      rewrite app_Znth1 by (rewrite Hzeros_len; lia).
      unfold zeros.
      rewrite Znth_repeat.
      destruct (prop_dec (0 <= i < k)); [reflexivity | contradiction].
    - unfold result.
      rewrite app_Znth2 by (rewrite Hzeros_len; lia).
      unfold ones.
      rewrite Znth_repeat_lt by lia.
      rewrite Hall by exact Hi.
      destruct (prop_dec (0 <= i < k)); [contradiction | reflexivity].
  }
  assert (Hsimplified : SimplifiedExams a k result).
  {
    unfold SimplifiedExams.
    exists (fun i => 0 <= i < k).
    split.
    - intros i Hi. unfold n in Hkn. lia.
    - split.
      + rewrite prefix_selected_card__final_result by
          (unfold n in Hkn; lia).
        lia.
      + split.
        * exact Hresult_len.
        * exact Hresult_values.
  }
  assert (Hresult_sad : ExamSadness result (Zlength a - k)).
  {
    pose proof (prefix_selected_nonboth_card__final_result n k
      ltac:(unfold n; lia)) as Hprefix.
    unfold n in Hprefix.
    unfold ExamSadness.
    rewrite Hresult_len.
    rewrite <- Hprefix.
    apply bounded_set_card_iff__final_result.
    intros i Hi.
    symmetry.
    exact (all_one_simplified_edge__final_result
      a result (fun j => 0 <= j < k) i Hall Hresult_values Hi).
  }
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (result, Zlength a - k).
  split.
  - split.
    + split; assumption.
    + intros [other other_sad] Hcandidate.
      simpl.
      destruct Hcandidate as (Hother_simplified & Hother_sadness).
      unfold SimplifiedExams in Hother_simplified.
      destruct Hother_simplified as
        (chosen & Hchosen_bounds & Hchosen_count & Hother_len & Hother_values).
      simpl in Hother_sadness, Hother_len.
      pose proof (all_one_candidate_sadness_nonboth__final_result
        a other other_sad chosen Hall Hother_len Hother_values Hother_sadness)
        as Hsad_count.
      pose proof (path_nonboth_count_lower_bound__final_result
        (Zlength a) k chosen Hkn Hchosen_count) as Hlower.
      lia.
  - reflexivity.
Qed.
Lemma all_one_exam_optimum__allone_returns :
  forall a k,
    1 <= k <= Zlength a ->
    (forall i, 0 <= i < Zlength a -> Znth i a 0 = 1) ->
    Spec k a (Zlength a - k).
Proof.
  intros a k Hk Hall.
  destruct (Z.eq_dec k (Zlength a)) as [Heq | Hneq].
  - replace (Zlength a - k) with 0 by lia.
    apply spec_all_one_full_budget__final_result; try lia.
    exact Hall.
  - apply spec_all_one_partial_budget__final_result; try lia.
    exact Hall.
Qed.
