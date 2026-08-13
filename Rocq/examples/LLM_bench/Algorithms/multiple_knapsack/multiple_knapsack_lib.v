Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition PairwiseWeightValue (xs : list (Z * Z)) : Z :=
  sum (map (fun wp => fst wp * snd wp) xs).

Definition PickWeight (weights picks : list Z) : Z :=
  PairwiseWeightValue (combine weights picks).

Definition PickValue (values picks : list Z) : Z :=
  PairwiseWeightValue (combine values picks).

Definition BoundedPickList
    (weights values counts : list Z) (capacity : Z) (picks : list Z) : Prop :=
  Zlength weights = Zlength values /\
  Zlength weights = Zlength counts /\
  Zlength picks = Zlength weights /\
  0 <= capacity /\
  Forall2 (fun pick cnt => 0 <= pick <= cnt) picks counts /\
  0 <= PickWeight weights picks /\
  PickWeight weights picks <= capacity.

Definition MultipleKnapsackAnswer
    (weights values counts : list Z) (capacity answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun picks => BoundedPickList weights values counts capacity picks)
    (fun picks => PickValue values picks)
    answer.

Definition MultipleKnapsackPrefixAnswer
    (weights values counts : list Z) (i capacity answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun picks =>
       BoundedPickList
         (sublist 0 i weights)
         (sublist 0 i values)
         (sublist 0 i counts)
         capacity
         picks)
    (fun picks => PickValue (sublist 0 i values) picks)
    answer.

Definition MKDPValueBound (dp : list Z) (capacity : Z) : Prop :=
  Zlength dp = capacity + 1 /\
  forall cap,
    0 <= cap <= capacity ->
    0 <= Znth cap dp 0 <= 1000000.

(** Pure representation invariant for the three caller-owned scratch arrays.
    It is intentionally independent of every bounded-knapsack semantic
    predicate so that initialization and loop-boundary assertions can retain
    the logical list lengths even when spatial resources are split away. *)
Definition MKScratchArraysSafety
    (old q_idx q_val : list Z) (capacity : Z) : Prop :=
  Zlength old = capacity + 1 /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1.

Definition MKDPTable
    (weights values counts : list Z) (i capacity : Z) (dp : list Z) : Prop :=
  0 <= i <= Zlength weights /\
  0 <= capacity /\
  Zlength dp = capacity + 1 /\
  forall cap,
    0 <= cap <= capacity ->
    MultipleKnapsackPrefixAnswer weights values counts i cap (Znth cap dp 0).

Definition MKZeroPrefix (dp : list Z) (hi : Z) : Prop :=
  0 <= hi /\
  Zlength dp = hi /\
  forall cap, 0 <= cap < hi -> Znth cap dp 0 = 0.

Definition MKCopyPrefix (src dst : list Z) (j capacity : Z) : Prop :=
  0 <= j <= capacity + 1 /\
  Zlength src = capacity + 1 /\
  Zlength dst = capacity + 1 /\
  forall cap, 0 <= cap < j -> Znth cap dst 0 = Znth cap src 0.

Definition MKTransitionValue
    (old : list Z) (w v cnt capacity pos ans : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= pos <= capacity /\
  Zlength old = capacity + 1 /\
  max_value_of_subset Z.le
    (fun take =>
       0 <= take <= cnt /\
       take * w <= pos /\
       0 <= pos - take * w <= capacity)
    (fun take => Znth (pos - take * w) old 0 + take * v)
    ans.

Definition MKTransitionValueBound
    (old : list Z) (w v cnt capacity : Z) : Prop :=
  forall pos ans,
    0 <= pos <= capacity ->
    MKTransitionValue old w v cnt capacity pos ans ->
    0 <= ans <= 1000000.

Definition MKItemResidueProgress
    (old dp : list Z) (r w v cnt capacity : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= r /\
  r <= w /\
  r <= capacity + 1 /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1 /\
  (forall rem k pos,
     pos = rem + k * w ->
     0 <= rem < r ->
     0 <= k ->
     0 <= pos <= capacity ->
     MKTransitionValue old w v cnt capacity pos (Znth pos dp 0)) /\
  (forall rem k pos,
     pos = rem + k * w ->
     r <= rem < w ->
     0 <= k ->
     0 <= pos <= capacity ->
     Znth pos dp 0 = Znth pos old 0).

Definition MKResiduePrefix
    (old dp : list Z) (r w v cnt k capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= k /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1 /\
  forall t,
    0 <= t < k ->
    r + t * w <= capacity ->
    MKTransitionValue old w v cnt capacity (r + t * w)
      (Znth (r + t * w) dp 0).

Definition MKItemResiduePrefixProgress
    (old dp : list Z) (r w v cnt k capacity : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= r < w /\
  0 <= k /\
  r <= capacity /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1 /\
  MKResiduePrefix old dp r w v cnt k capacity /\
  forall pos,
    0 <= pos <= capacity ->
    (forall rem t,
       pos = rem + t * w ->
       0 <= rem < r ->
       0 <= t ->
       MKTransitionValue old w v cnt capacity pos (Znth pos dp 0)) /\
    (forall rem t,
       pos = rem + t * w ->
       0 <= rem < w ->
       0 <= t ->
       (r < rem \/ (rem = r /\ k <= t)) ->
       Znth pos dp 0 = Znth pos old 0).

Definition MKQueueEntryValue
    (old q_idx q_val : list Z) (r w v pos : Z) : Prop :=
  0 <= Znth pos q_idx 0 /\
  r + Znth pos q_idx 0 * w < Zlength old /\
  Znth pos q_val 0 =
    Znth (r + Znth pos q_idx 0 * w) old 0 - Znth pos q_idx 0 * v.

Definition MKQueueEntriesValid
    (old q_idx q_val : list Z) (head tail r w v k cnt : Z) : Prop :=
  forall pos,
    head <= pos < tail ->
    k - cnt <= Znth pos q_idx 0 /\
    Znth pos q_idx 0 < k /\
    MKQueueEntryValue old q_idx q_val r w v pos.

Definition MKQueueEntriesValidAfterDrop
    (old q_idx q_val : list Z) (head tail r w v k cnt : Z) : Prop :=
  forall pos,
    head <= pos < tail ->
    k - cnt <= Znth pos q_idx 0 /\
    Znth pos q_idx 0 < k /\
    MKQueueEntryValue old q_idx q_val r w v pos.

Definition MKQueueIndexIncreasing (q_idx : list Z) (head tail : Z) : Prop :=
  forall p q,
    head <= p /\ p < q /\ q < tail ->
    Znth p q_idx 0 < Znth q q_idx 0.

Definition MKQueueValueDecreasing (q_val : list Z) (head tail : Z) : Prop :=
  forall p q,
    head <= p /\ p < q /\ q < tail ->
    Znth p q_val 0 > Znth q q_val 0.

Definition MKQueueResultValueBound
    (q_val : list Z) (head tail v k : Z) : Prop :=
  forall pos,
    head <= pos < tail ->
    0 <= Znth pos q_val 0 + k * v <= 1000000.

Definition MKQueueCoversWindow
    (old q_idx q_val : list Z) (head tail r w v k cnt : Z) : Prop :=
  forall cand,
    0 <= cand ->
    cand < k ->
    k - cnt <= cand ->
    r + cand * w < Zlength old ->
    exists pos,
      head <= pos < tail /\
      cand <= Znth pos q_idx 0 /\
      Znth pos q_idx 0 < k /\
      Znth (r + cand * w) old 0 - cand * v <= Znth pos q_val 0.

Definition MKQueueCoversWithPending
    (old q_idx q_val : list Z) (head tail r w v k cnt current : Z) : Prop :=
  forall cand,
    0 <= cand ->
    cand < k ->
    k - cnt <= cand ->
    r + cand * w < Zlength old ->
    (exists pos,
      head <= pos < tail /\
      cand <= Znth pos q_idx 0 /\
      Znth pos q_idx 0 < k /\
      Znth (r + cand * w) old 0 - cand * v <= Znth pos q_val 0) \/
    Znth (r + cand * w) old 0 - cand * v <= current.

Definition MKQueueEntriesValidForResult
    (old q_idx q_val : list Z) (head tail r w v processed cnt : Z) : Prop :=
  forall pos,
    head <= pos < tail ->
    processed - 1 - cnt <= Znth pos q_idx 0 /\
    Znth pos q_idx 0 < processed /\
    MKQueueEntryValue old q_idx q_val r w v pos.

Definition MKQueueCoversResultWindow
    (old q_idx q_val : list Z) (head tail r w v processed cnt : Z) : Prop :=
  forall cand,
    0 <= cand ->
    cand < processed ->
    processed - 1 - cnt <= cand ->
    r + cand * w < Zlength old ->
    exists pos,
      head <= pos < tail /\
      cand <= Znth pos q_idx 0 /\
      Znth pos q_idx 0 < processed /\
      Znth (r + cand * w) old 0 - cand * v <= Znth pos q_val 0.

Definition MKQueueDropLoopState
    (old q_idx q_val : list Z)
    (head tail r w v cnt k capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= k /\
  0 <= head <= tail /\
  tail <= k /\
  tail <= Zlength q_idx /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1 /\
  Zlength old = capacity + 1 /\
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v k cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt /\
  MKQueueResultValueBound q_val head tail v (k - 1).

Definition MKQueueAfterDrop
    (old q_idx q_val : list Z)
    (head tail r w v cnt k capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= k /\
  0 <= head <= tail /\
  tail <= k /\
  tail <= Zlength q_idx /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1 /\
  Zlength old = capacity + 1 /\
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt /\
  MKQueueResultValueBound q_val head tail v k.

Definition MKQueuePendingState
    (old q_idx q_val : list Z)
    (head tail r w v cnt k capacity current : Z) : Prop :=
  0 <= r < w /\
  0 <= k /\
  0 <= head <= tail /\
  tail <= k /\
  tail <= Zlength q_idx /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1 /\
  Zlength old = capacity + 1 /\
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversWithPending old q_idx q_val head tail r w v k cnt current /\
  MKQueueResultValueBound q_val head tail v k /\
  0 <= current + k * v <= 1000000.

Definition MKQueueState
    (old q_idx q_val : list Z)
    (head tail r w v cnt processed capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= processed /\
  0 <= head <= tail /\
  tail <= processed /\
  tail <= Zlength q_idx /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1 /\
  Zlength old = capacity + 1 /\
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v processed cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversResultWindow old q_idx q_val head tail r w v processed cnt /\
  MKQueueResultValueBound q_val head tail v (processed - 1) /\
  (head < tail ->
     MKTransitionValue old w v cnt capacity (r + (processed - 1) * w)
       (Znth head q_val 0 + (processed - 1) * v)).

Definition MKResidueLoopState
    (old dp q_idx q_val : list Z)
    (r w v cnt k head tail capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= k /\
  0 <= head <= tail /\
  tail <= k /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1 /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1 /\
  MKResiduePrefix old dp r w v cnt k capacity /\
  MKQueueState old q_idx q_val head tail r w v cnt k capacity.

(** Layered views used by the C annotations.

    The original predicates above remain the compact proof interface.  These
    views make the annotation boundary explicit: [Safety] predicates contain
    only bounds/list representation facts needed for safe C execution, while
    [Semantics] predicates contain the bounded-knapsack mathematics. *)

Definition MKDPTableSafety
    (weights : list Z) (i capacity : Z) (dp : list Z) : Prop :=
  0 <= i <= Zlength weights /\
  0 <= capacity /\
  Zlength dp = capacity + 1.

Definition MKDPTableSemantics
    (weights values counts : list Z) (i capacity : Z) (dp : list Z) : Prop :=
  forall cap,
    0 <= cap <= capacity ->
    MultipleKnapsackPrefixAnswer weights values counts i cap (Znth cap dp 0).

Definition MKZeroPrefixSafety (dp : list Z) (hi : Z) : Prop :=
  0 <= hi /\ Zlength dp = hi.

Definition MKZeroPrefixSemantics (dp : list Z) (hi : Z) : Prop :=
  forall cap, 0 <= cap < hi -> Znth cap dp 0 = 0.

Definition MKCopyPrefixSafety
    (src dst : list Z) (j capacity : Z) : Prop :=
  0 <= j <= capacity + 1 /\
  Zlength src = capacity + 1 /\
  Zlength dst = capacity + 1.

Definition MKCopyPrefixSemantics
    (src dst : list Z) (j : Z) : Prop :=
  forall cap, 0 <= cap < j -> Znth cap dst 0 = Znth cap src 0.

Definition MKTransitionSafety
    (old : list Z) (w cnt capacity pos : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= pos <= capacity /\
  Zlength old = capacity + 1.

Definition MKTransitionSemantics
    (old : list Z) (w v cnt capacity pos ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun take =>
       0 <= take <= cnt /\
       take * w <= pos /\
       0 <= pos - take * w <= capacity)
    (fun take => Znth (pos - take * w) old 0 + take * v)
    ans.

Definition MKItemResidueProgressSafety
    (old dp : list Z) (r w cnt capacity : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= r /\
  r <= w /\
  r <= capacity + 1 /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1.

Definition MKItemResidueProgressSemantics
    (old dp : list Z) (r w v cnt capacity : Z) : Prop :=
  (forall rem k pos,
     pos = rem + k * w ->
     0 <= rem < r ->
     0 <= k ->
     0 <= pos <= capacity ->
     MKTransitionSemantics old w v cnt capacity pos (Znth pos dp 0)) /\
  (forall rem k pos,
     pos = rem + k * w ->
     r <= rem < w ->
     0 <= k ->
     0 <= pos <= capacity ->
     Znth pos dp 0 = Znth pos old 0).

Definition MKItemResiduePrefixSafety
    (old dp : list Z) (r w cnt k capacity : Z) : Prop :=
  0 < w /\
  0 <= cnt /\
  0 <= r < w /\
  0 <= k /\
  r <= capacity /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1.

Definition MKItemResiduePrefixSemantics
    (old dp : list Z) (r w v cnt k capacity : Z) : Prop :=
  (forall t,
     0 <= t < k ->
     r + t * w <= capacity ->
     MKTransitionSemantics old w v cnt capacity (r + t * w)
       (Znth (r + t * w) dp 0)) /\
  forall pos,
    0 <= pos <= capacity ->
    (forall rem t,
       pos = rem + t * w ->
       0 <= rem < r ->
       0 <= t ->
       MKTransitionSemantics old w v cnt capacity pos (Znth pos dp 0)) /\
    (forall rem t,
       pos = rem + t * w ->
       0 <= rem < w ->
       0 <= t ->
       (r < rem \/ (rem = r /\ k <= t)) ->
       Znth pos dp 0 = Znth pos old 0).

Definition MKQueueStorageSafety
    (old q_idx q_val : list Z) (head tail limit capacity : Z) : Prop :=
  0 <= head <= tail /\
  tail <= limit /\
  tail <= Zlength q_idx /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1 /\
  Zlength old = capacity + 1.

Definition MKQueueDropSafety
    (old q_idx q_val : list Z)
    (head tail r w k capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= k /\
  MKQueueStorageSafety old q_idx q_val head tail k capacity.

Definition MKQueueDropSemantics
    (old q_idx q_val : list Z)
    (head tail r w v cnt k : Z) : Prop :=
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v k cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt /\
  MKQueueResultValueBound q_val head tail v (k - 1).

Definition MKQueueAfterDropSemantics
    (old q_idx q_val : list Z)
    (head tail r w v cnt k : Z) : Prop :=
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt /\
  MKQueueResultValueBound q_val head tail v k.

Definition MKQueuePendingSemantics
    (old q_idx q_val : list Z)
    (head tail r w v cnt k current : Z) : Prop :=
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversWithPending old q_idx q_val head tail r w v k cnt current /\
  MKQueueResultValueBound q_val head tail v k /\
  0 <= current + k * v <= 1000000.

Definition MKQueueResultSafety
    (old q_idx q_val : list Z)
    (head tail r w processed capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= processed /\
  MKQueueStorageSafety old q_idx q_val head tail processed capacity.

Definition MKQueueResultSemantics
    (old q_idx q_val : list Z)
    (head tail r w v cnt processed capacity : Z) : Prop :=
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v processed cnt /\
  MKQueueIndexIncreasing q_idx head tail /\
  MKQueueValueDecreasing q_val head tail /\
  MKQueueCoversResultWindow old q_idx q_val head tail r w v processed cnt /\
  MKQueueResultValueBound q_val head tail v (processed - 1) /\
  (head < tail ->
     MKTransitionSemantics old w v cnt capacity (r + (processed - 1) * w)
       (Znth head q_val 0 + (processed - 1) * v)).

Definition MKResidueLoopSafety
    (old dp q_idx q_val : list Z)
    (r w k head tail capacity : Z) : Prop :=
  0 <= r < w /\
  0 <= k /\
  0 <= head <= tail /\
  tail <= k /\
  Zlength old = capacity + 1 /\
  Zlength dp = capacity + 1 /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1.

Definition MKResidueLoopSemantics
    (old dp q_idx q_val : list Z)
    (r w v cnt k head tail capacity : Z) : Prop :=
  (forall t,
     0 <= t < k ->
     r + t * w <= capacity ->
     MKTransitionSemantics old w v cnt capacity (r + t * w)
       (Znth (r + t * w) dp 0)) /\
  MKQueueResultSemantics old q_idx q_val head tail r w v cnt k capacity.

(* Helper imports migrated from multiple_knapsack__vc_proving_round9_merged_proof_manual.v. *)
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

(* Helper lemmas migrated from multiple_knapsack__vc_proving_round9_merged_proof_manual.v. *)

Lemma MKZeroPrefix_extend_by_zero :
  forall dp hi,
    MKZeroPrefix dp hi ->
    MKZeroPrefix (dp ++ 0 :: nil) (hi + 1).
Proof.
  unfold MKZeroPrefix.
  intros dp hi (Hhi & Hlen & Hzero).
  repeat split; try lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - intros cap Hcap.
    destruct (Z.eq_dec cap hi) as [Heq | Hneq].
    + subst cap.
      rewrite app_Znth2 by lia.
      rewrite Hlen.
      replace (hi - hi) with 0 by lia.
      rewrite Znth0_cons.
      reflexivity.
    + rewrite app_Znth1 by (rewrite Hlen; lia).
      apply Hzero. lia.
Qed.

Lemma MKCopyPrefix_zero :
  forall src dst capacity,
    0 <= capacity ->
    Zlength src = capacity + 1 ->
    Zlength dst = capacity + 1 ->
    MKCopyPrefix src dst 0 capacity.
Proof.
  unfold MKCopyPrefix.
  intros src dst capacity Hcap Hsrc Hdst.
  repeat split; try lia.
Qed.

Lemma MKCopyPrefix_extend_by_replace_Znth :
  forall src dst j capacity,
    MKCopyPrefix src dst j capacity ->
    0 <= j <= capacity ->
    MKCopyPrefix src (replace_Znth j (Znth j src 0) dst) (j + 1) capacity.
Proof.
  unfold MKCopyPrefix.
  intros src dst j capacity (Hj & Hsrc & Hdst & Hcopy) Hj_range.
  repeat split; try lia.
  - rewrite Zlength_replace_Znth. exact Hdst.
  - intros cap Hcap.
    destruct (Z.eq_dec cap j) as [Heq | Hneq].
    + subst cap.
      rewrite Znth_replace_Znth_Same by (rewrite Hdst; lia).
      reflexivity.
    + rewrite Znth_replace_Znth_Diff
        by (try rewrite Hdst; lia).
      apply Hcopy. lia.
Qed.

Lemma MKDPTable_copy_full :
  forall weights values counts i capacity src dst,
    MKDPTable weights values counts i capacity src ->
    MKCopyPrefix src dst (capacity + 1) capacity ->
    MKDPTable weights values counts i capacity dst.
Proof.
  unfold MKDPTable, MKCopyPrefix.
  intros weights values counts i capacity src dst
         (Hi & Hcapacity & Hsrc_len & Hanswer)
         (_ & _ & Hdst_len & Hcopy).
  repeat split; try lia; auto.
  intros cap Hcap.
  rewrite Hcopy by lia.
  apply Hanswer. lia.
Qed.

Lemma MKItemResiduePrefixProgress_init :
  forall old dp r w v cnt capacity,
    0 <= r < w ->
    r <= capacity ->
    MKItemResidueProgress old dp r w v cnt capacity ->
    MKItemResiduePrefixProgress old dp r w v cnt 0 capacity.
Proof.
  unfold MKItemResidueProgress, MKItemResiduePrefixProgress, MKResiduePrefix.
  intros old dp r w v cnt capacity Hr_range Hr_capacity
         (Hw & Hcnt & Hr_nonneg & Hr_le_w & Hr_cap1 & Hold_len & Hdp_len &
          Hdone & Hfuture).
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hold_len |].
  split; [exact Hdp_len |].
  split.
  - repeat split; try lia; auto.
  - intros pos Hpos.
    split.
    + intros rem t0 Hpos_eq Hrem Ht0.
      eapply Hdone; eauto; lia.
    + intros rem t0 Hpos_eq Hrem Ht0 Hlater.
      eapply Hfuture; eauto.
      destruct Hlater as [Hgt | (Heq & _)].
      * lia.
      * subst rem. lia.
Qed.

Lemma MKResidueLoopState_empty_queue_init :
  forall old dp q_idx q_val r w v cnt capacity,
    0 <= r < w ->
    r <= capacity ->
    Zlength q_idx = capacity + 1 ->
    Zlength q_val = capacity + 1 ->
    MKItemResidueProgress old dp r w v cnt capacity ->
    MKResidueLoopState old dp q_idx q_val r w v cnt 0 0 0 capacity.
Proof.
  unfold MKResidueLoopState, MKQueueState, MKQueueEntriesValidForResult,
    MKQueueIndexIncreasing, MKQueueValueDecreasing, MKQueueCoversResultWindow,
    MKQueueResultValueBound, MKItemResidueProgress, MKResiduePrefix.
  intros old dp q_idx q_val r w v cnt capacity Hr_range Hr_capacity
         Hqidx_len Hqval_len
         (Hw & Hcnt & Hr_nonneg & Hr_le_w & Hr_cap1 & Hold_len & Hdp_len &
          Hdone & Hfuture).
  repeat split; try lia; auto.
Qed.

Lemma MKForall2_pick_nonneg_Znth :
  forall picks counts idx,
    Forall2 (fun pick cnt => 0 <= pick <= cnt) picks counts ->
    0 <= idx < Zlength picks ->
    0 <= Znth idx picks 0.
Proof.
  intros picks counts idx HFor.
  revert idx.
  induction HFor as [| pick cnt picks counts Hpick _ IH]; intros idx Hidx.
  - rewrite Zlength_nil in Hidx; lia.
  - destruct (Z.eq_dec idx 0) as [-> | Hnz].
    + rewrite Znth0_cons; lia.
    + rewrite Zlength_cons in Hidx.
      rewrite Znth_cons by lia.
      apply IH; lia.
Qed.

Lemma MKPickValue_le_weight_times_1000 :
  forall weights values picks,
    Zlength values = Zlength weights ->
    Zlength picks = Zlength weights ->
    (forall idx, 0 <= idx < Zlength weights ->
       1 <= Znth idx weights 0 /\ 0 <= Znth idx values 0 <= 1000) ->
    (forall idx, 0 <= idx < Zlength picks -> 0 <= Znth idx picks 0) ->
    0 <= PickValue values picks <= PickWeight weights picks * 1000.
Proof.
  induction weights as [| w weights IH]; intros values picks Hvalues Hpicks Hbounds Hpick_nonneg.
  - destruct values as [| v values].
    2:{ pose proof (Zlength_nonneg values); rewrite Zlength_cons, Zlength_nil in Hvalues; lia. }
    destruct picks as [| p picks].
    2:{ pose proof (Zlength_nonneg picks); rewrite Zlength_cons, Zlength_nil in Hpicks; lia. }
    unfold PickValue, PickWeight, PairwiseWeightValue; simpl; lia.
  - destruct values as [| v values].
    { pose proof (Zlength_nonneg weights); rewrite Zlength_cons, Zlength_nil in Hvalues; lia. }
    destruct picks as [| p picks].
    { pose proof (Zlength_nonneg weights); rewrite Zlength_cons, Zlength_nil in Hpicks; lia. }
    rewrite !Zlength_cons in Hvalues, Hpicks.
    assert (Hhead_bounds : 1 <= w /\ 0 <= v <= 1000).
    {
      specialize (Hbounds 0 ltac:(pose proof (Zlength_nonneg weights); rewrite Zlength_cons; lia)).
      rewrite !Znth0_cons in Hbounds.
      exact Hbounds.
    }
    assert (Hhead_pick : 0 <= p).
    {
      specialize (Hpick_nonneg 0 ltac:(pose proof (Zlength_nonneg picks); rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hpick_nonneg.
      exact Hpick_nonneg.
    }
    assert (Htail :
      0 <= PickValue values picks <= PickWeight weights picks * 1000).
    {
      assert (Hvalues_tail : Zlength values = Zlength weights) by lia.
      assert (Hpicks_tail : Zlength picks = Zlength weights) by lia.
      apply (IH values picks Hvalues_tail Hpicks_tail).
      - intros idx Hidx.
        specialize (Hbounds (idx + 1) ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth_cons in Hbounds by lia.
        replace (idx + 1 - 1) with idx in Hbounds by lia.
        exact Hbounds.
      - intros idx Hidx.
        specialize (Hpick_nonneg (idx + 1) ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth_cons in Hpick_nonneg by lia.
        replace (idx + 1 - 1) with idx in Hpick_nonneg by lia.
        exact Hpick_nonneg.
    }
    unfold PickValue, PickWeight, PairwiseWeightValue in *.
    simpl in *.
    nia.
Qed.

Lemma MKBoundedPickList_value_bound :
  forall weights values counts capacity picks,
    0 <= capacity ->
    (forall idx, 0 <= idx < Zlength weights ->
       1 <= Znth idx weights 0 /\ 0 <= Znth idx values 0 <= 1000) ->
    BoundedPickList weights values counts capacity picks ->
    0 <= PickValue values picks <= capacity * 1000.
Proof.
  intros weights values counts capacity picks Hcap Hbounds Hbounded.
  unfold BoundedPickList in Hbounded.
  destruct Hbounded as
    (Hwv & _Hwc & Hpicks_len & _Hcap' & HFor & _Hweight_nonneg & Hweight_cap).
  assert (Hpick_nonneg :
    forall idx, 0 <= idx < Zlength picks -> 0 <= Znth idx picks 0).
  {
    intros idx Hidx.
    eapply MKForall2_pick_nonneg_Znth; eauto.
  }
  pose proof (MKPickValue_le_weight_times_1000 weights values picks)
    as Hvalue_weight.
  specialize (Hvalue_weight ltac:(lia) ltac:(lia) Hbounds Hpick_nonneg).
  lia.
Qed.

Lemma MultipleKnapsackPrefixAnswer_zero_items :
  forall weights values counts capacity,
    0 <= capacity ->
    MultipleKnapsackPrefixAnswer weights values counts 0 capacity 0.
Proof.
  intros weights values counts capacity Hcap.
  unfold MultipleKnapsackPrefixAnswer, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset.
  change (sublist 0 0 weights) with (@nil Z).
  change (sublist 0 0 values) with (@nil Z).
  change (sublist 0 0 counts) with (@nil Z).
  exists (@nil Z).
  split; [split | reflexivity].
  - unfold BoundedPickList, PickWeight, PairwiseWeightValue.
    repeat split; try rewrite Zlength_nil; try solve [simpl; lia | constructor].
  - intros picks Hbounded.
    unfold BoundedPickList in Hbounded.
    destruct Hbounded as (_ & _ & Hpicks_len & _).
    rewrite Zlength_nil in Hpicks_len.
    apply Zlength_nil_inv in Hpicks_len.
    subst picks.
    unfold PickValue, PairwiseWeightValue.
    simpl.
    lia.
Qed.

Lemma MKZeroPrefix_implies_MKDPTable_zero_items :
  forall weights values counts capacity dp,
    0 <= capacity ->
    MKZeroPrefix dp (capacity + 1) ->
    MKDPTable weights values counts 0 capacity dp.
Proof.
  intros weights values counts capacity dp Hcap Hzero.
  unfold MKZeroPrefix in Hzero.
  destruct Hzero as (_Hhi & Hlen & Hzero_at).
  unfold MKDPTable.
  repeat split.
  - lia.
  - apply Zlength_nonneg.
  - exact Hcap.
  - exact Hlen.
  - intros cap Hcap_range.
    rewrite Hzero_at by lia.
    apply MultipleKnapsackPrefixAnswer_zero_items; lia.
Qed.

Lemma MultipleKnapsackPrefixAnswer_value_bound_by_capacity :
  forall weights values counts i capacity ans,
    0 <= i <= Zlength weights ->
    0 <= capacity ->
    (forall idx, 0 <= idx < Zlength weights ->
       1 <= Znth idx weights 0 /\ 0 <= Znth idx values 0 <= 1000) ->
    MultipleKnapsackPrefixAnswer weights values counts i capacity ans ->
    0 <= ans <= capacity * 1000.
Proof.
  intros weights values counts i capacity ans Hi Hcap Hbounds Hanswer.
  unfold MultipleKnapsackPrefixAnswer, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in Hanswer.
  destruct Hanswer as [picks [[Hbounded _Hmax] Hans]].
  subst ans.
  eapply MKBoundedPickList_value_bound; [exact Hcap | | exact Hbounded].
  intros idx Hidx.
  rewrite Zlength_sublist in Hidx by lia.
  rewrite !Znth_sublist0 by lia.
  apply Hbounds.
  lia.
Qed.

Lemma MKDPTable_value_bound_by_capacity :
  forall weights values counts i capacity dp pos,
    (forall idx, 0 <= idx < Zlength weights ->
       1 <= Znth idx weights 0 /\ 0 <= Znth idx values 0 <= 1000) ->
    MKDPTable weights values counts i capacity dp ->
    0 <= pos <= capacity ->
    0 <= Znth pos dp 0 <= pos * 1000.
Proof.
  intros weights values counts i capacity dp pos Hbounds Hdp Hpos.
  unfold MKDPTable in Hdp.
  destruct Hdp as (Hi & _Hcap & _Hlen & Hanswer).
  specialize (Hanswer pos Hpos).
  eapply MultipleKnapsackPrefixAnswer_value_bound_by_capacity; eauto; lia.
Qed.

Lemma MKDPTable_implies_MKDPValueBound_under_global_item_bounds :
  forall weights values counts i capacity dp,
    0 <= capacity <= 1000 ->
    (forall idx, 0 <= idx < Zlength weights ->
       1 <= Znth idx weights 0 /\ 0 <= Znth idx values 0 <= 1000) ->
    MKDPTable weights values counts i capacity dp ->
    MKDPValueBound dp capacity.
Proof.
  intros weights values counts i capacity dp Hcap_bound Hbounds Hdp.
  unfold MKDPValueBound.
  unfold MKDPTable in Hdp.
  destruct Hdp as (Hi & Hcap & Hlen & Hanswer).
  split; [exact Hlen |].
  intros cap Hcap_range.
  specialize (Hanswer cap Hcap_range).
  pose proof (MultipleKnapsackPrefixAnswer_value_bound_by_capacity
                weights values counts i cap (Znth cap dp 0)
                Hi (proj1 Hcap_range) Hbounds Hanswer) as Hvalue.
  nia.
Qed.

Lemma MKCopyPrefix_full_preserves_Znth :
  forall src dst capacity pos,
    MKCopyPrefix src dst (capacity + 1) capacity ->
    0 <= pos <= capacity ->
    Znth pos dst 0 = Znth pos src 0.
Proof.
  intros src dst capacity pos Hcopy Hpos.
  unfold MKCopyPrefix in Hcopy.
  destruct Hcopy as (_Hrange & _Hsrc_len & _Hdst_len & Hsame).
  apply Hsame; lia.
Qed.

Lemma MKDPTable_copy_implies_MKDPValueBound_under_global_item_bounds :
  forall weights values counts i capacity dp old,
    0 <= capacity <= 1000 ->
    (forall idx, 0 <= idx < Zlength weights ->
       1 <= Znth idx weights 0 /\ 0 <= Znth idx values 0 <= 1000) ->
    MKDPTable weights values counts i capacity dp ->
    MKCopyPrefix dp old (capacity + 1) capacity ->
    MKDPValueBound old capacity.
Proof.
  intros weights values counts i capacity dp old Hcap_bound Hbounds Hdp Hcopy.
  unfold MKDPValueBound.
  unfold MKCopyPrefix in Hcopy.
  destruct Hcopy as (_Hrange & _Hdp_len & Hold_len & Hsame).
  split; [exact Hold_len |].
  intros cap Hcap.
  pose proof (MKDPTable_value_bound_by_capacity weights values counts i capacity dp cap
                Hbounds Hdp Hcap) as Hvalue.
  rewrite Hsame by lia.
  nia.
Qed.

Lemma MKDPTable_implies_MKTransitionValueBound_for_current_item :
  forall weights values counts i capacity dp old w v cnt,
    0 <= capacity <= 1000 ->
    1 <= w ->
    0 <= v <= 1000 ->
    (forall idx, 0 <= idx < Zlength weights ->
       1 <= Znth idx weights 0 /\ 0 <= Znth idx values 0 <= 1000) ->
    MKDPTable weights values counts i capacity dp ->
    MKCopyPrefix dp old (capacity + 1) capacity ->
    MKTransitionValueBound old w v cnt capacity.
Proof.
  intros weights values counts i capacity dp old w v cnt
    Hcapacity Hw Hv Hbounds Hdp Hcopy.
  unfold MKTransitionValueBound.
  intros pos ans Hpos Htrans.
  unfold MKTransitionValue in Htrans.
  destruct Htrans as (_Hw_pos & _Hcnt & _Hpos_range & _Hold_len & Hmax).
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hmax.
  destruct Hmax as [take [[Htake _Htake_max] Hans]].
  subst ans.
  destruct Htake as (Htake_nonneg & _Htake_cnt & Htake_weight & Hrem).
  pose proof (MKCopyPrefix_full_preserves_Znth dp old capacity (pos - take * w)
                Hcopy ltac:(lia)) as Hcopy_at.
  pose proof (MKDPTable_value_bound_by_capacity weights values counts i capacity dp
                (pos - take * w) Hbounds Hdp ltac:(lia)) as Hdp_bound.
  rewrite Hcopy_at.
  nia.
Qed.

Lemma MKCopyPrefix_full_implies_MKItemResidueProgress_zero :
  forall old dp w v cnt capacity,
    1 <= w ->
    0 <= cnt ->
    MKCopyPrefix dp old (capacity + 1) capacity ->
    MKItemResidueProgress old dp 0 w v cnt capacity.
Proof.
  intros old dp w v cnt capacity Hw Hcnt Hcopy.
  unfold MKItemResidueProgress.
  unfold MKCopyPrefix in Hcopy.
  destruct Hcopy as (Hrange & Hdp_len & Hold_len & Hsame).
  repeat split; try lia; try exact Hold_len; try exact Hdp_len.
  intros rem k pos Hpos Hrem Hk Hcap.
  symmetry.
  apply Hsame.
  lia.
Qed.

Lemma MKResidueLoopState_to_MKQueueDropLoopState_predrop :
  forall (old dp q_idx q_val : list Z) (r w v cnt k head tail capacity : Z),
    MKResidueLoopState old dp q_idx q_val r w v cnt k head tail capacity ->
    MKQueueDropLoopState old q_idx q_val head tail r w v cnt k capacity.
Proof.
  intros old dp q_idx q_val r w v cnt k head tail capacity H.
  unfold MKResidueLoopState in H.
  destruct H as
    (Hr & Hk & Hhead & Htail & Hold & Hdp & Hqidx & Hqval & Hprefix & Hqueue).
  unfold MKQueueState in Hqueue.
  destruct Hqueue as
    (Hrq & Hkq & Hheadq & Htailq & Htailqidx & Hqidxlen & Hqvallen &
     Holdlen & Hentries & Hinc & Hdec & Hcovers & Hbound & Hlast).
  unfold MKQueueDropLoopState.
  split; [exact Hrq|].
  split; [exact Hkq|].
  split; [exact Hheadq|].
  split; [exact Htailq|].
  split; [exact Htailqidx|].
  split; [exact Hqidxlen|].
  split; [exact Hqvallen|].
  split; [exact Holdlen|].
  split; [exact Hentries|].
  split; [exact Hinc|].
  split; [exact Hdec|].
  split.
  - unfold MKQueueCoversWindow.
    intros cand Hcand0 Hcandlt Hcandlower Hcandlen.
    unfold MKQueueCoversResultWindow in Hcovers.
    apply Hcovers; try lia.
  - exact Hbound.
Qed.

Lemma MKQueueDropLoopState_pop_expired_preserves_predrop :
  forall (old q_idx q_val : list Z) (head tail r w v cnt k capacity : Z),
    Znth head q_idx 0 < k - cnt ->
    head < tail ->
    MKQueueDropLoopState old q_idx q_val head tail r w v cnt k capacity ->
    MKQueueDropLoopState old q_idx q_val (head + 1) tail r w v cnt k capacity.
Proof.
  intros old q_idx q_val head tail r w v cnt k capacity Hexpired Hnonempty Hstate.
  unfold MKQueueDropLoopState in *.
  destruct Hstate as
    (Hr & Hk & Hhead_tail & Htail_k & Htail_len & Hqidx_len & Hqval_len &
     Hold_len & Hvalid & Hinc & Hdec & Hcover & Hbound).
  split; [exact Hr |].
  split; [exact Hk |].
  split; [lia |].
  split; [exact Htail_k |].
  split; [exact Htail_len |].
  split; [exact Hqidx_len |].
  split; [exact Hqval_len |].
  split; [exact Hold_len |].
  split.
  - intros p Hp. apply Hvalid. lia.
  - split.
    + intros p q Hp. apply Hinc. lia.
    + split.
      * intros p q Hp. apply Hdec. lia.
      * split.
        -- intros cand Hcand0 Hcand_lt Hcand_lo Hcand_old.
    unfold MKQueueCoversWindow in Hcover.
    destruct (Hcover cand Hcand0 Hcand_lt Hcand_lo Hcand_old) as
      (pos & Hpos_range & Hcand_pos & Hpos_k & Hval).
    destruct (Z.eq_dec pos head) as [Hpos_head | Hpos_ne].
    { subst pos. lia. }
    { exists pos. repeat split; try lia; assumption. }
        -- intros p Hp. apply Hbound. lia.
Qed.

Lemma MKQueueDropLoopState_empty_exit_to_MKQueueAfterDrop :
  forall (old q_idx q_val : list Z) (head tail r w v cnt k capacity : Z),
    head >= tail ->
    MKQueueDropLoopState old q_idx q_val head tail r w v cnt k capacity ->
    MKQueueAfterDrop old q_idx q_val head tail r w v cnt k capacity.
Proof.
  intros old q_idx q_val head tail r w v cnt k capacity Hexit Hstate.
  unfold MKQueueAfterDrop, MKQueueDropLoopState in *.
  destruct Hstate as
    (Hr & Hk & Hhead_tail & Htail_k & Htail_len & Hqidx_len & Hqval_len &
     Hold_len & Hvalid & Hinc & Hdec & Hcover & Hbound).
  split; [exact Hr |].
  split; [exact Hk |].
  split; [lia |].
  split; [exact Htail_k |].
  split; [exact Htail_len |].
  split; [exact Hqidx_len |].
  split; [exact Hqval_len |].
  split; [exact Hold_len |].
  split.
  - intros p Hp. lia.
  - split; [exact Hinc |].
    split; [exact Hdec |].
    split; [exact Hcover |].
    intros p Hp. lia.
Qed.

Lemma MKQueueDropLoopState_nonempty_exit_to_MKQueueAfterDrop :
  forall (old q_idx q_val : list Z)
         (head tail r w v cnt k capacity current curpos : Z),
    Znth head q_idx 0 >= k - cnt ->
    head < tail ->
    0 <= v ->
    0 <= r ->
    r < w ->
    1 <= w ->
    curpos = r + k * w ->
    0 <= curpos <= capacity ->
    current = Znth curpos old 0 - k * v ->
    current + k * v <= 1000000 ->
    MKTransitionValueBound old w v cnt capacity ->
    MKQueueDropLoopState old q_idx q_val head tail r w v cnt k capacity ->
    MKQueueAfterDrop old q_idx q_val head tail r w v cnt k capacity.
Proof.
  intros old q_idx q_val head tail r w v cnt k capacity current curpos
    Hhead_ge Hnonempty Hv Hr0 Hrw Hw Hcurpos Hcurpos_bounds Hcurrent
    Hcurrent_upper Htrans_bound Hstate.
  unfold MKQueueDropLoopState in Hstate.
  destruct Hstate as
    (Hr & Hk & Hhead_tail & Htail_k & Htail_len & Hqidx_len & Hqval_len &
     Hold_len & Hvalid & Hinc & Hdec & Hcover & Hprev_bound).
  assert (Hhead_range : head <= head < tail) by lia.
  specialize (Hvalid head Hhead_range) as Hhead_valid.
  destruct Hhead_valid as (Hhead_old_low & Hhead_lt_k & Hhead_entry).
  unfold MKQueueEntryValue in Hhead_entry.
  destruct Hhead_entry as (Hhead_idx_nonneg & Hhead_old_bound & Hhead_val_eq).
  set (head_idx := Znth head q_idx 0) in *.
  set (head_ans := Znth head q_val 0 + k * v).
  assert (Hqval_le_head :
    forall p, head <= p < tail -> Znth p q_val 0 <= Znth head q_val 0).
  {
    intros p Hp.
    destruct (Z.eq_dec p head) as [-> | Hp_ne].
    - lia.
    - unfold MKQueueValueDecreasing in Hdec.
      specialize (Hdec head p ltac:(lia)).
      lia.
  }
  assert (Hhead_upper : head_ans <= 1000000).
  {
    destruct (Z_le_dec head_ans (current + k * v)) as [Hle_current | Hgt_current].
    - lia.
    - assert (Hhead_transition :
        MKTransitionValue old w v cnt capacity curpos head_ans).
      {
        unfold MKTransitionValue.
        repeat split; try lia; try assumption.
        unfold max_value_of_subset, max_object_of_subset.
        exists (k - head_idx).
        split.
        - split.
          + repeat split; try nia.
          + intros take Htake.
            destruct Htake as ((Htake0 & Htake_cnt) & Htake_w & Htake_rem).
            destruct (Z.eq_dec take 0) as [Htake_zero | Htake_nonzero].
            * subst take.
              assert (Hcurpos_zero : curpos - 0 * w = curpos) by nia.
              rewrite Hcurpos_zero.
              assert (Hcurrent_value : Znth curpos old 0 = current + k * v) by nia.
              assert (Hcurrent_le_head : current + k * v <= head_ans) by lia.
              replace (Znth (curpos - (k - head_idx) * w) old 0 +
                         (k - head_idx) * v) with head_ans.
              2: {
                unfold head_ans.
                assert (Hwitness_pos :
                  curpos - (k - head_idx) * w = r + head_idx * w) by nia.
                rewrite Hwitness_pos.
                nia.
              }
              replace (Znth curpos old 0 + 0 * v) with (current + k * v) by nia.
              exact Hcurrent_le_head.
            * set (cand := k - take).
              assert (Hcand0 : 0 <= cand) by (unfold cand; nia).
              assert (Hcand_lt : cand < k) by (unfold cand; nia).
              assert (Hcand_lo : k - cnt <= cand) by (unfold cand; nia).
              assert (Hcand_old : r + cand * w < Zlength old).
              {
                unfold cand.
                assert (curpos - take * w = r + (k - take) * w) by nia.
                lia.
              }
              unfold MKQueueCoversWindow in Hcover.
              destruct (Hcover cand Hcand0 Hcand_lt Hcand_lo Hcand_old) as
                (cover_pos & Hcover_range & Hcand_cover & Hcover_k & Hcover_val).
              assert (Hcover_le_head :
                Znth cover_pos q_val 0 <= Znth head q_val 0)
                by (apply Hqval_le_head; lia).
              replace (Znth (curpos - (k - head_idx) * w) old 0 +
                         (k - head_idx) * v) with head_ans.
              2: {
                unfold head_ans.
                assert (Hwitness_pos :
                  curpos - (k - head_idx) * w = r + head_idx * w) by nia.
                rewrite Hwitness_pos.
                nia.
              }
              assert (Htake_pos : curpos - take * w = r + cand * w)
                by (unfold cand; nia).
              rewrite Htake_pos.
              replace (Znth (r + cand * w) old 0 + take * v)
                with (Znth (r + cand * w) old 0 - cand * v + k * v)
                by (unfold cand; nia).
              unfold head_ans in *.
              lia.
        - unfold head_ans.
          assert (curpos - (k - head_idx) * w = r + head_idx * w) by nia.
          rewrite H.
          nia.
      }
      specialize (Htrans_bound curpos head_ans Hcurpos_bounds Hhead_transition).
      lia.
  }
  unfold MKQueueAfterDrop.
  split; [exact Hr |].
  split; [exact Hk |].
  split; [exact Hhead_tail |].
  split; [exact Htail_k |].
  split; [exact Htail_len |].
  split; [exact Hqidx_len |].
  split; [exact Hqval_len |].
  split; [exact Hold_len |].
  split.
  - unfold MKQueueEntriesValidAfterDrop.
    intros p Hp.
    specialize (Hvalid p Hp) as (Hold_low & Hp_lt_k & Hp_entry).
    assert (Hidx_low : k - cnt <= Znth p q_idx 0).
    {
      destruct (Z.eq_dec p head) as [-> | Hp_ne].
      - lia.
      - unfold MKQueueIndexIncreasing in Hinc.
        specialize (Hinc head p ltac:(lia)).
        lia.
    }
    split; [lia | split; [lia | exact Hp_entry]].
  - split; [exact Hinc |].
    split; [exact Hdec |].
    split; [exact Hcover |].
    unfold MKQueueResultValueBound.
    intros p Hp.
    specialize (Hprev_bound p Hp) as Hprev.
    assert (Znth p q_val 0 <= Znth head q_val 0)
      by (apply Hqval_le_head; lia).
    unfold head_ans in Hhead_upper.
    nia.
Qed.

Lemma MKQueueAfterDrop_to_MKQueuePendingState_current :
  forall old q_idx q_val head tail r w v cnt k capacity current,
    MKQueueAfterDrop old q_idx q_val head tail r w v cnt k capacity ->
    0 <= current + k * v <= 1000000 ->
    MKQueuePendingState old q_idx q_val head tail r w v cnt k capacity current.
Proof.
  intros.
  unfold MKQueueAfterDrop, MKQueuePendingState, MKQueueCoversWithPending in *.
  intuition eauto; try lia.
Qed.

Lemma MKQueuePendingState_pop_dominated_tail_preserves :
  forall old q_idx q_val head tail r w v cnt k capacity current,
    MKQueuePendingState old q_idx q_val head tail r w v cnt k capacity current ->
    head < tail ->
    Znth (tail - 1) q_val 0 <= current ->
    MKQueuePendingState old q_idx q_val head (tail - 1) r w v cnt k capacity current.
Proof.
  intros old q_idx q_val head tail r w v cnt k capacity current HP Hnonempty Hdom.
  unfold MKQueuePendingState in *.
  destruct HP as
    [Hr [Hk [Hheadtail [Htailk [Htail_len [Hqidx_len [Hqval_len
       [Hold_len [Hvalid [Hidx_inc [Hval_dec [Hcovers [Hresult_bound Hcurrent_bound]]]]]]]]]]]]].
  split; [exact Hr |].
  split; [exact Hk |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hqidx_len |].
  split; [exact Hqval_len |].
  split; [exact Hold_len |].
  split.
  { unfold MKQueueEntriesValidAfterDrop in *.
    intros pos0 Hpos.
    apply Hvalid; lia. }
  split.
  { unfold MKQueueIndexIncreasing in *.
    intros p q Hpq.
    apply Hidx_inc; lia. }
  split.
  { unfold MKQueueValueDecreasing in *.
    intros p q Hpq.
    apply Hval_dec; lia. }
  split.
  { unfold MKQueueCoversWithPending in *.
    intros cand Hcand0 Hcandlt Hcandcnt Hcandold.
    specialize (Hcovers cand Hcand0 Hcandlt Hcandcnt Hcandold) as [Hcovered | Hcurrent].
    + destruct Hcovered as [pos0 [Hpos [Hidxlo [Hidxhi Hval]]]].
      destruct (Z_lt_ge_dec pos0 (tail - 1)).
      * left. exists pos0. repeat split; try assumption; lia.
      * right.
        assert (pos0 = tail - 1) by lia.
        subst pos0.
        lia.
    + right; assumption. }
  split.
  { unfold MKQueueResultValueBound in *.
    intros pos0 Hpos.
    apply Hresult_bound; lia. }
  exact Hcurrent_bound.
Qed.

Lemma MKQueuePendingState_push_to_MKQueueState :
  forall old q_idx q_val head tail r w v cnt k capacity current,
    MKQueuePendingState old q_idx q_val head tail r w v cnt k capacity current ->
    current = Znth (r + k * w) old 0 - k * v ->
    0 <= r + k * w <= capacity ->
    0 <= cnt ->
    k <= capacity ->
    (head < tail -> Znth (tail - 1) q_val 0 > current) ->
    MKQueueState old
      (replace_Znth tail k q_idx)
      (replace_Znth tail current q_val)
      head (tail + 1) r w v cnt (k + 1) capacity.
Proof.
  intros old q_idx q_val head tail r w v cnt k capacity current
    HPending Hcurrent Hpos Hcnt Hkcap Htail_dom.
  unfold MKQueuePendingState in HPending.
  destruct HPending as
    [Hr [Hk [Hheadtail [Htailk [Htail_len [Hqidx_len [Hqval_len
       [Hold_len [Hvalid [Hidx_inc [Hval_dec [Hcovers
         [Hresult_bound Hcurrent_bound]]]]]]]]]]]]].
  set (q_idx' := replace_Znth tail k q_idx).
  set (q_val' := replace_Znth tail current q_val).
  assert (Htail_qidx : 0 <= tail < Zlength q_idx) by lia.
  assert (Htail_qval : 0 <= tail < Zlength q_val) by lia.
  assert (Htail_final : tail < Zlength q_idx') by
    (subst q_idx'; rewrite Zlength_replace_Znth; lia).
  assert (Htail_final_val : tail < Zlength q_val') by
    (subst q_val'; rewrite Zlength_replace_Znth; lia).
  assert (Hvalid_final :
    MKQueueEntriesValidForResult old q_idx' q_val' head (tail + 1)
      r w v (k + 1) cnt).
  {
    unfold MKQueueEntriesValidForResult.
    intros pos0 Hpos0.
    destruct (Z.eq_dec pos0 tail) as [-> | Hneq].
    - unfold MKQueueEntryValue.
      repeat split;
        subst q_idx' q_val';
        rewrite ?Znth_replace_Znth_Same by lia;
        try rewrite Hold_len; try lia; try exact Hcurrent.
    - assert (head <= pos0 < tail) by lia.
      specialize (Hvalid pos0 H) as [Hlo [Hhi Hentry]].
      unfold MKQueueEntryValue in *.
      destruct Hentry as [Hentry0 [Hentry1 Hentry2]].
      repeat split;
        subst q_idx' q_val';
        rewrite ?Znth_replace_Znth_Diff by lia;
        try lia; try assumption; try exact Hentry2.
  }
  assert (Hidx_inc_final :
    MKQueueIndexIncreasing q_idx' head (tail + 1)).
  {
    unfold MKQueueIndexIncreasing in *.
    intros p q Hpq.
    destruct Hpq as [Hp [Hpq Hq]].
    destruct (Z.eq_dec q tail) as [-> | Hqneq].
    - subst q_idx'.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_replace_Znth_Same by lia.
      specialize (Hvalid p ltac:(lia)) as [_ [Hp_idx _]].
      lia.
    - assert (q < tail) by lia.
      assert (p <> tail) by lia.
      subst q_idx'.
      rewrite !Znth_replace_Znth_Diff by lia.
      apply Hidx_inc; lia.
  }
  assert (Hval_dec_final :
    MKQueueValueDecreasing q_val' head (tail + 1)).
  {
    unfold MKQueueValueDecreasing in *.
    intros p q Hpq.
    destruct Hpq as [Hp [Hpq Hq]].
    destruct (Z.eq_dec q tail) as [-> | Hqneq].
    - assert (p <> tail) by lia.
      subst q_val'.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_replace_Znth_Same by lia.
      destruct (Z.eq_dec p (tail - 1)) as [-> | Hp_last].
      + apply Htail_dom; lia.
      + assert (Znth p q_val 0 > Znth (tail - 1) q_val 0).
        { apply Hval_dec; lia. }
        assert (Znth (tail - 1) q_val 0 > current).
        { apply Htail_dom; lia. }
        lia.
    - assert (q < tail) by lia.
      assert (p <> tail) by lia.
      subst q_val'.
      rewrite !Znth_replace_Znth_Diff by lia.
      apply Hval_dec; lia.
  }
  assert (Hcovers_final :
    MKQueueCoversResultWindow old q_idx' q_val' head (tail + 1)
      r w v (k + 1) cnt).
  {
    unfold MKQueueCoversResultWindow, MKQueueCoversWithPending in *.
    intros cand Hcand0 Hcandlt Hcandcnt Hcandold.
    destruct (Z_lt_ge_dec cand k) as [Hcand_k | Hcand_ge].
    - specialize (Hcovers cand Hcand0 Hcand_k ltac:(lia) Hcandold)
        as [Hcovered | Hpending].
      + destruct Hcovered as [pos0 [Hpos0 [Hcand_idx [Hidx_k Hval]]]].
        exists pos0.
        repeat split; try lia.
        * subst q_idx'. rewrite Znth_replace_Znth_Diff by lia. exact Hcand_idx.
        * subst q_idx'. rewrite Znth_replace_Znth_Diff by lia. lia.
        * subst q_val'. rewrite Znth_replace_Znth_Diff by lia. exact Hval.
      + exists tail.
        repeat split; try lia.
        * subst q_idx'. rewrite Znth_replace_Znth_Same by lia. lia.
        * subst q_idx'. rewrite Znth_replace_Znth_Same by lia. lia.
        * subst q_val'. rewrite Znth_replace_Znth_Same by lia. exact Hpending.
    - assert (cand = k) by lia. subst cand.
      exists tail.
      repeat split; try lia.
      + subst q_idx'. rewrite Znth_replace_Znth_Same by lia. lia.
      + subst q_idx'. rewrite Znth_replace_Znth_Same by lia. lia.
      + subst q_val'. rewrite Znth_replace_Znth_Same by lia. lia.
  }
  assert (Hresult_bound_final :
    MKQueueResultValueBound q_val' head (tail + 1) v k).
  {
    unfold MKQueueResultValueBound in *.
    intros pos0 Hpos0.
    destruct (Z.eq_dec pos0 tail) as [-> | Hneq].
    - subst q_val'. rewrite Znth_replace_Znth_Same by lia.
      exact Hcurrent_bound.
    - subst q_val'. rewrite Znth_replace_Znth_Diff by lia.
      apply Hresult_bound; lia.
  }
  unfold MKQueueState.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [subst q_idx'; rewrite Zlength_replace_Znth; lia|].
  split; [subst q_idx'; rewrite Zlength_replace_Znth; lia|].
  split; [subst q_val'; rewrite Zlength_replace_Znth; lia|].
  split; [lia|].
  split; [exact Hvalid_final|].
  split; [exact Hidx_inc_final|].
  split; [exact Hval_dec_final|].
  split; [exact Hcovers_final|].
  split; [replace (k + 1 - 1) with k by lia; exact Hresult_bound_final|].
  intros Hnonempty.
  replace (k + 1 - 1) with k by lia.
  unfold MKTransitionValue.
    repeat split; try lia.
    exists (k - Znth head q_idx' 0).
    split.
    + unfold max_object_of_subset.
      split.
      * specialize (Hvalid_final head ltac:(lia))
          as [Hhead_lo [Hhead_hi Hhead_entry]].
        unfold MKQueueEntryValue in Hhead_entry.
        destruct Hhead_entry as [Hidx_nonneg [Hidx_bound Hqval_eq]].
        repeat split; try lia.
        -- nia.
        -- replace (r + k * w - (k - Znth head q_idx' 0) * w)
             with (r + Znth head q_idx' 0 * w) by ring.
           rewrite Hold_len in Hidx_bound. nia.
      * intros take Htake.
        destruct Htake as [Htake_bounds [Htake_fit Htake_pos]].
        set (cand := k - take).
        assert (Hcand0 : 0 <= cand).
        { subst cand. nia. }
        assert (Hcandlt : cand < k + 1) by (subst cand; lia).
        assert (Hcandcnt : k + 1 - 1 - cnt <= cand) by (subst cand; lia).
        assert (Hcandold : r + cand * w < Zlength old).
        {
          subst cand.
          rewrite Hold_len.
          replace (r + (k - take) * w) with (r + k * w - take * w) by ring.
          lia.
        }
        specialize (Hcovers_final cand Hcand0 Hcandlt Hcandcnt Hcandold)
          as [pos0 [Hpos0 [Hcand_idx [Hidx_proc Hval_cover]]]].
        assert (Hqueue_le_head :
          Znth pos0 q_val' 0 <= Znth head q_val' 0).
        {
          destruct (Z.eq_dec pos0 head) as [-> | Hpos_head]; [lia|].
          assert (head < pos0) by lia.
          specialize (Hval_dec_final head pos0 ltac:(lia)).
          lia.
        }
        replace (r + k * w - take * w) with (r + cand * w)
          by (subst cand; ring).
        replace take with (k - cand) by (subst cand; ring).
        replace (Znth (r + cand * w) old 0 + (k - cand) * v)
          with (Znth (r + cand * w) old 0 - cand * v + k * v)
          by ring.
        specialize (Hvalid_final head ltac:(lia))
          as [_ [_ Hhead_entry_for_max]].
        unfold MKQueueEntryValue in Hhead_entry_for_max.
        destruct Hhead_entry_for_max as [_ [_ Hhead_qval_eq]].
        replace (r + k * w - (k - Znth head q_idx' 0) * w)
          with (r + Znth head q_idx' 0 * w) by ring.
        replace (Znth (r + Znth head q_idx' 0 * w) old 0 +
                   (k - Znth head q_idx' 0) * v)
          with (Znth head q_val' 0 + k * v).
        2: { rewrite Hhead_qval_eq. ring. }
        lia.
    + specialize (Hvalid_final head ltac:(lia))
        as [Hhead_lo [Hhead_hi Hhead_entry]].
      unfold MKQueueEntryValue in Hhead_entry.
      destruct Hhead_entry as [Hidx_nonneg [Hidx_bound Hqval_eq]].
      replace (r + k * w - (k - Znth head q_idx' 0) * w)
        with (r + Znth head q_idx' 0 * w) by ring.
      rewrite Hqval_eq.
      ring.
Qed.

Lemma MKQueueState_head_transition :
  forall old q_idx q_val head tail r w v cnt processed capacity,
    MKQueueState old q_idx q_val head tail r w v cnt processed capacity ->
    head < tail ->
    MKTransitionValue old w v cnt capacity (r + (processed - 1) * w)
      (Znth head q_val 0 + (processed - 1) * v).
Proof.
  intros old q_idx q_val head tail r w v cnt processed capacity Hstate Hnonempty.
  unfold MKQueueState in Hstate.
  tauto.
Qed.

Lemma MKQueueState_head_result_bound :
  forall q_val head tail v processed,
    MKQueueResultValueBound q_val head tail v (processed - 1) ->
    head < tail ->
    0 <= Znth head q_val 0 + (processed - 1) * v <= 1000000.
Proof.
  intros q_val head tail v processed Hbound Hnonempty.
  unfold MKQueueResultValueBound in Hbound.
  apply Hbound; lia.
Qed.

Lemma MKQueueState_head_bound :
  forall old q_idx q_val head tail r w v cnt processed capacity,
    MKQueueState old q_idx q_val head tail r w v cnt processed capacity ->
    head < tail ->
    0 <= Znth head q_val 0 + (processed - 1) * v <= 1000000.
Proof.
  intros old q_idx q_val head tail r w v cnt processed capacity Hstate Hnonempty.
  unfold MKQueueState in Hstate.
  destruct Hstate as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hbound _]]]]]]]]]]]]].
  unfold MKQueueResultValueBound in Hbound.
  apply Hbound; lia.
Qed.

Lemma residue_repr_unique :
  forall rem1 rem2 t1 t2 w,
    0 < w ->
    0 <= rem1 < w ->
    0 <= rem2 < w ->
    rem1 + t1 * w = rem2 + t2 * w ->
    rem1 = rem2.
Proof.
  intros rem1 rem2 t1 t2 w Hw Hrem1 Hrem2 Heq.
  assert ((rem1 + t1 * w) mod w = rem1) as Hmod1.
  { rewrite Z_mod_plus by lia. apply Z.mod_small; lia. }
  assert ((rem2 + t2 * w) mod w = rem2) as Hmod2.
  { rewrite Z_mod_plus by lia. apply Z.mod_small; lia. }
  rewrite <- Hmod1, <- Hmod2.
  now rewrite Heq.
Qed.

Lemma MKItemResiduePrefixProgress_extend_after_dp_write :
  forall old dp r w v cnt k capacity pos ans,
    pos = r + k * w ->
    0 <= pos <= capacity ->
    MKItemResiduePrefixProgress old dp r w v cnt k capacity ->
    MKTransitionValue old w v cnt capacity pos ans ->
    MKItemResiduePrefixProgress old (replace_Znth pos ans dp) r w v cnt
      (k + 1) capacity.
Proof.
  intros old dp r w v cnt k capacity pos ans Hpos Hpos_range Hprog Htrans.
  unfold MKItemResiduePrefixProgress in *.
  destruct Hprog as
    (Hw & Hcnt & Hr_range & Hk & Hr_cap & Hold_len & Hdp_len & Hprefix & Hrest).
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hold_len |].
  split; [rewrite Zlength_replace_Znth; exact Hdp_len |].
  split.
  - unfold MKResiduePrefix in Hprefix |- *.
    destruct Hprefix as (Hpr_range & Hpr_k & Hpr_old_len & Hpr_dp_len & Hpref).
    split; [lia |].
    split; [lia |].
    split; [exact Hold_len |].
    split; [rewrite Zlength_replace_Znth; exact Hdp_len |].
    intros t Ht Hcap.
    destruct (Z_lt_ge_dec t k) as [Ht_old | Ht_new].
    + specialize (Hpref t ltac:(lia) Hcap).
      rewrite Znth_replace_Znth_Diff.
      * exact Hpref.
      * rewrite Hdp_len; lia.
      * rewrite Hdp_len; lia.
      * subst pos; nia.
    + assert (t = k) by lia.
      subst t.
      replace (r + k * w) with pos by lia.
      rewrite Znth_replace_Znth_Same.
      * exact Htrans.
      * rewrite Hdp_len; lia.
  - intros p Hp_range.
    specialize (Hrest p Hp_range) as [Hdone Hsame].
    split.
    + intros rem t Hp_eq Hrem_range Ht.
      specialize (Hdone rem t Hp_eq Hrem_range Ht).
      rewrite Znth_replace_Znth_Diff.
      * exact Hdone.
      * rewrite Hdp_len; lia.
      * rewrite Hdp_len; lia.
      * intro Heq.
        assert (rem + t * w = r + k * w) as Hrepr by (subst p; subst pos; lia).
        assert (rem = r) as Hrem_eq.
        { eapply residue_repr_unique with (t1 := t) (t2 := k) (w := w);
            try eassumption; lia. }
        lia.
    + intros rem t Hp_eq Hrem_range Ht Hcase.
      assert (r < rem \/ rem = r /\ k <= t) as Hold_case by lia.
      specialize (Hsame rem t Hp_eq Hrem_range Ht Hold_case).
      rewrite Znth_replace_Znth_Diff.
      * exact Hsame.
      * rewrite Hdp_len; lia.
      * rewrite Hdp_len; lia.
      * intro Heq.
        assert (rem + t * w = r + k * w) as Hrepr by (subst p; subst pos; lia).
        assert (rem = r) as Hrem_eq.
        { eapply residue_repr_unique with (t1 := t) (t2 := k) (w := w);
            try eassumption; lia. }
        subst rem.
        destruct Hcase as [Hcase | [_ Ht_ge]]; nia.
Qed.

Lemma MKResidueLoopState_after_dp_write :
  forall old dp qidx qval r w v cnt k head tail capacity,
    MKItemResiduePrefixProgress old dp r w v cnt k capacity ->
    MKQueueState old qidx qval head tail r w v cnt k capacity ->
    MKResidueLoopState old dp qidx qval r w v cnt k head tail capacity.
Proof.
  intros old dp qidx qval r w v cnt k head tail capacity Hprog Hqueue.
  unfold MKResidueLoopState, MKItemResiduePrefixProgress, MKQueueState in *.
  tauto.
Qed.

Lemma MKResidueLoopState_to_MKItemResidueProgress_next_residue :
  forall old dp qidx qval r w v cnt k head tail capacity pos,
    pos = r + k * w ->
    pos > capacity ->
    MKItemResiduePrefixProgress old dp r w v cnt k capacity ->
    MKResidueLoopState old dp qidx qval r w v cnt k head tail capacity ->
    MKItemResidueProgress old dp (r + 1) w v cnt capacity.
Proof.
  intros old dp qidx qval r w v cnt k head tail capacity pos
    Hpos Hpast Hprog _Hloop.
  unfold MKItemResiduePrefixProgress in Hprog.
  destruct Hprog as
    (Hw & Hcnt & Hr_range & Hk & Hr_cap & Hold_len & Hdp_len & Hprefix & Hrest).
  unfold MKResiduePrefix in Hprefix.
  destruct Hprefix as (_ & _ & _ & _ & Hpref).
  unfold MKItemResidueProgress.
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hold_len |].
  split; [exact Hdp_len |].
  split.
  - intros rem t p Hp_eq Hrem_range Ht Hp_range.
    assert (rem < r \/ rem = r) as [Hrem_lt | Hrem_eq] by lia.
    + specialize (Hrest p Hp_range) as [Hdone _].
      eapply Hdone; eauto; lia.
    + subst rem.
      assert (t < k) by (subst pos; subst p; nia).
      replace p with (r + t * w) by lia.
      eapply Hpref.
      * lia.
      * lia.
  - intros rem t p Hp_eq Hrem_range Ht Hp_range.
    specialize (Hrest p Hp_range) as [_ Hsame].
    eapply Hsame; eauto; try lia.
Qed.

Lemma worker_Zlength_eq_length :
  forall (A B : Type) (xs : list A) (ys : list B),
    Zlength xs = Zlength ys -> Datatypes.length xs = Datatypes.length ys.
Proof.
  intros A B xs ys Hlen.
  rewrite !Zlength_correct in Hlen.
  lia.
Qed.

Lemma worker_sublist_0_succ {A : Type} (d : A) (xs : list A) (i : Z) :
  0 <= i < Zlength xs ->
  sublist 0 (i + 1) xs = sublist 0 i xs ++ Znth i xs d :: nil.
Proof.
  intros Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single d i xs) by lia.
  reflexivity.
Qed.

Lemma worker_PickWeight_app_single :
  forall weights picks w take,
    Zlength picks = Zlength weights ->
    PickWeight (weights ++ w :: nil) (picks ++ take :: nil) =
      PickWeight weights picks + w * take.
Proof.
  intros weights picks w take Hlen.
  unfold PickWeight, PairwiseWeightValue.
  rewrite combine_app.
  2: {
    apply worker_Zlength_eq_length.
    symmetry; exact Hlen.
  }
  rewrite map_app, sum_app.
  simpl.
  lia.
Qed.

Lemma worker_PickValue_app_single :
  forall values picks v take,
    Zlength picks = Zlength values ->
    PickValue (values ++ v :: nil) (picks ++ take :: nil) =
      PickValue values picks + v * take.
Proof.
  intros values picks v take Hlen.
  unfold PickValue, PairwiseWeightValue.
  rewrite combine_app.
  2: {
    apply worker_Zlength_eq_length.
    symmetry; exact Hlen.
  }
  rewrite map_app, sum_app.
  simpl.
  lia.
Qed.

Lemma worker_BoundedPickList_extend :
  forall pweights pvalues pcounts picks rem capacity w v cnt take,
    BoundedPickList pweights pvalues pcounts rem picks ->
    0 < w ->
    0 <= take <= cnt ->
    capacity = rem + take * w ->
    BoundedPickList (pweights ++ w :: nil) (pvalues ++ v :: nil)
      (pcounts ++ cnt :: nil) capacity (picks ++ take :: nil).
Proof.
  intros pweights pvalues pcounts picks rem capacity w v cnt take
    Hbounded Hw Htake Hcapacity.
  unfold BoundedPickList in *.
  destruct Hbounded as (Hwv & Hwc & Hpicks & Hrem & Hforall & Hweight).
  repeat split.
  - rewrite !Zlength_app_cons. lia.
  - rewrite !Zlength_app_cons. lia.
  - rewrite !Zlength_app_cons. lia.
  - lia.
  - apply Forall2_app; [exact Hforall |].
    constructor; [lia | constructor].
  - rewrite worker_PickWeight_app_single by exact Hpicks.
    lia.
  - rewrite worker_PickWeight_app_single by exact Hpicks.
    lia.
Qed.

Lemma worker_PickWeight_nonneg :
  forall weights picks counts,
    Zlength weights = Zlength picks ->
    Forall2 (fun pick cnt : Z => 0 <= pick <= cnt) picks counts ->
    (forall idx, 0 <= idx < Zlength weights -> 0 <= Znth idx weights 0) ->
    0 <= PickWeight weights picks.
Proof.
  induction weights as [| wt weights IH]; intros picks counts Hlen Hforall Hweights.
  - destruct picks as [| pick picks].
    + unfold PickWeight, PairwiseWeightValue; simpl; lia.
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg picks). lia.
  - destruct picks as [| pick picks].
    + unfold PickWeight, PairwiseWeightValue; simpl; lia.
    + inversion Hforall as [| ? ? ? counts' Hpick Htail]; subst.
      assert (Hwt : 0 <= wt).
      { specialize (Hweights 0).
        rewrite Znth0_cons in Hweights.
        apply Hweights.
        rewrite Zlength_cons. pose proof (Zlength_nonneg weights). lia.
      }
      assert (Htail_len : Zlength weights = Zlength picks).
      { rewrite !Zlength_cons in Hlen. lia. }
      assert (Htail_nonneg : 0 <= PickWeight weights picks).
      { eapply IH; [exact Htail_len | exact Htail |].
        intros idx Hidx.
        specialize (Hweights (idx + 1)).
        rewrite Znth_cons in Hweights by lia.
        replace (idx + 1 - 1) with idx in Hweights by lia.
        apply Hweights.
        rewrite Zlength_cons. lia.
      }
      unfold PickWeight, PairwiseWeightValue in *.
      simpl.
      lia.
Qed.

Lemma MKTransitionValue_matches_bounded_pick_extension :
  forall weights values counts i capacity old w v cnt pos ans,
    0 <= i < Zlength weights ->
    Zlength values = Zlength weights ->
    Zlength counts = Zlength weights ->
    w = Znth i weights 0 ->
    v = Znth i values 0 ->
    cnt = Znth i counts 0 ->
    (forall idx, 0 <= idx < Zlength weights -> 1 <= Znth idx weights 0) ->
    MKDPTable weights values counts i capacity old ->
    MKTransitionValue old w v cnt capacity pos ans ->
    MultipleKnapsackPrefixAnswer weights values counts (i + 1) pos ans.
Proof.
  intros weights values counts i capacity old w v cnt pos ans
    Hi Hvalues_len Hcounts_len Hw Hv Hcnt Hweights_pos Hdp Htrans.
  unfold MKTransitionValue in Htrans.
  destruct Htrans as (Hw_pos & Hcnt_nonneg & Hpos_range & Hold_len & Hmax_take).
  unfold MKDPTable in Hdp.
  destruct Hdp as (_ & _ & _ & Hdp).
  unfold MultipleKnapsackPrefixAnswer in *.
  rewrite (worker_sublist_0_succ 0 weights i) by lia.
  rewrite (worker_sublist_0_succ 0 values i) by lia.
  rewrite (worker_sublist_0_succ 0 counts i) by lia.
  rewrite <- Hw, <- Hv, <- Hcnt.
  clear Hw Hv Hcnt.
  destruct Hmax_take as [best_take [[Hbest_take_set Hbest_take_max] Hbest_take_value]].
  destruct Hbest_take_set as
    (Hbest_take_bounds & Hbest_take_weight & Hbest_rem_range).
  pose proof (Hdp (pos - best_take * w) Hbest_rem_range) as Hdp_best.
  unfold MultipleKnapsackPrefixAnswer in Hdp_best.
  destruct Hdp_best as [best_prefix [[Hbest_prefix_bounded Hbest_prefix_max]
                                      Hbest_prefix_value]].
  exists (best_prefix ++ best_take :: nil).
  split.
  - split.
    + eapply worker_BoundedPickList_extend.
      * exact Hbest_prefix_bounded.
      * exact Hw_pos.
      * exact Hbest_take_bounds.
      * lia.
    + intros picks Hpicks_bounded.
      unfold BoundedPickList in Hpicks_bounded.
      destruct Hpicks_bounded as
        (Hwv_app & Hwc_app & Hpicks_len & Hpos_nonneg & Hforall_app & Hweight_app).
      destruct (Forall2_app_inv_r (sublist 0 i counts) (cnt :: nil) Hforall_app)
        as [prefix [last (Hforall_prefix & Hforall_last & Hpicks_eq)]].
      inversion Hforall_last as [| take ? ? ? Htake_bounds Hlast_nil]; subst.
      inversion Hlast_nil; subst.
      assert (Hprefix_len_counts :
        Zlength prefix = Zlength (sublist 0 i counts)).
      { pose proof (Forall2_length Hforall_prefix) as Hlen_nat.
        rewrite !Zlength_correct.
        lia.
      }
      assert (Hprefix_len_weights :
        Zlength prefix = Zlength (sublist 0 i weights)).
      { rewrite Hprefix_len_counts.
        rewrite !Zlength_sublist0 by lia.
        lia.
      }
      assert (Hprefix_len_values :
        Zlength prefix = Zlength (sublist 0 i values)).
      { rewrite Hprefix_len_weights.
        rewrite !Zlength_sublist0 by lia.
        lia.
      }
      rewrite (worker_PickWeight_app_single (sublist 0 i weights) prefix
                 w take) in Hweight_app
        by exact Hprefix_len_weights.
      assert (Hprefix_weight_nonneg :
        0 <= PickWeight (sublist 0 i weights) prefix).
      { eapply worker_PickWeight_nonneg.
        - symmetry; exact Hprefix_len_weights.
        - exact Hforall_prefix.
        - intros idx Hidx.
          assert (Hidx_i : 0 <= idx < i).
          { rewrite Zlength_sublist0 in Hidx by lia. lia. }
          rewrite Znth_sublist0 by exact Hidx_i.
          specialize (Hweights_pos idx).
          lia.
      }
      assert (Hrem_range : 0 <= pos - take * w <= capacity) by lia.
      assert (Htake_set :
        0 <= take <= cnt /\ take * w <= pos /\ 0 <= pos - take * w <= capacity)
        by (repeat split; lia).
      specialize (Hbest_take_max take Htake_set).
      specialize (Hdp (pos - take * w) Hrem_range).
      unfold MultipleKnapsackPrefixAnswer in Hdp.
      destruct Hdp as [best [[_ Hprefix_max] Hprefix_value]].
      assert (Hprefix_bounded :
        BoundedPickList (sublist 0 i weights) (sublist 0 i values)
          (sublist 0 i counts) (pos - take * w) prefix).
      { unfold BoundedPickList.
        repeat split.
        - rewrite !Zlength_sublist0 by lia. lia.
        - rewrite !Zlength_sublist0 by lia. lia.
        - exact Hprefix_len_weights.
        - lia.
        - exact Hforall_prefix.
        - exact Hprefix_weight_nonneg.
        - lia.
      }
      specialize (Hprefix_max prefix Hprefix_bounded).
      assert (Hbest_pick_value :
        PickValue (sublist 0 i values ++ v :: nil)
          (best_prefix ++ best_take :: nil) =
        Znth (pos - best_take * w) old 0 + best_take * v).
      { assert (Hbest_prefix_len_values :
          Zlength best_prefix = Zlength (sublist 0 i values)).
        { unfold BoundedPickList in Hbest_prefix_bounded.
          destruct Hbest_prefix_bounded as (Hwv & _ & Hpicks & _).
          lia.
        }
        rewrite (worker_PickValue_app_single (sublist 0 i values) best_prefix
                   v best_take)
          by exact Hbest_prefix_len_values.
        rewrite Hbest_prefix_value.
        lia.
      }
      rewrite (worker_PickValue_app_single (sublist 0 i values) prefix
                 v take)
        by exact Hprefix_len_values.
      rewrite Hbest_pick_value.
      rewrite Hprefix_value in Hprefix_max.
      lia.
  - assert (Hbest_prefix_len_values :
      Zlength best_prefix = Zlength (sublist 0 i values)).
    { unfold BoundedPickList in Hbest_prefix_bounded.
      destruct Hbest_prefix_bounded as (Hwv & _ & Hpicks & _).
      lia.
    }
    rewrite (worker_PickValue_app_single (sublist 0 i values) best_prefix
               v best_take)
      by exact Hbest_prefix_len_values.
    rewrite Hbest_prefix_value.
    lia.
Qed.

Lemma MKItemResidueProgress_complete_implies_MKDPTable_next_item :
  forall weights values counts i capacity old dp r w v cnt,
    0 <= i < Zlength weights ->
    Zlength values = Zlength weights ->
    Zlength counts = Zlength weights ->
    w = Znth i weights 0 ->
    v = Znth i values 0 ->
    cnt = Znth i counts 0 ->
    (forall idx, 0 <= idx < Zlength weights -> 1 <= Znth idx weights 0) ->
    r >= w ->
    MKDPTable weights values counts i capacity old ->
    MKItemResidueProgress old dp r w v cnt capacity ->
    MKDPTable weights values counts (i + 1) capacity dp.
Proof.
  intros weights values counts i capacity old dp r w v cnt
    Hi Hvalues_len Hcounts_len Hw Hv Hcnt Hweights_pos Hr_ge Hdp Hprogress.
  unfold MKItemResidueProgress in Hprogress.
  destruct Hprogress as
    (Hw_pos & Hcnt_nonneg & Hr_nonneg & Hr_le_w & Hr_le_cap &
     Hold_len & Hdp_len & Hdone & _).
  pose proof Hdp as Hdp_full.
  unfold MKDPTable in *.
  destruct Hdp as (Hi_old & Hcap_nonneg & Hold_len' & Hold_caps).
  split.
  - lia.
  - split.
    + exact Hcap_nonneg.
    + split.
      * exact Hdp_len.
      * intros cap Hcap_range.
    assert (Hr_eq : r = w) by lia.
    assert (Hcap_decomp : cap = cap mod w + (cap / w) * w).
    { pose proof (Z.div_mod cap w) as Hdiv.
      specialize (Hdiv ltac:(lia)).
      nia.
    }
    assert (Hrem_range : 0 <= cap mod w < r).
    { rewrite Hr_eq. apply Z.mod_pos_bound. lia. }
    assert (Hdiv_nonneg : 0 <= cap / w).
    { apply Z.div_pos; lia. }
    pose proof (Hdone (cap mod w) (cap / w) cap Hcap_decomp
                 Hrem_range Hdiv_nonneg Hcap_range) as Htransition.
    eapply MKTransitionValue_matches_bounded_pick_extension; eauto.
Qed.

Lemma MKDPTable_final_capacity_implies_MultipleKnapsackAnswer :
  forall weights values counts capacity dp n,
    Zlength weights = n ->
    Zlength values = n ->
    Zlength counts = n ->
    0 <= capacity ->
    MKDPTable weights values counts n capacity dp ->
    MultipleKnapsackAnswer weights values counts capacity (Znth capacity dp 0).
Proof.
  intros weights values counts capacity dp n Hweights Hvalues Hcounts Hcap Hdp.
  unfold MKDPTable in Hdp.
  destruct Hdp as [_ [_ [_ Hdp]]].
  specialize (Hdp capacity (conj Hcap (Z.le_refl capacity))).
  unfold MultipleKnapsackAnswer, MultipleKnapsackPrefixAnswer in *.
  replace (sublist 0 n weights) with weights in Hdp by
    (symmetry; apply sublist_self; symmetry; exact Hweights).
  replace (sublist 0 n values) with values in Hdp by
    (symmetry; apply sublist_self; symmetry; exact Hvalues).
  replace (sublist 0 n counts) with counts in Hdp by
    (symmetry; apply sublist_self; symmetry; exact Hcounts).
  exact Hdp.
Qed.

Lemma MKQueuePending_layers_push__g08 :
  forall old q_idx q_val head tail r w v cnt k capacity current,
    MKQueueDropSafety old q_idx q_val head tail r w k capacity ->
    MKQueuePendingSemantics old q_idx q_val head tail r w v cnt k current ->
    current = Znth (r + k * w) old 0 - k * v ->
    0 <= r + k * w <= capacity ->
    0 <= cnt ->
    k <= capacity ->
    (head < tail -> Znth (tail - 1) q_val 0 > current) ->
    MKQueueResultSafety old
      (replace_Znth tail k q_idx) (replace_Znth tail current q_val)
      head (tail + 1) r w (k + 1) capacity /\
    MKQueueResultSemantics old
      (replace_Znth tail k q_idx) (replace_Znth tail current q_val)
      head (tail + 1) r w v cnt (k + 1) capacity.
Proof.
  intros old q_idx q_val head tail r w v cnt k capacity current
    Hsafe Hsem Hcurrent Hpos Hcnt Hk Htail.
  assert (Hpending :
    MKQueuePendingState old q_idx q_val head tail r w v cnt k capacity current).
  {
    unfold MKQueuePendingState, MKQueueDropSafety, MKQueueStorageSafety,
      MKQueuePendingSemantics in *.
    tauto.
  }
  pose proof (MKQueuePendingState_push_to_MKQueueState
    old q_idx q_val head tail r w v cnt k capacity current
    Hpending Hcurrent Hpos Hcnt Hk Htail) as Hstate.
  unfold MKQueueState, MKQueueResultSafety, MKQueueStorageSafety,
    MKQueueResultSemantics, MKTransitionValue, MKTransitionSafety,
    MKTransitionSemantics in *.
  tauto.
Qed.
Lemma MKResidueLoopSemantics_after_dp_write__g09 :
  forall old dp qidx qval r w v cnt k head tail capacity pos ans,
    0 <= r ->
    0 < w ->
    pos = r + k * w ->
    0 <= pos <= capacity ->
    Zlength dp = capacity + 1 ->
    MKItemResiduePrefixSemantics old dp r w v cnt k capacity ->
    MKQueueResultSemantics old qidx qval head tail r w v cnt (k + 1) capacity ->
    MKTransitionSemantics old w v cnt capacity pos ans ->
    MKResidueLoopSemantics old (replace_Znth pos ans dp) qidx qval
      r w v cnt (k + 1) head tail capacity.
Proof.
  intros old dp qidx qval r w v cnt k head tail capacity pos ans
    Hr Hw Hpos Hpos_range Hdp_len Hprefix Hqueue Htrans.
  unfold MKItemResiduePrefixSemantics in Hprefix.
  unfold MKResidueLoopSemantics.
  destruct Hprefix as [Hpref _].
  split; [|exact Hqueue].
  intros t Ht Hcap.
  destruct (Z_lt_ge_dec t k) as [Ht_old | Ht_new].
  - specialize (Hpref t ltac:(lia) Hcap).
    rewrite Znth_replace_Znth_Diff.
    + exact Hpref.
    + rewrite Hdp_len; lia.
    + rewrite Hdp_len; lia.
    + subst pos; nia.
  - assert (t = k) by lia.
    subst t.
    replace (r + k * w) with pos by lia.
    rewrite Znth_replace_Znth_Same.
    + exact Htrans.
    + rewrite Hdp_len; lia.
Qed.
Lemma MKResidueLoopSafety_after_dp_write__g09 :
  forall old dp qidx qval r w k head tail capacity pos ans,
    Zlength dp = capacity + 1 ->
    MKQueueResultSafety old qidx qval head tail r w (k + 1) capacity ->
    MKResidueLoopSafety old (replace_Znth pos ans dp) qidx qval
      r w (k + 1) head tail capacity.
Proof.
  intros old dp qidx qval r w k head tail capacity pos ans Hdp Hqueue.
  unfold MKQueueResultSafety, MKQueueStorageSafety in Hqueue.
  unfold MKResidueLoopSafety.
  destruct Hqueue as (Hr & Hk & Hheadtail & Htail & _ & Hqidx & Hqval & Hold).
  repeat split; try lia; try assumption.
  rewrite Zlength_replace_Znth; exact Hdp.
Qed.
Lemma MKItemResiduePrefixSemantics_after_dp_write__g09 :
  forall old dp r w v cnt k capacity pos ans,
    0 < w ->
    0 <= r ->
    r < w ->
    pos = r + k * w ->
    0 <= pos <= capacity ->
    Zlength dp = capacity + 1 ->
    MKItemResiduePrefixSemantics old dp r w v cnt k capacity ->
    MKTransitionSemantics old w v cnt capacity pos ans ->
    MKItemResiduePrefixSemantics old (replace_Znth pos ans dp)
      r w v cnt (k + 1) capacity.
Proof.
  intros old dp r w v cnt k capacity pos ans Hw Hr Hr_w Hpos Hpos_range Hdp_len Hprog Htrans.
  unfold MKItemResiduePrefixSemantics in *.
  destruct Hprog as [Hprefix Hrest].
  split.
  - intros t Ht Hcap.
    destruct (Z_lt_ge_dec t k) as [Ht_old | Ht_new].
    + specialize (Hprefix t ltac:(lia) Hcap).
      rewrite Znth_replace_Znth_Diff.
      * exact Hprefix.
      * rewrite Hdp_len; lia.
      * rewrite Hdp_len; lia.
      * subst pos; nia.
    + assert (t = k) by lia.
      subst t.
      replace (r + k * w) with pos by lia.
      rewrite Znth_replace_Znth_Same.
      * exact Htrans.
      * rewrite Hdp_len; lia.
  - intros p Hp_range.
    specialize (Hrest p Hp_range) as [Hdone Hsame].
    split.
    + intros rem t Hp_eq Hrem_range Ht.
      specialize (Hdone rem t Hp_eq Hrem_range Ht).
      rewrite Znth_replace_Znth_Diff.
      * exact Hdone.
      * rewrite Hdp_len; lia.
      * rewrite Hdp_len; lia.
      * intro Heq.
        assert (rem + t * w = r + k * w) as Hrepr by (subst p; subst pos; lia).
        assert (rem = r) as Hrem_eq.
        { eapply residue_repr_unique with (t1 := t) (t2 := k) (w := w);
            try eassumption; lia. }
        lia.
    + intros rem t Hp_eq Hrem_range Ht Hcase.
      assert (r < rem \/ rem = r /\ k <= t) as Hold_case by lia.
      specialize (Hsame rem t Hp_eq Hrem_range Ht Hold_case).
      rewrite Znth_replace_Znth_Diff.
      * exact Hsame.
      * rewrite Hdp_len; lia.
      * rewrite Hdp_len; lia.
      * intro Heq.
        assert (rem + t * w = r + k * w) as Hrepr by (subst p; subst pos; lia).
        assert (rem = r) as Hrem_eq.
        { eapply residue_repr_unique with (t1 := t) (t2 := k) (w := w);
            try eassumption; lia. }
        subst rem.
        destruct Hcase as [Hcase | [_ Ht_ge]]; nia.
Qed.
Lemma MKItemResiduePrefixSafety_after_dp_write__g09 :
  forall old dp r w cnt k capacity pos ans,
    Zlength dp = capacity + 1 ->
    MKItemResiduePrefixSafety old dp r w cnt k capacity ->
    MKItemResiduePrefixSafety old (replace_Znth pos ans dp)
      r w cnt (k + 1) capacity.
Proof.
  intros old dp r w cnt k capacity pos ans Hdp Hsafe.
  unfold MKItemResiduePrefixSafety in *.
  destruct Hsafe as (Hw & Hcnt & Hr & Hk & Hrcap & Hold & _).
  repeat split; try lia; try assumption.
  rewrite Zlength_replace_Znth; exact Hdp.
Qed.
Lemma MKItemResidueProgressSemantics_next_residue__g09 :
  forall old dp r w v cnt k capacity pos,
    0 < w ->
    0 <= r ->
    pos = r + k * w ->
    pos > capacity ->
    MKItemResiduePrefixSemantics old dp r w v cnt k capacity ->
    MKItemResidueProgressSemantics old dp (r + 1) w v cnt capacity.
Proof.
  intros old dp r w v cnt k capacity pos Hw Hr Hpos Hpast Hprog.
  unfold MKItemResiduePrefixSemantics in Hprog.
  destruct Hprog as [Hpref Hrest].
  unfold MKItemResidueProgressSemantics.
  split.
  - intros rem t p Hp_eq Hrem_range Ht Hp_range.
    assert (rem < r \/ rem = r) as [Hrem_lt | Hrem_eq] by lia.
    + specialize (Hrest p Hp_range) as [Hdone _].
      exact (Hdone rem t Hp_eq (conj (proj1 Hrem_range) Hrem_lt) Ht).
    + subst rem.
      assert (t < k) by (subst pos; subst p; nia).
      replace p with (r + t * w) by lia.
      eapply Hpref; lia.
  - intros rem t p Hp_eq Hrem_range Ht Hp_range.
    specialize (Hrest p Hp_range) as [_ Hsame].
    assert (Hcase : r < rem \/ (rem = r /\ k <= t)) by (left; lia).
    assert (Hrem0 : 0 <= rem) by lia.
    exact (Hsame rem t Hp_eq (conj Hrem0 (proj2 Hrem_range)) Ht Hcase).
Qed.
Lemma MKItemResidueProgressSafety_next_residue__g09 :
  forall old dp r w cnt k capacity pos,
    pos > capacity ->
    MKItemResiduePrefixSafety old dp r w cnt k capacity ->
    MKItemResidueProgressSafety old dp (r + 1) w cnt capacity.
Proof.
  intros old dp r w cnt k capacity pos Hpast Hsafe.
  unfold MKItemResiduePrefixSafety in Hsafe.
  unfold MKItemResidueProgressSafety.
  destruct Hsafe as (Hw & Hcnt & Hr & Hk & Hrcap & Hold & Hdp).
  repeat split; try lia; assumption.
Qed.
Lemma MKDPTable_from_safety_semantics__g10 :
  forall weights values counts i capacity dp,
    MKDPTableSafety weights i capacity dp ->
    MKDPTableSemantics weights values counts i capacity dp ->
    MKDPTable weights values counts i capacity dp.
Proof.
  intros weights values counts i capacity dp Hsafe Hsem.
  unfold MKDPTableSafety in Hsafe.
  unfold MKDPTableSemantics in Hsem.
  unfold MKDPTable.
  destruct Hsafe as (Hi & Hcapacity & Hlength).
  split; [exact Hi |].
  split; [exact Hcapacity |].
  split; assumption.
Qed.
Lemma MKItemResidueProgress_from_safety_semantics__g10 :
  forall old dp r w v cnt capacity,
    MKItemResidueProgressSafety old dp r w cnt capacity ->
    MKItemResidueProgressSemantics old dp r w v cnt capacity ->
    MKItemResidueProgress old dp r w v cnt capacity.
Proof.
  intros old dp r w v cnt capacity Hsafe Hsem.
  unfold MKItemResidueProgressSafety in Hsafe.
  unfold MKItemResidueProgressSemantics in Hsem.
  unfold MKItemResidueProgress.
  destruct Hsafe as
    (Hw & Hcnt & Hr0 & Hrw & Hrcap & Holdlen & Hdplen).
  destruct Hsem as (Hdone & Htodo).
  split; [exact Hw |].
  split; [exact Hcnt |].
  split; [exact Hr0 |].
  split; [exact Hrw |].
  split; [exact Hrcap |].
  split; [exact Holdlen |].
  split; [exact Hdplen |].
  split.
  - intros rem k pos Hpos Hrem Hk Hposrange.
    specialize (Hdone rem k pos Hpos Hrem Hk Hposrange).
    unfold MKTransitionValue.
    split; [exact Hw |].
    split; [exact Hcnt |].
    split; [exact Hposrange |].
    split; assumption.
  - exact Htodo.
Qed.

Lemma MKQueuePending_push_complete_outcome__g06 :
  forall old q_idx q_val head tail r w v cnt k capacity current pos,
    pos = r + k * w ->
    MKQueueDropSafety old q_idx q_val head tail r w k capacity ->
    MKQueuePendingSemantics old q_idx q_val head tail r w v cnt k current ->
    current = Znth pos old 0 - k * v ->
    0 <= pos <= capacity ->
    0 <= cnt ->
    k <= capacity ->
    (head < tail -> Znth (tail - 1) q_val 0 > current) ->
    MKQueueResultSafety old
      (replace_Znth tail k q_idx) (replace_Znth tail current q_val)
      head (tail + 1) r w (k + 1) capacity /\
    MKQueueResultSemantics old
      (replace_Znth tail k q_idx) (replace_Znth tail current q_val)
      head (tail + 1) r w v cnt (k + 1) capacity /\
    0 <= Znth head (replace_Znth tail current q_val) 0 + k * v <= 1000000 /\
    MKTransitionSafety old w cnt capacity pos /\
    MKTransitionSemantics old w v cnt capacity pos
      (Znth head (replace_Znth tail current q_val) 0 + k * v).
Proof.
  intros old q_idx q_val head tail r w v cnt k capacity current pos
    Hpos_eq Hsafe Hsem Hcurrent Hpos Hcnt Hk Htail.
  assert (Hcurrent' : current = Znth (r + k * w) old 0 - k * v).
  { rewrite <- Hpos_eq. exact Hcurrent. }
  assert (Hpos' : 0 <= r + k * w <= capacity).
  { rewrite <- Hpos_eq. exact Hpos. }
  pose proof (MKQueuePending_layers_push__g08
    old q_idx q_val head tail r w v cnt k capacity current
    Hsafe Hsem Hcurrent' Hpos' Hcnt Hk Htail) as [Hresult_safe Hresult_sem].
  assert (Hnonempty : head < tail + 1).
  {
    pose proof Hsafe as Hshape.
    unfold MKQueueDropSafety, MKQueueStorageSafety in Hshape.
    destruct Hshape as (_ & _ & Hheadtail & _).
    lia.
  }
  assert (Htransition_safe : MKTransitionSafety old w cnt capacity pos).
  {
    unfold MKQueueDropSafety, MKQueueStorageSafety in Hsafe.
    unfold MKTransitionSafety.
    destruct Hsafe as (Hr & _ & _ & _ & _ & _ & _ & Holdlen).
    repeat split; try lia; assumption.
  }
  pose proof Hresult_sem as Hresult_sem_full.
  unfold MKQueueResultSemantics in Hresult_sem.
  destruct Hresult_sem as
    (Hvalid & Hinc & Hdec & Hcovers & Hbound & Htransition).
  specialize (Hbound head (conj (Z.le_refl head) Hnonempty)).
  specialize (Htransition Hnonempty).
  replace (k + 1 - 1) with k in Hbound by lia.
  replace (r + (k + 1 - 1) * w) with pos in Htransition by lia.
  replace (k + 1 - 1) with k in Htransition by lia.
  split; [exact Hresult_safe |].
  split; [exact Hresult_sem_full |].
  split; [exact Hbound |].
  split; assumption.
Qed.
Lemma MKItemResidue_complete_table__g09 :
  forall weights values counts i capacity old dp r w v cnt,
    0 <= i < Zlength weights ->
    Zlength values = Zlength weights ->
    Zlength counts = Zlength weights ->
    w = Znth i weights 0 ->
    v = Znth i values 0 ->
    cnt = Znth i counts 0 ->
    (forall idx, 0 <= idx < Zlength weights -> 1 <= Znth idx weights 0) ->
    r >= w ->
    MKDPTableSafety weights i capacity old ->
    MKDPTableSemantics weights values counts i capacity old ->
    MKItemResidueProgressSafety old dp r w cnt capacity ->
    MKItemResidueProgressSemantics old dp r w v cnt capacity ->
    MKDPTableSafety weights (i + 1) capacity dp /\
    MKDPTableSemantics weights values counts (i + 1) capacity dp.
Proof.
  intros weights values counts i capacity old dp r w v cnt
    Hi Hvalues_len Hcounts_len Hw Hv Hcnt Hweights_pos Hr_ge
    Htable_safe Htable_sem Hprogress_safe Hprogress_sem.
  pose proof (MKDPTable_from_safety_semantics__g10
    weights values counts i capacity old Htable_safe Htable_sem) as Htable.
  pose proof (MKItemResidueProgress_from_safety_semantics__g10
    old dp r w v cnt capacity Hprogress_safe Hprogress_sem) as Hprogress.
  pose proof (MKItemResidueProgress_complete_implies_MKDPTable_next_item
    weights values counts i capacity old dp r w v cnt
    Hi Hvalues_len Hcounts_len Hw Hv Hcnt Hweights_pos Hr_ge
    Htable Hprogress) as Hnext.
  unfold MKDPTable in Hnext.
  unfold MKDPTableSafety, MKDPTableSemantics.
  tauto.
Qed.
