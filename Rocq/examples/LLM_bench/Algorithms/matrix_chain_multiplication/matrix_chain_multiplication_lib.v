From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MatrixChainDimensionsBounded
    (dimensions : list Z) (matrix_count : Z) : Prop :=
  Zlength dimensions = matrix_count + 1 /\
  forall i, 0 <= i <= matrix_count ->
    1 <= Znth i dimensions 0 <= 100.

Inductive MatrixChainPlan
    (dimensions : list Z) : Z -> Z -> Z -> Prop :=
  | MatrixChainPlan_single :
      forall left,
        0 <= left ->
        left + 1 < Zlength dimensions ->
        MatrixChainPlan dimensions left left 0
  | MatrixChainPlan_join :
      forall left split right left_cost right_cost,
        0 <= left ->
        left <= split < right ->
        right + 1 < Zlength dimensions ->
        MatrixChainPlan dimensions left split left_cost ->
        MatrixChainPlan dimensions (split + 1) right right_cost ->
        MatrixChainPlan dimensions left right
          (left_cost + right_cost +
           Znth left dimensions 0 *
           Znth (split + 1) dimensions 0 *
           Znth (right + 1) dimensions 0).

Definition MatrixChainIntervalMinimum
    (dimensions : list Z) (left right answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun scalar_cost =>
       MatrixChainPlan dimensions left right scalar_cost)
    (fun scalar_cost => scalar_cost)
    answer.

Definition MatrixChainMinimumCost
    (dimensions : list Z) (matrix_count answer : Z) : Prop :=
  Zlength dimensions = matrix_count + 1 /\
  MatrixChainIntervalMinimum dimensions 0 (matrix_count - 1) answer.

Definition MatrixChainTableResult
    (dimensions table : list Z) (matrix_count : Z) : Prop :=
  Zlength table = matrix_count * matrix_count /\
  forall left right,
    0 <= left /\ left <= right /\ right < matrix_count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * matrix_count + right) table 0).

Definition MatrixChainZeroPrefix (table : list Z) (done : Z) : Prop :=
  Zlength table = done /\
  forall index, 0 <= index < done -> Znth index table 0 = 0.

Definition MatrixChainTableValuesBounded (table : list Z) : Prop :=
  forall index, 0 <= index < Zlength table ->
    0 <= Znth index table 0 <= 7000000.

Definition MatrixChainLengthsDone
    (dimensions table : list Z) (matrix_count next_length : Z) : Prop :=
  1 <= next_length /\
  forall length left right,
    1 <= length < next_length ->
    right = left + length - 1 ->
    0 <= left ->
    left + length <= matrix_count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * matrix_count + right) table 0).

Definition MatrixChainLeftProgress
    (dimensions table : list Z)
    (matrix_count length next_left : Z) : Prop :=
  MatrixChainLengthsDone dimensions table matrix_count length /\
  forall left right,
    0 <= left < next_left ->
    right = left + length - 1 ->
    left + length <= matrix_count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * matrix_count + right) table 0).

Definition MatrixChainSplitCandidate
    (dimensions table : list Z)
    (width left right split candidate : Z) : Prop :=
  candidate =
    Znth (left * width + split) table 0 +
    Znth ((split + 1) * width + right) table 0 +
    Znth left dimensions 0 *
    Znth (split + 1) dimensions 0 *
    Znth (right + 1) dimensions 0.

Definition MatrixChainSplitProgress
    (dimensions table : list Z)
    (matrix_count width length left next_split best : Z) : Prop :=
  MatrixChainLeftProgress dimensions table matrix_count length left /\
  let right := left + length - 1 in
  min_value_of_subset Z.le
    (fun candidate =>
       exists split,
         left <= split < next_split /\
         MatrixChainSplitCandidate
           dimensions table width left right split candidate)
    (fun candidate => candidate)
    best.

From Coq Require Import Lia.
Lemma matrix_chain_zero_table_lengths_done__initialization :
  forall dimensions table matrix_count,
    1 <= matrix_count ->
    Zlength dimensions = matrix_count + 1 ->
    MatrixChainZeroPrefix table (matrix_count * matrix_count) ->
    MatrixChainLengthsDone dimensions table matrix_count 2.
Proof.
  intros dimensions table matrix_count Hcount Hdims Hzero.
  destruct Hzero as [Htable Hentries].
  unfold MatrixChainLengthsDone.
  split; [lia |].
  intros length left right Hlength Hright Hleft Hfits.
  assert (length = 1) by lia. subst length.
  assert (right = left) by lia. subst right.
  assert (Hindex : 0 <= left * matrix_count + left <
                   matrix_count * matrix_count) by nia.
  unfold MatrixChainIntervalMinimum, min_value_of_subset.
  replace (left + 1 - 1) with left by lia.
  rewrite (Hentries (left * matrix_count + left) Hindex).
  exists 0.
  split; [| reflexivity].
  unfold min_object_of_subset.
  split.
  - constructor; lia.
  - intros scalar_cost Hplan.
    inversion Hplan; subst; lia.
Qed.
Lemma matrix_chain_plan_linear_upper_bound__candidate_progress :
  forall dimensions matrix_count left right,
    MatrixChainDimensionsBounded dimensions matrix_count ->
    0 <= left ->
    left <= right ->
    right < matrix_count ->
    exists cost,
      MatrixChainPlan dimensions left right cost /\
      cost <= (right - left) * 1000000.
Proof.
  intros dimensions matrix_count.
  intros left right Hdimensions Hleft Horder Hright.
  remember (Z.to_nat (right - left)) as span eqn:Hspan.
  revert left right Hleft Horder Hright Hspan.
  induction span as [| span IH].
  - intros left right Hleft Horder Hright Hspan.
    assert (Hdifference : right - left = 0).
    {
      rewrite <- (Z2Nat.id (right - left)) by lia.
      rewrite <- Hspan.
      reflexivity.
    }
    assert (Hsame : right = left) by lia.
    subst right.
    exists 0.
    split.
    + apply MatrixChainPlan_single.
      * exact Hleft.
      * destruct Hdimensions as [Hlength _].
        rewrite Hlength.
        lia.
    + lia.
  - intros left right Hleft Horder Hright Hspan.
    assert (Hdifference : right - left = Z.of_nat (S span)).
    {
      rewrite <- (Z2Nat.id (right - left)) by lia.
      f_equal.
      symmetry.
      exact Hspan.
    }
    assert (Hstrict : left < right) by lia.
    assert (Hrecursive_span : Z.to_nat (right - (left + 1)) = span).
    {
      apply Nat2Z.inj.
      rewrite Z2Nat.id by lia.
      simpl in Hdifference.
      lia.
    }
    destruct (IH (left + 1) right ltac:(lia) ltac:(lia) Hright
                 (eq_sym Hrecursive_span))
      as [right_cost [Hright_plan Hright_cost]].
    destruct Hdimensions as [Hlength Hbounds].
    pose proof (Hbounds left ltac:(lia)) as Hdim_left.
    pose proof (Hbounds (left + 1) ltac:(lia)) as Hdim_middle.
    pose proof (Hbounds (right + 1) ltac:(lia)) as Hdim_right.
    exists
      (0 + right_cost +
       Znth left dimensions 0 *
       Znth (left + 1) dimensions 0 *
       Znth (right + 1) dimensions 0).
    split.
    + eapply MatrixChainPlan_join with
          (split := left) (left_cost := 0) (right_cost := right_cost).
      * exact Hleft.
      * lia.
      * rewrite Hlength. lia.
      * apply MatrixChainPlan_single.
        -- exact Hleft.
        -- rewrite Hlength. lia.
      * exact Hright_plan.
    + assert (Htwo_dimensions :
        Znth left dimensions 0 * Znth (left + 1) dimensions 0 <= 10000)
        by nia.
      assert (Hproduct :
        Znth left dimensions 0 *
        Znth (left + 1) dimensions 0 *
        Znth (right + 1) dimensions 0 <= 1000000)
        by nia.
      simpl in Hdifference.
      nia.
Qed.
Lemma matrix_chain_interval_minimum_upper_bound__candidate_progress :
  forall dimensions matrix_count left right answer,
    MatrixChainDimensionsBounded dimensions matrix_count ->
    0 <= left ->
    left <= right ->
    right < matrix_count ->
    MatrixChainIntervalMinimum dimensions left right answer ->
    answer <= (right - left) * 1000000.
Proof.
  intros dimensions matrix_count left right answer
    Hdimensions Hleft Horder Hright Hminimum.
  destruct
    (matrix_chain_plan_linear_upper_bound__candidate_progress
       dimensions matrix_count left right Hdimensions Hleft Horder Hright)
    as [canonical [Hcanonical Hcanonical_bound]].
  unfold MatrixChainIntervalMinimum, min_value_of_subset,
    min_object_of_subset in Hminimum.
  destruct Hminimum as [optimal [[Hoptimal Hleast] Hanswer]].
  cbn in Hanswer.
  subst answer.
  pose proof (Hleast canonical Hcanonical) as Hoptimal_bound.
  cbn in Hoptimal_bound.
  lia.
Qed.
Lemma matrix_chain_split_progress_initial__candidate_progress :
  forall dimensions table matrix_count width length left,
    MatrixChainLeftProgress dimensions table matrix_count length left ->
    MatrixChainSplitProgress
      dimensions table matrix_count width length left (left + 1)
      (Znth (left * width + left) table 0 +
       Znth ((left + 1) * width + (left + length - 1)) table 0 +
       Znth left dimensions 0 *
       Znth (left + 1) dimensions 0 *
       Znth ((left + length - 1) + 1) dimensions 0).
Proof.
  intros dimensions table matrix_count width length left Hleft_progress.
  unfold MatrixChainSplitProgress.
  split; [exact Hleft_progress |].
  cbn.
  unfold min_value_of_subset, min_object_of_subset.
  eexists.
  split.
  - split.
    + exists left.
      split; [lia |].
      unfold MatrixChainSplitCandidate.
      reflexivity.
    + intros candidate [split [Hsplit Hcandidate]].
      assert (split = left) by lia.
      subst split.
      unfold MatrixChainSplitCandidate in Hcandidate.
      cbn in Hcandidate.
      subst candidate.
      lia.
  - reflexivity.
Qed.
Lemma matrix_chain_split_progress_better__min_update :
  forall dimensions table matrix_count width length left split best candidate,
    left <= split ->
    candidate < best ->
    MatrixChainSplitCandidate dimensions table width left
      (left + length - 1) split candidate ->
    MatrixChainSplitProgress dimensions table matrix_count width
      length left split best ->
    MatrixChainSplitProgress dimensions table matrix_count width
      length left (split + 1) candidate.
Proof.
  intros dimensions table matrix_count width length left split best candidate
    Hleftsplit Hbetter Hcandidate Hprogress.
  unfold MatrixChainSplitProgress in *; cbn in *.
  destruct Hprogress as [Hleft Hminimum].
  split; [exact Hleft |].
  rewrite <- (min_l Z.le best candidate) by lia.
  eapply (min_union_1_right Z.le best candidate candidate
    (fun value : Z => value)
    (fun value => exists root,
      left <= root < split /\
      MatrixChainSplitCandidate dimensions table width left
        (left + length - 1) root value)
    (fun value => exists root,
      left <= root < split + 1 /\
      MatrixChainSplitCandidate dimensions table width left
        (left + length - 1) root value)).
  - exact Hminimum.
  - reflexivity.
  - intros value; split.
    + intros (root & Hbounds & Hroot).
      destruct (Z_lt_ge_dec root split) as [Hlt | Hge].
      * left. exists root. split; [lia | exact Hroot].
      * right.
        assert (root = split) by lia; subst root.
        unfold MatrixChainSplitCandidate in *; lia.
    + intros [(root & Hbounds & Hroot) | Heq].
      * exists root. split; [lia | exact Hroot].
      * subst value. exists split. split; [lia | exact Hcandidate].
Qed.
Lemma matrix_chain_split_progress_not_better__min_update :
  forall dimensions table matrix_count width length left split best candidate,
    left <= split ->
    best <= candidate ->
    MatrixChainSplitCandidate dimensions table width left
      (left + length - 1) split candidate ->
    MatrixChainSplitProgress dimensions table matrix_count width
      length left split best ->
    MatrixChainSplitProgress dimensions table matrix_count width
      length left (split + 1) best.
Proof.
  intros dimensions table matrix_count width length left split best candidate
    Hleftsplit Hnotbetter Hcandidate Hprogress.
  unfold MatrixChainSplitProgress in *; cbn in *.
  destruct Hprogress as [Hleft Hminimum].
  split; [exact Hleft |].
  rewrite <- (min_r Z.le best candidate) by lia.
  eapply (min_union_1_right Z.le best candidate candidate
    (fun value : Z => value)
    (fun value => exists root,
      left <= root < split /\
      MatrixChainSplitCandidate dimensions table width left
        (left + length - 1) root value)
    (fun value => exists root,
      left <= root < split + 1 /\
      MatrixChainSplitCandidate dimensions table width left
        (left + length - 1) root value)).
  - exact Hminimum.
  - reflexivity.
  - intros value; split.
    + intros (root & Hbounds & Hroot).
      destruct (Z_lt_ge_dec root split) as [Hlt | Hge].
      * left. exists root. split; [lia | exact Hroot].
      * right.
        assert (root = split) by lia; subst root.
        unfold MatrixChainSplitCandidate in *; lia.
    + intros [(root & Hbounds & Hroot) | Heq].
      * exists root. split; [lia | exact Hroot].
      * subst value. exists split. split; [lia | exact Hcandidate].
Qed.
Lemma matrix_chain_split_progress_complete__min_update :
  forall dimensions table matrix_count length left right best,
    2 <= length ->
    0 <= left ->
    right = left + length - 1 ->
    right < matrix_count ->
    right + 1 < Zlength dimensions ->
    MatrixChainSplitProgress dimensions table matrix_count matrix_count
      length left right best ->
    MatrixChainIntervalMinimum dimensions left right best.
Proof.
  intros dimensions table matrix_count length left right best
    Hlength Hleft Hright Hrightbound Hdimensionbound Hprogress.
  subst right.
  unfold MatrixChainSplitProgress in Hprogress; cbn in Hprogress.
  destruct Hprogress as [[Hdone Hleftprogress] Hminimum].
  unfold MatrixChainIntervalMinimum.
  destruct Hminimum as
    [candidate [[[root [[Hrootleft Hrootright] Hcandidate]] Hcandidateleast]
                Hcandidatebest]].
  assert (Hleftminimum :
    MatrixChainIntervalMinimum dimensions left root
      (Znth (left * matrix_count + root) table 0)).
  {
    eapply Hdone with (length := root - left + 1); lia.
  }
  assert (Hrightminimum :
    MatrixChainIntervalMinimum dimensions (root + 1)
      (left + length - 1)
      (Znth ((root + 1) * matrix_count + (left + length - 1)) table 0)).
  {
    eapply Hdone with (length := left + length - 1 - root); lia.
  }
  unfold MatrixChainIntervalMinimum in Hleftminimum, Hrightminimum.
  destruct Hleftminimum as
    [left_cost [[Hleftplan Hleftleast] Hleftcost]].
  destruct Hrightminimum as
    [right_cost [[Hrightplan Hrightleast] Hrightcost]].
  exists candidate.
  split.
  - split.
    + unfold MatrixChainSplitCandidate in Hcandidate.
      rewrite Hcandidate.
      rewrite <- Hleftcost, <- Hrightcost.
      eapply MatrixChainPlan_join with
        (split := root) (left_cost := left_cost) (right_cost := right_cost);
        eauto; lia.
    + intros arbitrary_plan Harbitrary.
      inversion Harbitrary as
        [single_left Hsingleleft Hsingledim
        | join_left join_split join_right join_left_cost join_right_cost
          Hjoinleft Hjoinbounds Hjoindim Hjoinleftplan Hjoinrightplan];
        subst.
      * lia.
      * assert (Hjoinleftminimum :
          MatrixChainIntervalMinimum dimensions left join_split
            (Znth (left * matrix_count + join_split) table 0)).
        {
          eapply Hdone with (length := join_split - left + 1); lia.
        }
        assert (Hjoinrightminimum :
          MatrixChainIntervalMinimum dimensions (join_split + 1)
            (left + length - 1)
            (Znth ((join_split + 1) * matrix_count +
                    (left + length - 1)) table 0)).
        {
          eapply Hdone with
            (length := left + length - 1 - join_split); lia.
        }
        unfold MatrixChainIntervalMinimum in
          Hjoinleftminimum, Hjoinrightminimum.
        destruct Hjoinleftminimum as
          [join_left_opt [[Hjoinleftlegal Hjoinleftleast]
                          Hjoinleftcost]].
        destruct Hjoinrightminimum as
          [join_right_opt [[Hjoinrightlegal Hjoinrightleast]
                           Hjoinrightcost]].
        specialize (Hjoinleftleast join_left_cost Hjoinleftplan).
        specialize (Hjoinrightleast join_right_cost Hjoinrightplan).
        specialize (Hcandidateleast
          (Znth (left * matrix_count + join_split) table 0 +
           Znth ((join_split + 1) * matrix_count +
                 (left + length - 1)) table 0 +
           Znth left dimensions 0 *
           Znth (join_split + 1) dimensions 0 *
           Znth ((left + length - 1) + 1) dimensions 0)).
        assert (Hjoincandidate :
          exists split,
            left <= split < left + length - 1 /\
            MatrixChainSplitCandidate dimensions table matrix_count left
              (left + length - 1) split
              (Znth (left * matrix_count + join_split) table 0 +
               Znth ((join_split + 1) * matrix_count +
                     (left + length - 1)) table 0 +
               Znth left dimensions 0 *
               Znth (join_split + 1) dimensions 0 *
               Znth ((left + length - 1) + 1) dimensions 0)).
        {
          exists join_split. split; [lia |].
          unfold MatrixChainSplitCandidate. reflexivity.
        }
        specialize (Hcandidateleast Hjoincandidate).
        rewrite Hjoinleftcost in Hjoinleftleast.
        rewrite Hjoinrightcost in Hjoinrightleast.
        lia.
  - exact Hcandidatebest.
Qed.

(** Mathematical predicates exposed by the refactored annotation.  Existing
    helper lemmas retain their original internal premises for proof reuse. *)
Definition MatrixChainOptimalCost (dimensions : list Z) (count answer : Z) : Prop :=
  MatrixChainIntervalMinimum dimensions 0 (count - 1) answer.
Definition MatrixChainTableComplete (dimensions table : list Z) (count : Z) : Prop :=
  forall left right, 0 <= left /\ left <= right /\ right < count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * count + right) table 0).
Definition MatrixChainLengthsComplete (dimensions table : list Z) (count next : Z) : Prop :=
  forall len left right, 1 <= len < next -> right = left + len - 1 ->
    0 <= left -> left + len <= count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * count + right) table 0).
Definition MatrixChainLeftComplete (dimensions table : list Z) (count len next : Z) : Prop :=
  MatrixChainLengthsComplete dimensions table count len /\
  forall left right, 0 <= left < next -> right = left + len - 1 ->
    left + len <= count ->
    MatrixChainIntervalMinimum dimensions left right
      (Znth (left * count + right) table 0).
Definition MatrixChainSplitMinimum (dimensions table : list Z)
  (count width len left next best : Z) : Prop :=
  MatrixChainLeftComplete dimensions table count len left /\
  min_value_of_subset Z.le
    (fun candidate => exists split, left <= split < next /\
      MatrixChainSplitCandidate dimensions table width left (left + len - 1) split candidate)
    (fun candidate => candidate) best.
