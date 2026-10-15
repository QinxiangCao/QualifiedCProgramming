Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Definition ValidDelegation (students : list (Z*Z)) (chosen : Z -> Prop) : Prop :=
  (forall i, chosen i -> 0 <= i < Zlength students) /\
  exists size, size > 0 /\ forall subject,
    (exists i, chosen i /\ fst (Znth i students (0,0)) = subject) ->
    #(fun i : Z => 0 <= i < Zlength students /\
      chosen i /\ fst (Znth i students (0,0)) = subject) = size.
Definition DelegationSkill (students : list (Z*Z)) (chosen : Z -> Prop) : Z :=
  sum (fun i : Z => 0 <= i < Zlength students /\ chosen i)
    (fun i => snd (Znth i students (0,0))).
Definition Pre (m : Z) (students : list (Z*Z)) : Prop := 1 <= Zlength students <= 100000 /\ 1 <= m <= 100000 /\
  Forall (fun p => 1 <= fst p <= m /\ -10000 <= snd p <= 10000) students.
Definition Spec (m : Z) (students : list (Z*Z)) (out : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (ValidDelegation students) (DelegationSkill students) 0 out.

(** Mathematical observations used by the C sweep.  They describe the
    sorted candidate sequence and the contribution of completed subject
    blocks; none of them executes the C loops. *)
Definition CandidateSubject (students : list (Z * Z)) (i : Z) : Z :=
  fst (Znth i students (0, 0)).

Definition CandidateSkill (students : list (Z * Z)) (i : Z) : Z :=
  snd (Znth i students (0, 0)).

Definition CandidatesSorted (students : list (Z * Z)) : Prop :=
  forall i j,
    0 <= i /\ i < j /\ j < Zlength students ->
    CandidateSubject students i < CandidateSubject students j \/
    (CandidateSubject students i = CandidateSubject students j /\
     CandidateSkill students j <= CandidateSkill students i).

Definition SubjectBoundary (students : list (Z * Z)) (p : Z) : Prop :=
  0 <= p <= Zlength students /\
  (p = 0 \/ p = Zlength students \/
   CandidateSubject students (p - 1) <> CandidateSubject students p).

Definition SubjectBlockStart (students : list (Z * Z)) (p : Z) : Prop :=
  0 <= p < Zlength students /\
  (p = 0 \/
   CandidateSubject students (p - 1) <> CandidateSubject students p).

Definition SkillSum (students : list (Z * Z)) (lo hi : Z) : Z :=
  fold_right Z.add 0 (map snd (sublist lo hi students)).

Definition SubjectHasK
    (students : list (Z * Z)) (start k : Z) : Prop :=
  SubjectBlockStart students start /\
  1 <= k /\ start + k <= Zlength students /\
  forall t, start <= t < start + k ->
    CandidateSubject students t = CandidateSubject students start.

Definition SubjectContribution
    (students : list (Z * Z)) (start k : Z) : Z :=
  if prop_dec (SubjectHasK students start k)
  then Z.max 0 (SkillSum students start (start + k))
  else 0.

Definition CompletedContribution
    (students : list (Z * Z)) (processed k : Z) : Z :=
  sum
    (fun start : Z =>
       0 <= start < processed /\ SubjectBlockStart students start)
    (fun start => SubjectContribution students start k).

Definition CompetitionOuterState
    (students : list (Z * Z)) (processed : Z) (totals : list Z) : Prop :=
  SubjectBoundary students processed /\
  Zlength totals = Zlength students + 1 /\
  Znth 0 totals 0 = 0 /\
  forall k, 1 <= k <= Zlength students ->
    Znth k totals 0 = CompletedContribution students processed k.

Definition CompetitionInnerState
    (students : list (Z * Z)) (start done prefix : Z)
    (totals : list Z) : Prop :=
  0 <= start /\ start <= done /\ done <= Zlength students /\
  SubjectBoundary students start /\
  (start < done ->
   forall t, start <= t < done ->
     CandidateSubject students t = CandidateSubject students start) /\
  prefix = SkillSum students start done /\
  Zlength totals = Zlength students + 1 /\
  Znth 0 totals 0 = 0 /\
  forall k, 1 <= k <= Zlength students ->
    Znth k totals 0 =
      CompletedContribution students start k +
      (if prop_dec (1 <= k <= done - start)
       then SubjectContribution students start k
       else 0).

Definition CompetitionAnswerPrefix
    (totals : list Z) (n done answer : Z) : Prop :=
  Zlength totals = n + 1 /\ 0 <= done <= n /\
  max_value_of_subset_with_default Z.le
    (fun k : Z => 1 <= k <= done)
    (fun k => Znth k totals 0) 0 answer.

Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Lemma completed_contribution_at_zero__initialization :
  forall students k, CompletedContribution students 0 k = 0.
Proof.
  intros students k.
  unfold CompletedContribution.
  rewrite (SumLib.Sum.sum_ext
    (fun start : Z => 0 <= start < 0 /\ SubjectBlockStart students start)
    (fun start => SubjectContribution students start k)
    (fun _ => 0)).
  - apply SumLib.Sum.sum_zero.
  - intros start Hstart.
    lia.
Qed.
Lemma competition_inner_from_outer_empty__initialization :
  forall students i totals,
    CompetitionOuterState students i totals ->
    CompetitionInnerState students i i 0 totals.
Proof.
  intros students i totals Houter.
  unfold CompetitionOuterState in Houter.
  destruct Houter as [Hboundary [Hlength [Hzero Htotals]]].
  unfold CompetitionInnerState.
  refine (conj _ (conj _ (conj _ (conj Hboundary
    (conj _ (conj _ (conj Hlength (conj Hzero _)))))))).
  - unfold SubjectBoundary in Hboundary.
    lia.
  - lia.
  - unfold SubjectBoundary in Hboundary.
    lia.
  - lia.
  - unfold SkillSum.
    rewrite Zsublist_nil by lia.
    reflexivity.
  - intros k Hk.
    rewrite Htotals by exact Hk.
    destruct (prop_dec (1 <= k <= i - i)); lia.
Qed.
Lemma candidate_bounds_permutation__initialization :
  forall students sorted m default,
    Permutation students sorted ->
    (forall i, 0 <= i < Zlength students ->
      1 <= fst (Znth i students default) <= m /\
      -10000 <= snd (Znth i students default) <= 10000) ->
    forall i, 0 <= i < Zlength sorted ->
      1 <= fst (Znth i sorted default) <= m /\
      -10000 <= snd (Znth i sorted default) <= 10000.
Proof.
  intros students sorted m default Hperm Hbounds.
  assert (Hstudents : Forall
    (fun p => 1 <= fst p <= m /\ -10000 <= snd p <= 10000)
    students).
  {
    apply (proj2 (Forall_Znth
      (fun p => 1 <= fst p <= m /\ -10000 <= snd p <= 10000)
      default students)).
    exact Hbounds.
  }
  assert (Hsorted : Forall
    (fun p => 1 <= fst p <= m /\ -10000 <= snd p <= 10000)
    sorted).
  {
    eapply Permutation_Forall; eauto.
  }
  apply (proj1 (Forall_Znth
    (fun p => 1 <= fst p <= m /\ -10000 <= snd p <= 10000)
    default sorted)).
  exact Hsorted.
Qed.
Lemma Zlength_replace_Znth__inner_update :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros.
  revert n.
  induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma skill_sum_extend_same_subject__inner_update :
  forall (students : list (Z * Z)) start done,
    0 <= start <= done ->
    done < Zlength students ->
    SkillSum students start (done + 1) =
      SkillSum students start done + CandidateSkill students done.
Proof.
  intros students start done Hstart Hdone.
  unfold SkillSum, CandidateSkill.
  rewrite (sublist_split start (done + 1) done students) by lia.
  rewrite (sublist_single (0, 0) done students) by lia.
  rewrite map_app, fold_right_app.
  simpl.
  assert (Hfold : forall xs acc,
      fold_right Z.add acc xs = fold_right Z.add 0 xs + acc).
  { intros xs acc. induction xs as [|x xs IH]; simpl; lia. }
  rewrite Hfold.
  lia.
Qed.
Lemma subject_contribution_extend__inner_update :
  forall (students : list (Z * Z)) start done prefix totals,
    CompetitionInnerState students start done prefix totals ->
    done < Zlength students ->
    CandidateSubject students done = CandidateSubject students start ->
    SubjectContribution students start (done + 1 - start) =
      Z.max 0 (prefix + CandidateSkill students done).
Proof.
  intros students start done prefix totals Hstate Hdone Hsubject.
  unfold CompetitionInnerState in Hstate.
  destruct Hstate as
      [Hstart0 [Hstartdone [Hdonele [Hboundary [Hsame
       [Hprefix [Hlength [Hzero Htotals]]]]]]]].
  assert (Hblock : SubjectBlockStart students start).
  { unfold SubjectBoundary in Hboundary.
    unfold SubjectBlockStart.
    destruct Hboundary as [Hbounds Hcase].
    split; [lia |].
    destruct Hcase as [Hz | [Hend | Hneq]].
    - left; exact Hz.
    - exfalso; lia.
    - right; exact Hneq. }
  assert (Hhas : SubjectHasK students start (done + 1 - start)).
  { unfold SubjectHasK.
    split; [exact Hblock |].
    split; [lia |].
    split; [lia |].
    intros t Ht.
    replace (start + (done + 1 - start)) with (done + 1) in Ht by lia.
    destruct (Z_lt_ge_dec t done) as [Htdone | Hdonet].
    - apply Hsame; lia.
    - assert (t = done) by lia. subst t. exact Hsubject. }
  unfold SubjectContribution.
  destruct (Sum.prop_dec (SubjectHasK students start (done + 1 - start)))
    as [Hyes | Hno].
  - replace (start + (done + 1 - start)) with (done + 1) by lia.
    rewrite skill_sum_extend_same_subject__inner_update by lia.
    rewrite <- Hprefix.
    reflexivity.
  - contradiction.
Qed.
Lemma competition_inner_step_positive__inner_update :
  forall (students : list (Z * Z)) start done prefix totals skill,
    CompetitionInnerState students start done prefix totals ->
    done < Zlength students ->
    CandidateSubject students done = CandidateSubject students start ->
    skill = CandidateSkill students done ->
    0 < prefix + skill ->
    CompetitionInnerState students start (done + 1) (prefix + skill)
      (replace_Znth (done + 1 - start)
        (Znth (done + 1 - start) totals 0 + (prefix + skill)) totals).
Proof.
  intros students start done prefix totals skill Hstate Hdone Hsubject
    Hskill Hpositive.
  pose proof (subject_contribution_extend__inner_update
    students start done prefix totals Hstate Hdone Hsubject) as Hcontribution.
  unfold CompetitionInnerState in Hstate |- *.
  destruct Hstate as
      [Hstart0 [Hstartdone [Hdonele [Hboundary [Hsame
       [Hprefix [Hlength [Hzero Htotals]]]]]]]].
  split; [exact Hstart0 |].
  split; [lia |].
  split; [lia |].
  split; [exact Hboundary |].
  split.
  - intros Hlt t Ht.
    destruct (Z_lt_ge_dec t done) as [Htdone | Hdonet].
    + apply Hsame; lia.
    + assert (t = done) by lia. subst t. exact Hsubject.
  - split.
    + rewrite (skill_sum_extend_same_subject__inner_update students start done)
      by lia.
      lia.
    + split.
      * rewrite Zlength_replace_Znth__inner_update. exact Hlength.
      * split.
        -- rewrite Znth_replace_Znth_Diff; try lia; exact Hzero.
        -- intros k Hk.
           destruct (Z.eq_dec k (done + 1 - start)) as [Heq | Hneq].
           { subst k.
             rewrite Znth_replace_Znth_Same by lia.
             rewrite Htotals by lia.
             destruct (Sum.prop_dec (1 <= done + 1 - start <= done - start))
               as [Hold | Hold]; [lia |].
             simpl.
             rewrite Hcontribution.
             rewrite Hskill, Z.max_r by lia.
             destruct (Sum.prop_dec
               (1 <= done + 1 - start <= done + 1 - start))
               as [Hnew | Hnew].
             - lia.
             - exfalso; apply Hnew; lia. }
           { rewrite Znth_replace_Znth_Diff by lia.
             rewrite Htotals by exact Hk.
             destruct (Sum.prop_dec (1 <= k <= done - start)) as [Hold | Hold];
             destruct (Sum.prop_dec (1 <= k <= done + 1 - start)) as [Hnew | Hnew];
             try reflexivity; exfalso; lia. }
Qed.
Lemma competition_inner_step_nonpositive__inner_update :
  forall (students : list (Z * Z)) start done prefix totals skill,
    CompetitionInnerState students start done prefix totals ->
    done < Zlength students ->
    CandidateSubject students done = CandidateSubject students start ->
    skill = CandidateSkill students done ->
    prefix + skill <= 0 ->
    CompetitionInnerState students start (done + 1) (prefix + skill) totals.
Proof.
  intros students start done prefix totals skill Hstate Hdone Hsubject
    Hskill Hnonpositive.
  pose proof (subject_contribution_extend__inner_update
    students start done prefix totals Hstate Hdone Hsubject) as Hcontribution.
  unfold CompetitionInnerState in Hstate |- *.
  destruct Hstate as
      [Hstart0 [Hstartdone [Hdonele [Hboundary [Hsame
       [Hprefix [Hlength [Hzero Htotals]]]]]]]].
  split; [exact Hstart0 |].
  split; [lia |].
  split; [lia |].
  split; [exact Hboundary |].
  split.
  - intros Hlt t Ht.
    destruct (Z_lt_ge_dec t done) as [Htdone | Hdonet].
    + apply Hsame; lia.
    + assert (t = done) by lia. subst t. exact Hsubject.
  - split.
    + rewrite (skill_sum_extend_same_subject__inner_update students start done)
        by lia.
      lia.
    + split; [exact Hlength |].
      split; [exact Hzero |].
      intros k Hk.
      rewrite Htotals by exact Hk.
      destruct (Z.eq_dec k (done + 1 - start)) as [Heq | Hneq].
      * subst k.
        destruct (Sum.prop_dec (1 <= done + 1 - start <= done - start))
          as [Hold | Hold]; [lia |].
        simpl.
        rewrite Hcontribution, <- Hskill, Z.max_l by lia.
        destruct (Sum.prop_dec
          (1 <= done + 1 - start <= done + 1 - start)) as [Hnew | Hnew].
        -- lia.
        -- exfalso; apply Hnew; lia.
      * destruct (Sum.prop_dec (1 <= k <= done - start)) as [Hold | Hold];
        destruct (Sum.prop_dec (1 <= k <= done + 1 - start)) as [Hnew | Hnew];
        try reflexivity; exfalso; lia.
Qed.
Lemma fold_right_add_permutation__outer_advance {A : Type}
    (f : A -> Z) (xs ys : list A) :
  Permutation xs ys ->
  fold_right (fun x acc => f x + acc) 0 xs =
  fold_right (fun x acc => f x + acc) 0 ys.
Proof.
  intro Hperm.
  induction Hperm; simpl.
  - reflexivity.
  - rewrite IHHperm. reflexivity.
  - lia.
  - rewrite IHHperm1, IHHperm2. reflexivity.
Qed.
Lemma finite_sum_predicate_ext__outer_advance {A : Type}
    (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q) (f : A -> Z) :
  (forall x, P x <-> Q x) ->
  @sum A P FP f = @sum A Q FQ f.
Proof.
  intro Hequiv.
  unfold sum.
  apply fold_right_add_permutation__outer_advance.
  apply NoDup_Permutation.
  - apply enum_nodup.
  - apply enum_nodup.
  - intro x.
    rewrite <- !enum_ok.
    apply Hequiv.
Qed.
Lemma finite_sum_restrict__outer_advance {A : Type}
    (P Q : A -> Prop) (FP : Finite P) (f : A -> Z) :
  @sum A (fun x => P x /\ Q x) (@Finite_subset A P Q FP) f =
  @sum A P FP (fun x => if prop_dec (Q x) then f x else 0).
Proof.
  unfold sum.
  simpl.
  induction (@enum A P FP) as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (prop_dec (Q x)); simpl; rewrite IH; lia.
Qed.
Lemma sum_bounded_predicate_extend_point__outer_advance
    (P : Z -> Prop) (f : Z -> Z) (start done : Z) :
  0 <= start < done ->
  P start ->
  (forall x, start < x < done -> ~ P x) ->
  sum (fun x : Z => 0 <= x < done /\ P x) f =
  sum (fun x : Z => 0 <= x < start /\ P x) f + f start.
Proof.
  intros Hrange HPstart Hgap.
  set (PD := fun x : Z => 0 <= x < done /\ P x).
  transitivity
    (sum PD (fun x => if prop_dec (x < start) then f x else 0) +
     sum PD (fun x => if prop_dec (x = start) then f x else 0)).
  - rewrite <- sum_add.
    apply sum_ext.
    intros x [Hx HPx].
    destruct (prop_dec (x < start));
      destruct (prop_dec (x = start)); try lia.
    exfalso.
    apply (Hgap x ltac:(lia)).
    exact HPx.
  - f_equal.
    + rewrite <- (finite_sum_restrict__outer_advance
        PD (fun x => x < start) _ f).
      apply finite_sum_predicate_ext__outer_advance.
      intro x.
      unfold PD.
      split.
      * intros [[Hx HPx] Hlt]. split; [lia | exact HPx].
      * intros [Hx HPx]. split.
        -- split; [lia | exact HPx].
        -- lia.
    + rewrite <- (finite_sum_restrict__outer_advance
        PD (fun x => x = start) _ f).
      rewrite <- (sum_Z_range_single start f).
      apply finite_sum_predicate_ext__outer_advance.
      intro x.
      unfold PD.
      split.
      * intros [[Hx HPx] Heq]. subst x. lia.
      * intro Hx. assert (x = start) by lia. subst x. auto.
Qed.
Lemma subject_boundary_from_sorted_change__outer_advance :
  forall (students : list (Z * Z)) start done,
    CandidatesSorted students ->
    0 <= start < done ->
    done < Zlength students ->
    (forall t, start <= t < done ->
       CandidateSubject students t = CandidateSubject students start) ->
    CandidateSubject students done <> CandidateSubject students start ->
    SubjectBoundary students done.
Proof.
  intros students start done _ Hstart Hdone Hsame Hchange.
  unfold SubjectBoundary.
  split; [lia |].
  right; right.
  intro Heq.
  apply Hchange.
  rewrite <- Heq.
  apply Hsame.
  lia.
Qed.
Lemma subject_block_start_from_inner_start__outer_advance :
  forall (students : list (Z * Z)) start done,
    start < done ->
    done <= Zlength students ->
    SubjectBoundary students start ->
    SubjectBlockStart students start.
Proof.
  intros students start done Hlt Hdone Hboundary.
  unfold SubjectBoundary in Hboundary.
  unfold SubjectBlockStart.
  destruct Hboundary as [Hbounds Hcase].
  split; [lia |].
  destruct Hcase as [Hzero | [Hend | Hchange]].
  - left; exact Hzero.
  - lia.
  - right; exact Hchange.
Qed.
Lemma no_subject_block_start_inside_inner__outer_advance :
  forall (students : list (Z * Z)) start done x,
    0 <= start ->
    start < done ->
    (forall t, start <= t < done ->
       CandidateSubject students t = CandidateSubject students start) ->
    start < x < done ->
    ~ SubjectBlockStart students x.
Proof.
  intros students start done x Hstart Hlt Hsame Hx Hblock.
  unfold SubjectBlockStart in Hblock.
  destruct Hblock as [_ [Hzero | Hchange]].
  - lia.
  - apply Hchange.
    rewrite (Hsame (x - 1) ltac:(lia)).
    rewrite (Hsame x ltac:(lia)).
    reflexivity.
Qed.
Lemma completed_contribution_extend_inner__outer_advance :
  forall (students : list (Z * Z)) start done k,
    0 <= start ->
    start < done ->
    done <= Zlength students ->
    SubjectBoundary students start ->
    (forall t, start <= t < done ->
       CandidateSubject students t = CandidateSubject students start) ->
    CompletedContribution students done k =
      CompletedContribution students start k +
      SubjectContribution students start k.
Proof.
  intros students start done k Hstart Hlt Hdone Hboundary Hsame.
  unfold CompletedContribution.
  apply (sum_bounded_predicate_extend_point__outer_advance
    (SubjectBlockStart students)
    (fun s => SubjectContribution students s k) start done).
  - lia.
  - eapply subject_block_start_from_inner_start__outer_advance; eauto.
  - intros x Hx.
    eapply no_subject_block_start_inside_inner__outer_advance; eauto.
Qed.
Lemma subject_contribution_past_inner_boundary_zero__outer_advance :
  forall (students : list (Z * Z)) start done k,
    0 <= start ->
    start < done ->
    done <= Zlength students ->
    SubjectBoundary students done ->
    (forall t, start <= t < done ->
       CandidateSubject students t = CandidateSubject students start) ->
    done - start < k ->
    SubjectContribution students start k = 0.
Proof.
  intros students start done k Hstart Hlt Hdone Hboundary Hsame Hk.
  unfold SubjectContribution.
  destruct (prop_dec (SubjectHasK students start k)) as [Hhas | Hnot].
  - exfalso.
    unfold SubjectHasK in Hhas.
    destruct Hhas as [_ [Hkpos [Hwithin Hall]]].
    unfold SubjectBoundary in Hboundary.
    destruct Hboundary as [_ [Hzero | [Hend | Hchange]]].
    + lia.
    + lia.
    + apply Hchange.
      rewrite (Hsame (done - 1) ltac:(lia)).
      rewrite (Hall done ltac:(lia)).
      reflexivity.
  - reflexivity.
Qed.
Lemma competition_outer_from_inner_boundary__outer_advance :
  forall (students : list (Z * Z)) start done prefix totals,
    start < done ->
    SubjectBoundary students done ->
    CompetitionInnerState students start done prefix totals ->
    CompetitionOuterState students done totals.
Proof.
  intros students start done prefix totals Hlt Hdone_boundary Hinner.
  unfold CompetitionInnerState in Hinner.
  destruct Hinner as
    [Hstart [Hstart_done [Hdone [Hstart_boundary
    [Hsame [Hprefix [Hlength [Hzero Htotals]]]]]]]].
  unfold CompetitionOuterState.
  split; [exact Hdone_boundary |].
  split; [exact Hlength |].
  split; [exact Hzero |].
  intros k Hkrange.
  rewrite (Htotals k Hkrange).
  rewrite (completed_contribution_extend_inner__outer_advance
    students start done k Hstart Hlt Hdone Hstart_boundary
    (Hsame Hlt)).
  destruct (prop_dec (1 <= k <= done - start)) as [Hin | Hout].
  - reflexivity.
  - rewrite (subject_contribution_past_inner_boundary_zero__outer_advance
      students start done k Hstart Hlt Hdone Hdone_boundary
      (Hsame Hlt)) by lia.
    lia.
Qed.
Lemma competition_answer_prefix_zero__answer_scan :
  forall totals n,
    0 <= n ->
    Zlength totals = n + 1 ->
    Znth 0 totals 0 = 0 ->
    CompetitionAnswerPrefix totals n 0 0.
Proof.
  intros totals n Hn Hlen Hzero.
  unfold CompetitionAnswerPrefix.
  repeat split; try lia.
  apply max_default_default.
  intros k Hk.
  lia.
Qed.
Lemma competition_answer_prefix_step_take__answer_scan :
  forall totals n k answer,
    CompetitionAnswerPrefix totals n (k - 1) answer ->
    1 <= k <= n ->
    answer < Znth k totals 0 ->
    CompetitionAnswerPrefix totals n k (Znth k totals 0).
Proof.
  intros totals n k answer Hprefix Hk Htake.
  unfold CompetitionAnswerPrefix in *.
  destruct Hprefix as [Hlen [Hdone Hmaximum]].
  repeat split; try lia.
  assert (Hsets : forall b : Z,
             (1 <= b <= k) <-> (1 <= b <= k - 1) \/ k = b).
  {
    intros b.
    split.
    - intros Hb.
      destruct (Z.eq_dec b k) as [Heq | Hneq].
      + right. lia.
      + left. lia.
    - intros [Hb | Heq]; lia.
  }
  pose proof
    (max_default_union_1_right Z.le
       answer (Znth k totals 0) k
       (fun x : Z => Znth x totals 0)
       (fun x : Z => 1 <= x <= k - 1)
       (fun x : Z => 1 <= x <= k)
       0 Hmaximum eq_refl Hsets) as Hextended.
  rewrite (max_r Z.le answer (Znth k totals 0) ltac:(lia)) in Hextended.
  exact Hextended.
Qed.
Lemma competition_answer_prefix_step_keep__answer_scan :
  forall totals n k answer,
    CompetitionAnswerPrefix totals n (k - 1) answer ->
    1 <= k <= n ->
    Znth k totals 0 <= answer ->
    CompetitionAnswerPrefix totals n k answer.
Proof.
  intros totals n k answer Hprefix Hk Hkeep.
  unfold CompetitionAnswerPrefix in *.
  destruct Hprefix as [Hlen [Hdone Hmaximum]].
  repeat split; try lia.
  assert (Hsets : forall b : Z,
             (1 <= b <= k) <-> (1 <= b <= k - 1) \/ k = b).
  {
    intros b.
    split.
    - intros Hb.
      destruct (Z.eq_dec b k) as [Heq | Hneq].
      + right. lia.
      + left. lia.
    - intros [Hb | Heq]; lia.
  }
  pose proof
    (max_default_union_1_right Z.le
       answer (Znth k totals 0) k
       (fun x : Z => Znth x totals 0)
       (fun x : Z => 1 <= x <= k - 1)
       (fun x : Z => 1 <= x <= k)
       0 Hmaximum eq_refl Hsets) as Hextended.
  rewrite (max_l Z.le answer (Znth k totals 0) ltac:(lia)) in Hextended.
  exact Hextended.
Qed.
Lemma sum_permutation__final_result : forall xs ys : list Z,
  Permutation xs ys -> ListLib.sum xs = ListLib.sum ys.
Proof.
  intros xs ys Hperm. induction Hperm; simpl; lia.
Qed.
Lemma fold_sum_map__final_result : forall {A : Type}
    (f : A -> Z) xs,
  fold_right (fun x acc => f x + acc) 0 xs = ListLib.sum (map f xs).
Proof.
  intros A f xs. induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Lemma finite_sum_as_filter__final_result : forall lo hi
    (P : Z -> Prop) (F : Finite (fun i : Z => lo <= i < hi /\ P i))
    (f : Z -> Z) order,
  Permutation (Zrange lo hi) order ->
  @sum Z (fun i : Z => lo <= i < hi /\ P i) F f =
  ListLib.sum (map f
    (filter (fun i => if prop_dec (P i) then true else false) order)).
Proof.
  intros lo hi P F f order Hperm.
  unfold SumLib.Sum.sum.
  rewrite fold_sum_map__final_result.
  apply sum_permutation__final_result.
  apply Permutation_map.
  apply NoDup_Permutation.
  - apply enum_nodup.
  - apply NoDup_filter. eapply Permutation_NoDup; [exact Hperm|].
    apply NoDup_Zrange.
  - intros x. rewrite <- enum_ok, filter_In. split.
    + intros [Hrange HP]. split.
      * eapply Permutation_in; [exact Hperm|]. apply In_Zrange. exact Hrange.
      * destruct (prop_dec (P x)) as [_|Hnot]; [reflexivity|contradiction].
    + intros [Hin Htest]. split.
      * apply In_Zrange. eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
        exact Hin.
      * destruct (prop_dec (P x)) as [HP|Hnot]; [exact HP|discriminate].
Qed.
Lemma sum_ones_length__final_result : forall {A : Type} (xs : list A),
  ListLib.sum (map (fun _ => 1) xs) = Zlength xs.
Proof.
  intros A xs. induction xs as [|x xs IH].
  - reflexivity.
  - rewrite Zlength_cons. change (1 + ListLib.sum (map (fun _ : A => 1) xs) =
      Zlength xs + 1). rewrite IH. apply Z.add_comm.
Qed.
Lemma set_card_as_filter_length__final_result : forall lo hi
    (P : Z -> Prop) (F : Finite (fun i : Z => lo <= i < hi /\ P i)) order,
  Permutation (Zrange lo hi) order ->
  @set_card Z (fun i : Z => lo <= i < hi /\ P i) F =
  Zlength
    (filter (fun i => if prop_dec (P i) then true else false) order).
Proof.
  intros lo hi P F order Hperm. unfold set_card.
  rewrite (finite_sum_as_filter__final_result lo hi P
    F (fun _ => 1) order Hperm).
  apply sum_ones_length__final_result.
Qed.
Lemma firstn_shift_upper__final_result : forall x xs n,
  Forall (fun y : Z => y <= x) xs ->
  (n < length xs)%nat ->
  ListLib.sum (firstn (S n) xs) <=
  x + ListLib.sum (firstn n xs).
Proof.
  intros x xs. induction xs as [|y ys IH]; intros n Hall Hn.
  - simpl in Hn. exfalso. exact (Nat.nlt_0_r n Hn).
  - inversion Hall as [|? ? Hy Hys]; subst. destruct n as [|n].
    + simpl. lia.
    + simpl in Hn. apply Nat.succ_lt_mono in Hn.
      simpl. specialize (IH n Hys Hn).
      replace (x + (y + ListLib.sum (firstn n ys))) with
        (y + (x + ListLib.sum (firstn n ys))) by ring.
      apply Z.add_le_mono_l. exact IH.
Qed.
Lemma decreasing_filter_sum_le_prefix__final_result :
  forall {A : Type} (f : A -> Z) (test : A -> bool) xs,
    ListLib.decreasing (map f xs) ->
    ListLib.sum (map f (filter test xs)) <=
    ListLib.sum (firstn (length (filter test xs)) (map f xs)).
Proof.
  intros A f test xs. induction xs as [|x xs IH]; intros Hdec; simpl.
  - lia.
  - pose proof (proj2 (mono_noninc_iff_decreasing (f x :: map f xs)) Hdec)
      as Hmono.
    apply mono_noninc_cons in Hmono as [Hhead Htail].
    pose proof (proj1 (mono_noninc_iff_decreasing (map f xs)) Htail)
      as Hdec_tail.
    specialize (IH Hdec_tail).
    destruct (test x) eqn:Htest; simpl.
    + lia.
    + destruct (filter test xs) as [|y ys] eqn:Hfilter; simpl in *; [lia|].
      assert (Hlen : (length ys < length (map f xs))%nat).
      { rewrite length_map. change (S (length ys) <= length xs)%nat.
        replace (S (length ys)) with (length (filter test xs)) by
          (rewrite Hfilter; reflexivity).
        pose proof (filter_length test xs). lia. }
      pose proof (firstn_shift_upper__final_result
        (f x) (map f xs) (length ys) Hhead Hlen) as Hshift.
      eapply Z.le_trans; [exact IH | exact Hshift].
Qed.
Lemma Zlength_firstn_to_nat__final_result : forall {A : Type}
    (xs : list A) k,
  0 <= k <= Zlength xs ->
  Zlength (firstn (Z.to_nat k) xs) = k.
Proof.
  intros A xs k Hk. rewrite !Zlength_correct, length_firstn.
  rewrite Nat.min_l.
  - apply Z2Nat.id. lia.
  - rewrite Zlength_correct in Hk.
    rewrite <- (Nat2Z.id (length xs)). apply Z2Nat.inj_le; lia.
Qed.
Lemma Znth_map__final_result : forall {A B : Type} (f : A -> B) xs
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
Lemma mono_inc_Zrange_aux__final_result :
  forall n low, mono_inc (Zrange_aux low n).
Proof.
  induction n as [|n IH]; intros low.
  - apply mono_inc_nil.
  - simpl Zrange_aux.
    apply (proj2 (mono_inc_cons low (Zrange_aux (low + 1) n))).
    split.
    + apply Forall_forall. intros x Hx.
      apply In_Zrange_aux_lb in Hx. lia.
    + apply IH.
Qed.
Lemma mono_inc_Zrange__final_result :
  forall low high, mono_inc (Zrange low high).
Proof.
  intros low high. unfold Zrange. apply mono_inc_Zrange_aux__final_result.
Qed.
Lemma mono_inc_filter__final_result :
  forall (p : Z -> bool) xs,
    mono_inc xs -> mono_inc (filter p xs).
Proof.
  intros p xs. induction xs as [|x xs IH]; intros Hmono.
  - simpl. apply mono_inc_nil.
  - pose proof (proj1 (mono_inc_cons x xs) Hmono) as [Hx Htail].
    simpl. destruct (p x) eqn:Hp.
    + apply (proj2 (mono_inc_cons x (filter p xs))). split.
      * apply Forall_forall. intros y Hy.
        apply filter_In in Hy as [Hy _].
        apply Forall_forall with (x := y) in Hx; assumption.
      * apply IH. exact Htail.
    + apply IH. exact Htail.
Qed.
Lemma subject_order_decreasing__final_result :
  forall students subject,
    CandidatesSorted students ->
    ListLib.decreasing
      (map (CandidateSkill students)
        (filter
          (fun i => if prop_dec (CandidateSubject students i = subject)
                    then true else false)
          (Zrange 0 (Zlength students)))).
Proof.
  intros students subject Hsorted.
  set (order := filter
    (fun i => if prop_dec (CandidateSubject students i = subject)
              then true else false)
    (Zrange 0 (Zlength students))).
  apply (proj1 (mono_noninc_iff_decreasing _)).
  unfold mono_noninc. intros i j Hi Hij Hj.
  assert (Hjorder : j < Zlength order).
  { rewrite !Zlength_correct, length_map in Hj.
    rewrite Zlength_correct. exact Hj. }
  assert (Hiorder : 0 <= i < Zlength order) by lia.
  rewrite (@Znth_map__final_result Z Z (CandidateSkill students)
    order 0 0 i) by exact Hiorder.
  rewrite (@Znth_map__final_result Z Z (CandidateSkill students)
    order 0 0 j) by lia.
  destruct (Z.eq_dec i j) as [->|Hne]; [lia|].
  assert (Hij' : i < j) by lia.
  pose proof (mono_inc_filter__final_result
    (fun q => if prop_dec (CandidateSubject students q = subject)
              then true else false)
    (Zrange 0 (Zlength students))
    (mono_inc_Zrange__final_result 0 (Zlength students))) as Hinc.
  fold order in Hinc.
  unfold mono_inc in Hinc.
  specialize (Hinc i j Hi Hij' Hjorder).
  assert (Hidxi : 0 <= Znth i order 0 < Zlength students).
  { apply In_Zrange.
    pose proof (Znth_In_Zlength order 0 i ltac:(lia)) as Hinorder.
    apply filter_In in Hinorder as [Hin _].
    exact Hin. }
  assert (Hidxj : 0 <= Znth j order 0 < Zlength students).
  { apply In_Zrange.
    pose proof (Znth_In_Zlength order 0 j ltac:(lia)) as Hinorder.
    apply filter_In in Hinorder as [Hin _].
    exact Hin. }
  specialize (Hsorted (Znth i order 0) (Znth j order 0)
    ltac:(lia)) as [Hsubjectlt|[Hsubjecteq Hskill]].
  - exfalso.
    assert (Hsi : CandidateSubject students (Znth i order 0) = subject).
    { pose proof (Znth_In_Zlength order 0 i ltac:(lia)) as Hinorder.
      apply filter_In in Hinorder as [_ Htest].
      destruct (prop_dec
        (CandidateSubject students (Znth i order 0) = subject));
        [assumption|discriminate]. }
    assert (Hsj : CandidateSubject students (Znth j order 0) = subject).
    { pose proof (Znth_In_Zlength order 0 j ltac:(lia)) as Hinorder.
      apply filter_In in Hinorder as [_ Htest].
      destruct (prop_dec
        (CandidateSubject students (Znth j order 0) = subject));
        [assumption|discriminate]. }
    lia.
  - lia.
Qed.
Lemma Zlength_Zrange_aux__final_result : forall low n,
  Zlength (Zrange_aux low n) = Z.of_nat n.
Proof.
  intros low n. revert low. induction n as [|n IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__final_result : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__final_result. lia.
Qed.
Lemma Zrange_split_three__final_result : forall n lo hi,
  0 <= lo /\ lo <= hi /\ hi <= n ->
  Zrange 0 n = Zrange 0 lo ++ Zrange lo hi ++ Zrange hi n.
Proof.
  intros n lo hi [Hlo [Hlohi Hhin]]. unfold Zrange.
  replace (Z.to_nat (n - 0)) with
    (Z.to_nat (lo - 0) +
      (Z.to_nat (hi - lo) + Z.to_nat (n - hi)))%nat by lia.
  rewrite Zrange_aux_app.
  rewrite Zrange_aux_app.
  replace (0 + Z.of_nat (Z.to_nat (lo - 0))) with lo by lia.
  replace (lo + Z.of_nat (Z.to_nat (hi - lo))) with hi by lia.
  reflexivity.
Qed.
Lemma filter_all_false__final_result : forall {A : Type}
    (test : A -> bool) xs,
  (forall x, In x xs -> test x = false) ->
  filter test xs = nil.
Proof.
  intros A test xs. induction xs as [|x xs IH]; intros Hall; simpl.
  - reflexivity.
  - rewrite (Hall x (or_introl eq_refl)). apply IH.
    intros y Hy. apply Hall. right. exact Hy.
Qed.
Lemma filter_all_true__final_result : forall {A : Type}
    (test : A -> bool) xs,
  (forall x, In x xs -> test x = true) ->
  filter test xs = xs.
Proof.
  intros A test xs. induction xs as [|x xs IH]; intros Hall; simpl.
  - reflexivity.
  - rewrite (Hall x (or_introl eq_refl)). f_equal. apply IH.
    intros y Hy. apply Hall. right. exact Hy.
Qed.
Lemma candidate_subject_before_start__final_result :
  forall students start i,
    CandidatesSorted students ->
    SubjectBlockStart students start ->
    0 <= i < start ->
    CandidateSubject students i < CandidateSubject students start.
Proof.
  intros students start i Hsorted [Hstart Hboundary] Hi.
  destruct Hboundary as [Hzero|Hboundary]; [lia|].
  pose proof (Hsorted i start ltac:(lia)) as Hends.
  destruct Hends as [Hlt|[Heq _]]; [exact Hlt|].
  assert (Hprev : CandidateSubject students (start - 1) <
      CandidateSubject students start).
  { pose proof (Hsorted (start - 1) start ltac:(lia)) as Hlast.
    destruct Hlast as [Hlt|[Heqprev _]]; [exact Hlt|contradiction]. }
  destruct (Z.eq_dec i (start - 1)) as [->|Hne].
  - rewrite Heq in Hprev. lia.
  - pose proof (Hsorted i (start - 1) ltac:(lia)) as Hmiddle.
    destruct Hmiddle as [Hltprev|[Heqprev _]]; rewrite Heq in *; lia.
Qed.
Lemma subject_order_prefix__final_result :
  forall students start k,
    CandidatesSorted students ->
    SubjectBlockStart students start ->
    1 <= k ->
    start + k <= Zlength students ->
    (forall t, start <= t < start + k ->
       CandidateSubject students t = CandidateSubject students start) ->
    firstn (Z.to_nat k)
      (filter
        (fun i => if prop_dec
          (CandidateSubject students i = CandidateSubject students start)
          then true else false)
        (Zrange 0 (Zlength students))) =
    Zrange start (start + k).
Proof.
  intros students start k Hsorted Hstart Hk Hbound Hsame.
  set (test := fun i => if prop_dec
    (CandidateSubject students i = CandidateSubject students start)
    then true else false).
  rewrite (Zrange_split_three__final_result
    (Zlength students) start (start + k)) by
    (destruct Hstart as [[? ?] _]; lia).
  rewrite !filter_app.
  assert (Hpre : filter test (Zrange 0 start) = nil).
  { apply filter_all_false__final_result. intros i Hi.
    apply In_Zrange in Hi.
    unfold test. destruct (prop_dec
      (CandidateSubject students i = CandidateSubject students start))
      as [Heq|Hneq]; [|reflexivity].
    pose proof (candidate_subject_before_start__final_result
      students start i Hsorted Hstart Hi). lia. }
  assert (Hmid : filter test (Zrange start (start + k)) =
      Zrange start (start + k)).
  { apply filter_all_true__final_result. intros i Hi.
    apply In_Zrange in Hi. unfold test.
    destruct (prop_dec
      (CandidateSubject students i = CandidateSubject students start))
      as [Heq|Hneq]; [reflexivity|].
    exfalso. apply Hneq. apply Hsame. exact Hi. }
  rewrite Hpre, Hmid. simpl.
  rewrite firstn_app.
  assert (Hlen : length (Zrange start (start + k)) = Z.to_nat k).
  { apply Nat2Z.inj.
    rewrite <- Zlength_correct, Zlength_Zrange__final_result by lia.
    rewrite Z2Nat.id by lia. lia. }
  rewrite Hlen.
  replace (Z.to_nat k - Z.to_nat k)%nat with O by lia.
  simpl. rewrite app_nil_r. rewrite <- Hlen. apply firstn_all.
Qed.
Lemma skill_sum_as_index_list__final_result :
  forall students lo hi,
    0 <= lo <= hi ->
    hi <= Zlength students ->
    SkillSum students lo hi =
    ListLib.sum
      (map (CandidateSkill students) (Zrange lo hi)).
Proof.
  intros students lo hi Hlo Hhi.
  unfold SkillSum, CandidateSkill.
  change (ListLib.sum (map snd (sublist lo hi students)) =
    ListLib.sum (map (fun i => snd (Znth i students (0, 0)))
      (Zrange lo hi))).
  rewrite (list_sum_map_as_Z_range_sum (0, 0) snd
    (sublist lo hi students)).
  rewrite Zlength_sublist by lia.
  rewrite <- fold_sum_map__final_result.
  rewrite <- sum_range_unfold.
  transitivity
    (sum (fun i : Z => 0 <= i < hi - lo)
      (fun i => snd (Znth (i + lo) students (0, 0)))).
  - apply sum_Z_range_ext. intros i Hi.
    rewrite Znth_sublist by lia. reflexivity.
  - rewrite <- (sum_Z_range_shift 0 (hi - lo) lo
      (fun i => snd (Znth i students (0, 0)))).
    change (0 + lo) with lo.
    replace (hi - lo + lo) with hi by lia.
    reflexivity.
Qed.
Lemma sorted_subject_block_topk_optimal__final_result :
  forall students start k chosen,
    CandidatesSorted students ->
    SubjectHasK students start k ->
    #(fun i : Z =>
       0 <= i < Zlength students /\ chosen i /\
       CandidateSubject students i = CandidateSubject students start) = k ->
    sum
      (fun i : Z =>
         0 <= i < Zlength students /\ chosen i /\
         CandidateSubject students i = CandidateSubject students start)
      (CandidateSkill students) <=
    SubjectContribution students start k.
Proof.
  intros students start k chosen Hsorted Hhas Hcard.
  destruct Hhas as [Hstart [Hk [Hbound Hsame]]].
  set (order := filter
    (fun i => if prop_dec
      (CandidateSubject students i = CandidateSubject students start)
      then true else false)
    (Zrange 0 (Zlength students))).
  set (selected := filter
    (fun i => if prop_dec (chosen i) then true else false) order).
  set (paired :=
      filter
        (fun i => if prop_dec
          (chosen i /\ CandidateSubject students i =
            CandidateSubject students start)
          then true else false)
        (Zrange 0 (Zlength students))).
  assert (Hselected_perm : Permutation paired selected).
  { subst selected paired. apply NoDup_Permutation.
    - apply NoDup_filter. apply NoDup_Zrange.
    - apply NoDup_filter. subst order.
      apply NoDup_filter. apply NoDup_Zrange.
    - intros i. rewrite !filter_In. split.
      + intros [Hinrange Hpairtest].
        destruct (prop_dec
          (chosen i /\ CandidateSubject students i =
            CandidateSubject students start)) as [[Hchosen Hsubject]|Hnot];
          [|discriminate].
        split.
        * unfold order. apply filter_In. split; [exact Hinrange|].
          destruct (prop_dec (CandidateSubject students i =
            CandidateSubject students start)); [reflexivity|contradiction].
        *
        destruct (prop_dec (chosen i)); [reflexivity|contradiction].
      + intros [Hinorder Hchosen_test].
        assert (Hchosen : chosen i).
        { destruct (prop_dec (chosen i)); [assumption|discriminate]. }
        assert (Hinrange : In i (Zrange 0 (Zlength students))).
        { unfold order in Hinorder. apply filter_In in Hinorder as [Hin _].
          exact Hin. }
        assert (Hsubject : CandidateSubject students i =
            CandidateSubject students start).
        { unfold order in Hinorder. apply filter_In in Hinorder as [_ Htest].
          destruct (prop_dec (CandidateSubject students i =
            CandidateSubject students start)); [assumption|discriminate]. }
        split; [exact Hinrange|].
        destruct (prop_dec
          (chosen i /\ CandidateSubject students i =
            CandidateSubject students start)) as [Hpair|Hnotpair].
        * reflexivity.
        * exfalso. apply Hnotpair. split; assumption. }
  assert (Hsum :
      sum
        (fun i : Z =>
           0 <= i < Zlength students /\ chosen i /\
           CandidateSubject students i = CandidateSubject students start)
        (CandidateSkill students) =
      ListLib.sum (map (CandidateSkill students) selected)).
  { rewrite (finite_sum_as_filter__final_result
      0 (Zlength students)
      (fun i => chosen i /\
        CandidateSubject students i = CandidateSubject students start)
      _ (CandidateSkill students) (Zrange 0 (Zlength students))).
    - apply sum_permutation__final_result. apply Permutation_map.
      exact Hselected_perm.
    - apply Permutation_refl. }
  assert (Hselected_len : Zlength selected = k).
  { rewrite <- Hcard.
    rewrite (set_card_as_filter_length__final_result
      0 (Zlength students)
      (fun i => chosen i /\
        CandidateSubject students i = CandidateSubject students start)
      _ (Zrange 0 (Zlength students))).
    - pose proof (Permutation_length Hselected_perm) as Hplen.
      fold paired. rewrite !Zlength_correct. f_equal.
      symmetry. exact Hplen.
    - apply Permutation_refl. }
  assert (Htop := decreasing_filter_sum_le_prefix__final_result
    (CandidateSkill students)
    (fun i => if prop_dec (chosen i) then true else false)
    order).
  specialize (Htop (ltac:(subst order;
    apply subject_order_decreasing__final_result; exact Hsorted))).
  fold selected in Htop.
  assert (Hlen_nat : length selected = Z.to_nat k).
  { apply Nat2Z.inj.
    rewrite <- Zlength_correct, Hselected_len, Z2Nat.id by lia. lia. }
  rewrite Hlen_nat in Htop.
  assert (Hprefix : firstn (Z.to_nat k) order =
      Zrange start (start + k)).
  { subst order. apply subject_order_prefix__final_result; assumption. }
  rewrite firstn_map, Hprefix in Htop.
  rewrite <- (skill_sum_as_index_list__final_result
    students start (start + k)) in Htop by
    (destruct Hstart as [[? ?] _]; lia).
  unfold SubjectContribution.
  destruct (prop_dec (SubjectHasK students start k)) as [Hyes|Hno].
  - rewrite Hsum. eapply Z.le_trans; [exact Htop|apply Z.le_max_r].
  - exfalso. apply Hno. unfold SubjectHasK.
    split; [exact Hstart|]. split; [exact Hk|].
    split; [exact Hbound|exact Hsame].
Qed.
Lemma subject_block_start_exists__final_result :
  forall students i,
    0 <= i < Zlength students ->
    exists start,
      SubjectBlockStart students start /\
      start <= i /\
      CandidateSubject students i = CandidateSubject students start.
Proof.
  intros students i Hi.
  remember (Z.to_nat i) as ni eqn:Hni.
  assert (Hi_nat : i = Z.of_nat ni) by (subst ni; rewrite Z2Nat.id by lia; reflexivity).
  revert i Hi Hni Hi_nat.
  induction ni as [|ni IH]; intros i Hi Hni Hi_nat.
  - assert (i = 0) by lia. subst i. exists 0. split.
    + unfold SubjectBlockStart. split; [lia|left; reflexivity].
    + split; [lia|reflexivity].
  - destruct (prop_dec
      (CandidateSubject students (i - 1) = CandidateSubject students i))
      as [Hsame|Hdiff].
    + assert (Hprev : 0 <= i - 1 < Zlength students) by lia.
      assert (Hprev_nat : Z.to_nat (i - 1) = ni) by lia.
      specialize (IH (i - 1) Hprev (eq_sym Hprev_nat) ltac:(lia))
        as [start [Hstart [Hle Heq]]].
      exists start. split; [exact Hstart|]. split; [lia|].
      rewrite <- Hsame. exact Heq.
    + exists i. split.
      * unfold SubjectBlockStart. split; [exact Hi|].
        right. exact Hdiff.
      * split; [lia|reflexivity].
Qed.
Lemma subject_block_start_unique__final_result :
  forall students a b,
    CandidatesSorted students ->
    SubjectBlockStart students a ->
    SubjectBlockStart students b ->
    CandidateSubject students a = CandidateSubject students b ->
    a = b.
Proof.
  intros students a b Hsorted Ha Hb Heq.
  destruct (Z.lt_trichotomy a b) as [Hab|[->|Hba]]; [|reflexivity|].
  - pose proof (candidate_subject_before_start__final_result
      students b a Hsorted Hb ltac:(destruct Ha as [[? ?] _]; lia)).
    lia.
  - pose proof (candidate_subject_before_start__final_result
      students a b Hsorted Ha ltac:(destruct Hb as [[? ?] _]; lia)).
    lia.
Qed.
Lemma filter_complement_perm__final_result : forall {A : Type}
    (test : A -> bool) xs,
  Permutation xs
    (filter test xs ++ filter (fun x => negb (test x)) xs).
Proof.
  intros A test xs. induction xs as [|x xs IH]; simpl.
  - constructor.
  - destruct (test x) eqn:Hx; simpl.
    + apply perm_skip. exact IH.
    + eapply Permutation_trans.
      * apply perm_skip. exact IH.
      * apply Permutation_middle.
Qed.
Lemma filter_after_complement__final_result : forall {A : Type}
    (p q : A -> bool) xs,
  (forall x, In x xs -> p x = true -> q x = false) ->
  filter p (filter (fun x => negb (q x)) xs) = filter p xs.
Proof.
  intros A p q xs. induction xs as [|x xs IH]; intros Hdisjoint; simpl.
  - reflexivity.
  - assert (Htail : forall z, In z xs -> p z = true -> q z = false).
    { intros z Hz. apply Hdisjoint. right. exact Hz. }
    destruct (q x) eqn:Hqx; simpl.
    + destruct (p x) eqn:Hpx; [|apply IH; exact Htail].
      specialize (Hdisjoint x (or_introl eq_refl) Hpx).
      rewrite Hqx in Hdisjoint. discriminate.
    + destruct (p x) eqn:Hpx; simpl.
      * f_equal. apply IH. exact Htail.
      * apply IH. exact Htail.
Qed.
Lemma list_sum_map_partition__final_result :
  forall {A B : Type} (xs : list A) (ys : list B)
    (belongs : A -> B -> bool) (f : A -> Z),
    NoDup ys ->
    (forall x, In x xs ->
      exists y,
        In y ys /\ belongs x y = true /\
        forall z, In z ys -> belongs x z = true -> z = y) ->
    ListLib.sum (map f xs) =
    ListLib.sum
      (map
        (fun y => ListLib.sum
          (map f (filter (fun x => belongs x y) xs)))
        ys).
Proof.
  intros A B xs ys. revert xs.
  induction ys as [|y ys IH]; intros xs belongs f Hnodup Howner.
  - assert (xs = nil).
    { destruct xs as [|x xs]; [reflexivity|].
      specialize (Howner x (or_introl eq_refl)) as [z [Hz _]].
      contradiction. }
    subst xs. reflexivity.
  - inversion Hnodup as [|? ? Hynotin Hnodupys]; subst.
    set (hit := filter (fun x => belongs x y) xs).
    set (rest := filter (fun x => negb (belongs x y)) xs).
    pose proof (filter_complement_perm__final_result
      (fun x => belongs x y) xs) as Hsplit.
    fold hit rest in Hsplit.
    rewrite (sum_permutation__final_result _ _ (Permutation_map f Hsplit)).
    rewrite map_app, ListLib.sum_app. simpl.
    assert (Howner_rest : forall x, In x rest ->
      exists z, In z ys /\ belongs x z = true /\
        forall w, In w ys -> belongs x w = true -> w = z).
    { intros x Hxrest. unfold rest in Hxrest.
      apply filter_In in Hxrest as [Hx Hnoty].
      specialize (Howner x Hx) as [z [[Hz|Hz] [Hbel Huniq]]].
      - subst z. rewrite Hbel in Hnoty. discriminate.
      - exists z. split; [exact Hz|]. split; [exact Hbel|].
        intros w Hw Hbw. apply Huniq; [right; exact Hw|exact Hbw]. }
    fold hit rest.
    f_equal.
    rewrite (IH rest belongs f Hnodupys Howner_rest).
    f_equal. apply map_ext_in. intros z Hz.
    assert (Hfilter :
      filter (fun x => belongs x z) rest =
      filter (fun x => belongs x z) xs).
    { unfold rest. apply filter_after_complement__final_result.
      intros x Hx Hxz.
      destruct (belongs x y) eqn:Hxy; [|reflexivity].
      exfalso.
      specialize (Howner x Hx) as [owner [[Howner_y|Howner_ys]
        [Hbowner Huniq]]].
      - subst owner. pose proof (Huniq z (or_intror Hz) Hxz) as Heq.
        subst z. contradiction.
      - pose proof (Huniq y (or_introl eq_refl) Hxy) as Heq.
        subst owner. contradiction. }
    rewrite Hfilter. reflexivity.
Qed.
Lemma subject_has_k_of_positive_card__final_result :
  forall students start k chosen,
    CandidatesSorted students ->
    SubjectBlockStart students start ->
    1 <= k ->
    #(fun i : Z =>
       0 <= i < Zlength students /\ chosen i /\
       CandidateSubject students i = CandidateSubject students start) = k ->
    SubjectHasK students start k.
Proof.
  intros students start k chosen Hsorted Hstart Hk Hcard.
  set (order := filter
    (fun i => if prop_dec
      (CandidateSubject students i = CandidateSubject students start)
      then true else false)
    (Zrange 0 (Zlength students))).
  set (picked := filter
    (fun i => if prop_dec
      (chosen i /\ CandidateSubject students i =
        CandidateSubject students start)
      then true else false)
    (Zrange 0 (Zlength students))).
  assert (Hpicked_len : Zlength picked = k).
  { rewrite <- Hcard. subst picked.
    symmetry.
    apply set_card_as_filter_length__final_result.
    apply Permutation_refl. }
  assert (Hpicked_incl : incl picked order).
  { intros i Hi. unfold picked in Hi. apply filter_In in Hi as [Hrange Htest].
    destruct (prop_dec
      (chosen i /\ CandidateSubject students i =
        CandidateSubject students start)) as [[_ Hsubject]|Hnot];
      [|discriminate].
    unfold order. apply filter_In. split; [exact Hrange|].
    destruct (prop_dec (CandidateSubject students i =
      CandidateSubject students start)); [reflexivity|contradiction]. }
  assert (Hk_order : k <= Zlength order).
  { assert (Hlen : (length picked <= length order)%nat).
    { apply NoDup_incl_length; [|exact Hpicked_incl].
      subst picked. apply NoDup_filter. apply NoDup_Zrange. }
    rewrite !Zlength_correct in Hpicked_len |- *.
    rewrite <- Hpicked_len. apply Nat2Z.inj_le. exact Hlen. }
  assert (Horder_lower : incl order (Zrange start (Zlength students))).
  { intros i Hi. unfold order in Hi. apply filter_In in Hi as [Hrange Htest].
    apply In_Zrange in Hrange.
    assert (Hsubject : CandidateSubject students i =
        CandidateSubject students start).
    { destruct (prop_dec (CandidateSubject students i =
        CandidateSubject students start)); [assumption|discriminate]. }
    apply In_Zrange. split; [|lia].
    destruct (Z_lt_ge_dec i start) as [Hlt|Hge]; [|lia].
    pose proof (candidate_subject_before_start__final_result
      students start i Hsorted Hstart ltac:(lia)). lia. }
  assert (Hbound : start + k <= Zlength students).
  { assert (Hlen : (length order <=
        length (Zrange start (Zlength students)))%nat).
    { apply NoDup_incl_length; [|exact Horder_lower].
      subst order. apply NoDup_filter. apply NoDup_Zrange. }
    assert (HZlen : Zlength order <=
        Zlength (Zrange start (Zlength students))).
    { rewrite (Zlength_correct order),
        (Zlength_correct (Zrange start (Zlength students))).
      apply Nat2Z.inj_le. exact Hlen. }
    rewrite Zlength_Zrange__final_result in HZlen by
      (destruct Hstart as [[? ?] _]; lia).
    lia. }
  unfold SubjectHasK. split; [exact Hstart|].
  split; [exact Hk|]. split; [exact Hbound|].
  intros t Ht.
  destruct (Z.eq_dec t start) as [->|Hne]; [reflexivity|].
  pose proof (Hsorted start t ltac:(destruct Hstart as [[? ?] _]; lia))
    as Hstartt.
  destruct Hstartt as [Hsubjectlt|[Hsubjecteq _]];
    [|symmetry; exact Hsubjecteq].
  exfalso.
  assert (Horder_before : incl order (Zrange start t)).
  { intros j Hj. apply In_Zrange. split.
    - pose proof (Horder_lower j Hj) as Hjlower.
      apply In_Zrange in Hjlower. lia.
    - unfold order in Hj. apply filter_In in Hj as [Hjrange Hjtest].
      apply In_Zrange in Hjrange.
      assert (Hjsubject : CandidateSubject students j =
          CandidateSubject students start).
      { destruct (prop_dec (CandidateSubject students j =
          CandidateSubject students start)); [assumption|discriminate]. }
      destruct (Z_lt_ge_dec j t) as [Hjt|Hjt]; [exact Hjt|].
      destruct (Z.eq_dec j t) as [->|Hjne]; [lia|].
      pose proof (Hsorted t j ltac:(
        destruct Hstart as [[Hs0 Hsn] Hsb]; repeat split; lia)) as
        [Htj|[Htjieq _]]; lia. }
  assert (Hlen : (length order <= length (Zrange start t))%nat).
  { apply NoDup_incl_length; [|exact Horder_before].
    subst order. apply NoDup_filter. apply NoDup_Zrange. }
  assert (HZlen : Zlength order <= Zlength (Zrange start t)).
  { rewrite (Zlength_correct order),
      (Zlength_correct (Zrange start t)).
    apply Nat2Z.inj_le. exact Hlen. }
  rewrite Zlength_Zrange__final_result in HZlen by
    (destruct Hstart as [[? ?] _]; lia).
  lia.
Qed.
Lemma list_sum_map_le__final_result : forall {A : Type}
    (f g : A -> Z) xs,
  (forall x, In x xs -> f x <= g x) ->
  ListLib.sum (map f xs) <= ListLib.sum (map g xs).
Proof.
  intros A f g xs. induction xs as [|x xs IH]; intros Hle; simpl.
  - lia.
  - apply Z.add_le_mono.
    + apply Hle. left. reflexivity.
    + apply IH. intros y Hy. apply Hle. right. exact Hy.
Qed.
Lemma delegation_subject_sum_as_filter__final_result :
  forall students chosen subject,
    sum
      (fun i : Z =>
         0 <= i < Zlength students /\ chosen i /\
         CandidateSubject students i = subject)
      (CandidateSkill students) =
    ListLib.sum
      (map (CandidateSkill students)
        (filter
          (fun i => if prop_dec (CandidateSubject students i = subject)
                    then true else false)
          (filter (fun i => if prop_dec (chosen i) then true else false)
            (Zrange 0 (Zlength students))))).
Proof.
  intros students chosen subject.
  rewrite (finite_sum_as_filter__final_result
    0 (Zlength students)
    (fun i => chosen i /\ CandidateSubject students i = subject)
    _ (CandidateSkill students) (Zrange 0 (Zlength students))) by
    apply Permutation_refl.
  apply sum_permutation__final_result. apply Permutation_map.
  apply NoDup_Permutation.
  - apply NoDup_filter. apply NoDup_Zrange.
  - apply NoDup_filter. apply NoDup_filter. apply NoDup_Zrange.
  - intros i. repeat rewrite filter_In. split.
    + intros [Hrange Hpairtest].
      destruct (prop_dec (chosen i /\ CandidateSubject students i = subject))
        as [[Hchosen Hsubject]|Hnot]; [|discriminate].
      split; [split; [exact Hrange|]|].
      * destruct (prop_dec (chosen i)); [reflexivity|contradiction].
      * destruct (prop_dec (CandidateSubject students i = subject));
          [reflexivity|contradiction].
    + intros [[Hrange Hchosen_test] Hsubject_test]. split; [exact Hrange|].
      assert (Hchosen : chosen i).
      { destruct (prop_dec (chosen i)); [assumption|discriminate]. }
      assert (Hsubject : CandidateSubject students i = subject).
      { destruct (prop_dec (CandidateSubject students i = subject));
          [assumption|discriminate]. }
      destruct (prop_dec (chosen i /\ CandidateSubject students i = subject));
        [reflexivity|exfalso; apply n; split; assumption].
Qed.
Lemma completed_contribution_upper__final_result :
  forall students chosen,
    CandidatesSorted students ->
    1 <= Zlength students ->
    ValidDelegation students chosen ->
    exists k,
      1 <= k <= Zlength students /\
      DelegationSkill students chosen <=
        CompletedContribution students (Zlength students) k.
Proof.
  intros students chosen Hsorted Hnonempty
    [Hchosen_bounds [size [Hsize Huniform]]].
  set (selected := filter
    (fun i => if prop_dec (chosen i) then true else false)
    (Zrange 0 (Zlength students))).
  assert (Hskill : DelegationSkill students chosen =
      ListLib.sum (map (CandidateSkill students) selected)).
  { unfold DelegationSkill, CandidateSkill.
    apply finite_sum_as_filter__final_result.
    apply Permutation_refl. }
  destruct selected as [|first selected_tail] eqn:Hselected.
  - exists 1. split; [lia|].
    rewrite Hskill. simpl.
    unfold CompletedContribution.
    apply sum_nonneg. intros start Hstart.
    unfold SubjectContribution.
    destruct (prop_dec (SubjectHasK students start 1)); [apply Z.le_max_l|lia].
  - assert (Hfirst_selected : In first selected).
    { rewrite Hselected. left. reflexivity. }
    unfold selected in Hfirst_selected.
    apply filter_In in Hfirst_selected as [Hfirst_range Hfirst_test].
    apply In_Zrange in Hfirst_range.
    assert (Hfirst_chosen : chosen first).
    { destruct (prop_dec (chosen first)); [assumption|discriminate]. }
    specialize (Huniform (CandidateSubject students first)) as Hfirst_card.
    assert (Hexfirst : exists i,
      chosen i /\
      fst (Znth i students (0, 0)) = CandidateSubject students first).
    { exists first. split; [exact Hfirst_chosen|reflexivity]. }
    specialize (Hfirst_card Hexfirst).
    destruct (subject_block_start_exists__final_result
      students first Hfirst_range) as
      [first_start [Hfirst_start [_ Hfirst_subject]]].
    assert (Hfirst_card_start :
      #(fun i : Z => 0 <= i < Zlength students /\ chosen i /\
        CandidateSubject students i = CandidateSubject students first_start) =
      size).
    { rewrite <- Hfirst_subject. exact Hfirst_card. }
    pose proof (subject_has_k_of_positive_card__final_result
      students first_start size chosen Hsorted Hfirst_start ltac:(lia)
      Hfirst_card_start) as Hfirst_has.
    destruct Hfirst_has as [_ [_ [Hfirst_bound _]]].
    exists size. split.
    + destruct Hfirst_start as [[Hstart0 _] _]. lia.
    + set (starts := filter
        (fun start => if prop_dec (SubjectBlockStart students start)
                      then true else false)
        (Zrange 0 (Zlength students))).
      set (belongs := fun i start => if prop_dec
        (CandidateSubject students i = CandidateSubject students start)
        then true else false).
      assert (Hcompleted :
        CompletedContribution students (Zlength students) size =
        ListLib.sum (map
          (fun start => SubjectContribution students start size) starts)).
      { unfold CompletedContribution.
        apply finite_sum_as_filter__final_result.
        apply Permutation_refl. }
      assert (Hpartition :
        ListLib.sum (map (CandidateSkill students) selected) =
        ListLib.sum (map
          (fun start => ListLib.sum
            (map (CandidateSkill students)
              (filter (fun i => belongs i start) selected)))
          starts)).
      { apply list_sum_map_partition__final_result.
        - subst starts. apply NoDup_filter. apply NoDup_Zrange.
        - intros i Hi.
          unfold selected in Hi. apply filter_In in Hi as [Hirange Hitest].
          apply In_Zrange in Hirange.
          destruct (subject_block_start_exists__final_result
            students i Hirange) as [start [Hstart [_ Hsubject]]].
          exists start. split.
          + subst starts. apply filter_In. split.
            * apply In_Zrange. destruct Hstart as [[? ?] _]. lia.
            * destruct (prop_dec (SubjectBlockStart students start));
                [reflexivity|contradiction].
          + split.
            * unfold belongs. destruct (prop_dec
                (CandidateSubject students i = CandidateSubject students start));
                [reflexivity|contradiction].
            * intros z Hz Hbel.
              subst starts. apply filter_In in Hz as [Hzrange Hztest].
              assert (Hzstart : SubjectBlockStart students z).
              { destruct (prop_dec (SubjectBlockStart students z));
                  [assumption|discriminate]. }
              assert (Hiz : CandidateSubject students i =
                  CandidateSubject students z).
              { unfold belongs in Hbel.
                destruct (prop_dec (CandidateSubject students i =
                  CandidateSubject students z)); [assumption|discriminate]. }
              apply subject_block_start_unique__final_result with
                (students := students); try assumption. lia. }
      assert (Hblocks :
        ListLib.sum (map
          (fun start => ListLib.sum
            (map (CandidateSkill students)
              (filter (fun i => belongs i start) selected)))
          starts) <=
        ListLib.sum (map
          (fun start => SubjectContribution students start size) starts)).
      { apply list_sum_map_le__final_result. intros start Hstart_in.
        assert (Hstart : SubjectBlockStart students start).
        { subst starts. apply filter_In in Hstart_in as [_ Htest].
          destruct (prop_dec (SubjectBlockStart students start));
            [assumption|discriminate]. }
        set (block_selected := filter (fun i => belongs i start) selected).
        destruct block_selected as [|x xs] eqn:Hblock.
        - simpl. unfold SubjectContribution.
          destruct (prop_dec (SubjectHasK students start size));
            [apply Z.le_max_l|lia].
        - assert (Hxblock : In x block_selected).
          { rewrite Hblock. left. reflexivity. }
          unfold block_selected in Hxblock.
          apply filter_In in Hxblock as [Hxselected Hxbelongs].
          unfold selected in Hxselected.
          apply filter_In in Hxselected as [Hxrange Hxchosen_test].
          apply In_Zrange in Hxrange.
          assert (Hxchosen : chosen x).
          { destruct (prop_dec (chosen x)); [assumption|discriminate]. }
          assert (Hxsubject : CandidateSubject students x =
              CandidateSubject students start).
          { unfold belongs in Hxbelongs.
            destruct (prop_dec (CandidateSubject students x =
              CandidateSubject students start)); [assumption|discriminate]. }
          specialize (Huniform (CandidateSubject students start)) as Hcard.
          assert (Hex : exists i,
            chosen i /\ fst (Znth i students (0, 0)) =
              CandidateSubject students start).
          { exists x. split; assumption. }
          specialize (Hcard Hex).
          pose proof (subject_has_k_of_positive_card__final_result
            students start size chosen Hsorted Hstart ltac:(lia) Hcard) as Hhas.
          pose proof (sorted_subject_block_topk_optimal__final_result
            students start size chosen Hsorted Hhas Hcard) as Hopt.
          rewrite (delegation_subject_sum_as_filter__final_result
            students chosen (CandidateSubject students start)) in Hopt.
          fold selected in Hopt. fold belongs in Hopt.
          assert (Hfilter_block :
            filter
              (fun i =>
                if prop_dec
                  (CandidateSubject students i =
                   CandidateSubject students start)
                then true else false) selected = x :: xs).
          { change (filter (fun i => belongs i start) selected = x :: xs).
            unfold block_selected in Hblock. exact Hblock. }
          rewrite Hfilter_block in Hopt.
          exact Hopt. }
      rewrite Hskill. rewrite <- Hselected.
      rewrite Hpartition, Hcompleted. exact Hblocks.
Qed.
Lemma completed_contribution_attainable__final_result :
  forall students k,
    CandidatesSorted students ->
    1 <= k <= Zlength students ->
    exists chosen,
      ValidDelegation students chosen /\
      DelegationSkill students chosen =
        CompletedContribution students (Zlength students) k.
Proof.
  intros students k Hsorted Hk.
  set (chosen := fun i : Z => exists start,
    SubjectBlockStart students start /\
    SubjectHasK students start k /\
    0 < SkillSum students start (start + k) /\
    start <= i < start + k).
  exists chosen. split.
  - split.
    + intros i [start [Hstart [Hhas [Hpositive Hi]]]].
      destruct Hstart as [[Hstart0 Hstartn] Hboundary].
      destruct Hhas as [_ [_ [Hend _]]]. lia.
    + exists k. split; [lia|]. intros subject Hex.
      destruct Hex as [i [[start [Hstart [Hhas [Hpositive Hi]]]] Hsubject]].
      assert (Hsubject_start : CandidateSubject students start = subject).
      { rewrite <- Hsubject. destruct Hhas as [_ [_ [_ Hall]]].
        symmetry. apply Hall. exact Hi. }
      rewrite (set_card_as_filter_length__final_result
        0 (Zlength students)
        (fun x => chosen x /\ CandidateSubject students x = subject)
        _ (Zrange 0 (Zlength students)) (Permutation_refl _)).
      assert (Hfilter : Permutation
        (filter
          (fun x =>
            if prop_dec
              (chosen x /\ CandidateSubject students x = subject)
            then true else false)
          (Zrange 0 (Zlength students)))
        (Zrange start (start + k))).
      { apply NoDup_Permutation; try apply NoDup_filter;
          try apply NoDup_Zrange.
        intros x. rewrite filter_In, <- !In_Zrange. split.
        - intros [[Hx0 Hxn] Htest].
          destruct (prop_dec
            (chosen x /\ CandidateSubject students x = subject))
            as [[Hxchosen Hxsubject]|Hnot]; [|discriminate].
          destruct Hxchosen as
            [other [Hother_start [Hother_has [Hother_positive Hother_range]]]].
          assert (Hother_subject :
            CandidateSubject students other = subject).
          { rewrite <- Hxsubject. destruct Hother_has as [_ [_ [_ Hall]]].
            symmetry. apply Hall. exact Hother_range. }
          assert (other = start).
          { apply subject_block_start_unique__final_result with
              (students := students); try assumption.
            rewrite Hother_subject, Hsubject_start. reflexivity. }
          subst other. exact Hother_range.
        - intros Hxrange. split.
          + pose proof Hstart as Hstart_bounds.
            destruct Hstart_bounds as [[Hstart0 Hstartn] Hboundary].
            destruct Hhas as [_ [_ [Hend _]]]. lia.
          + destruct (prop_dec
              (chosen x /\ CandidateSubject students x = subject))
              as [Hyes|Hno]; [reflexivity|].
            exfalso. apply Hno. split.
            * unfold chosen. exists start. split; [exact Hstart|].
              split; [exact Hhas|]. split; assumption.
            * rewrite <- Hsubject_start.
              destruct Hhas as [_ [_ [_ Hall]]].
              apply Hall. exact Hxrange. }
      rewrite Zlength_correct, (Permutation_length Hfilter).
      rewrite <- Zlength_correct, Zlength_Zrange__final_result by lia. lia.
  - set (selected := filter
      (fun i => if prop_dec (chosen i) then true else false)
      (Zrange 0 (Zlength students))).
    set (starts := filter
      (fun start => if prop_dec (SubjectBlockStart students start)
                    then true else false)
      (Zrange 0 (Zlength students))).
    set (belongs := fun i start => if prop_dec
      (CandidateSubject students i = CandidateSubject students start)
      then true else false).
    assert (Hskill : DelegationSkill students chosen =
      ListLib.sum (map (CandidateSkill students) selected)).
    { unfold DelegationSkill, CandidateSkill.
      apply finite_sum_as_filter__final_result. apply Permutation_refl. }
    assert (Hpartition :
      ListLib.sum (map (CandidateSkill students) selected) =
      ListLib.sum (map
        (fun start => ListLib.sum
          (map (CandidateSkill students)
            (filter (fun i => belongs i start) selected))) starts)).
    { apply list_sum_map_partition__final_result.
      - subst starts. apply NoDup_filter. apply NoDup_Zrange.
      - intros i Hi. unfold selected in Hi.
        apply filter_In in Hi as [Hirange Hitest].
        destruct (prop_dec (chosen i)) as [Hchosen|Hnot];
          [|discriminate].
        destruct Hchosen as
          [start [Hstart [Hhas [Hpositive Hindex]]]].
        exists start. split.
        + subst starts. apply filter_In. split.
          * apply In_Zrange. destruct Hstart as [[? ?] _]. lia.
          * destruct (prop_dec (SubjectBlockStart students start));
              [reflexivity|contradiction].
        + split.
          * unfold belongs. destruct Hhas as [_ [_ [_ Hall]]].
            destruct (prop_dec
              (CandidateSubject students i = CandidateSubject students start));
              [reflexivity|]. exfalso. apply n. apply Hall. exact Hindex.
          * intros other Hother_in Hbelongs.
            subst starts. apply filter_In in Hother_in as [Hother_range Htest].
            assert (Hother_start : SubjectBlockStart students other).
            { destruct (prop_dec (SubjectBlockStart students other));
                [assumption|discriminate]. }
            assert (Hisubject : CandidateSubject students i =
                CandidateSubject students start).
            { destruct Hhas as [_ [_ [_ Hall]]]. apply Hall. exact Hindex. }
            assert (Hiother : CandidateSubject students i =
                CandidateSubject students other).
            { unfold belongs in Hbelongs.
              destruct (prop_dec
                (CandidateSubject students i = CandidateSubject students other));
                [assumption|discriminate]. }
            apply subject_block_start_unique__final_result with
              (students := students); try assumption.
            rewrite <- Hisubject, Hiother. reflexivity. }
    assert (Hblocks :
      ListLib.sum (map
        (fun start => ListLib.sum
          (map (CandidateSkill students)
            (filter (fun i => belongs i start) selected))) starts) =
      ListLib.sum (map
        (fun start => SubjectContribution students start k) starts)).
    { f_equal. apply map_ext_in. intros start Hstart_in.
      assert (Hstart : SubjectBlockStart students start).
      { subst starts. apply filter_In in Hstart_in as [_ Htest].
        destruct (prop_dec (SubjectBlockStart students start));
          [assumption|discriminate]. }
      set (block := filter (fun i => belongs i start) selected).
      destruct (prop_dec (SubjectHasK students start k)) as [Hhas|Hnohas].
      + destruct (Z_lt_dec 0 (SkillSum students start (start + k)))
          as [Hpositive|Hnonpositive].
        * assert (Hblock_perm : Permutation block (Zrange start (start + k))).
          { apply NoDup_Permutation.
            - unfold block. apply NoDup_filter. unfold selected.
              apply NoDup_filter. apply NoDup_Zrange.
            - apply NoDup_Zrange.
            - intros i. unfold block, selected.
              rewrite filter_In, filter_In, <- !In_Zrange. split.
              + intros [[[Hi0 Hin] Hchosen_test] Hbelongs].
                destruct (prop_dec (chosen i)) as [Hchosen|Hnot];
                  [|discriminate].
                destruct Hchosen as
                  [other [Hother_start [Hother_has
                    [Hother_positive Hother_range]]]].
                assert (Hisubject : CandidateSubject students i =
                    CandidateSubject students start).
                { unfold belongs in Hbelongs.
                  destruct (prop_dec
                    (CandidateSubject students i =
                     CandidateSubject students start));
                    [assumption|discriminate]. }
                assert (Hother_subject : CandidateSubject students i =
                    CandidateSubject students other).
                { destruct Hother_has as [_ [_ [_ Hall]]].
                  apply Hall. exact Hother_range. }
                assert (other = start).
                { apply subject_block_start_unique__final_result with
                    (students := students); try assumption.
                  rewrite <- Hother_subject, Hisubject. reflexivity. }
                subst other. exact Hother_range.
              + intros Hirange. repeat split.
                -- pose proof Hstart as Hstart_bounds.
                   destruct Hstart_bounds as [[Hstart0 Hstartn] Hboundary].
                   destruct Hhas as [_ [_ [Hend _]]]. lia.
                -- pose proof Hstart as Hstart_bounds.
                   destruct Hstart_bounds as [[Hstart0 Hstartn] Hboundary].
                   destruct Hhas as [_ [_ [Hend _]]]. lia.
                -- destruct (prop_dec (chosen i)) as [Hyes|Hno];
                     [reflexivity|]. exfalso. apply Hno.
                   unfold chosen. exists start. split; [exact Hstart|].
                   split; [exact Hhas|]. split; assumption.
                -- unfold belongs. destruct (prop_dec
                     (CandidateSubject students i =
                      CandidateSubject students start)); [reflexivity|].
                   exfalso. apply n. destruct Hhas as [_ [_ [_ Hall]]].
                   apply Hall. exact Hirange. }
          fold block.
          rewrite (sum_permutation__final_result _ _
            (Permutation_map (CandidateSkill students) Hblock_perm)).
          rewrite <- skill_sum_as_index_list__final_result by
            (destruct Hhas as [[[Hstart0 Hstartn] Hboundary]
              [Hk1 [Hend Hall]]]; lia).
          unfold SubjectContribution.
          destruct (prop_dec (SubjectHasK students start k));
            [|contradiction]. symmetry. apply Z.max_r. lia.
        * assert (Hblock_empty : block = nil).
          { destruct block as [|i rest] eqn:Hb; [reflexivity|].
            exfalso. assert (Hi : In i block).
            { rewrite Hb. left. reflexivity. }
            unfold block, selected in Hi.
            apply filter_In in Hi as [Hiselected Hbelongs].
            apply filter_In in Hiselected as [Hirange Hchosen_test].
            destruct (prop_dec (chosen i)) as [Hchosen|Hnot];
              [|discriminate].
            destruct Hchosen as
              [other [Hother_start [Hother_has
                [Hother_positive Hother_range]]]].
            assert (Hisubject : CandidateSubject students i =
                CandidateSubject students start).
            { unfold belongs in Hbelongs. destruct (prop_dec
                (CandidateSubject students i = CandidateSubject students start));
                [assumption|discriminate]. }
            assert (Hother_subject : CandidateSubject students i =
                CandidateSubject students other).
            { destruct Hother_has as [_ [_ [_ Hall]]].
              apply Hall. exact Hother_range. }
            assert (other = start).
            { apply subject_block_start_unique__final_result with
                (students := students); try assumption.
              rewrite <- Hother_subject, Hisubject. reflexivity. }
            subst other. lia. }
          fold block. rewrite Hblock_empty. simpl.
          unfold SubjectContribution.
          destruct (prop_dec (SubjectHasK students start k));
            [|contradiction]. rewrite Z.max_l by lia. reflexivity.
      + assert (Hblock_empty : block = nil).
        { destruct block as [|i rest] eqn:Hb; [reflexivity|].
          exfalso. assert (Hi : In i block).
          { rewrite Hb. left. reflexivity. }
          unfold block, selected in Hi.
          apply filter_In in Hi as [Hiselected Hbelongs].
          apply filter_In in Hiselected as [Hirange Hchosen_test].
          destruct (prop_dec (chosen i)) as [Hchosen|Hnot];
            [|discriminate].
          destruct Hchosen as
            [other [Hother_start [Hother_has
              [Hother_positive Hother_range]]]].
          assert (Hisubject : CandidateSubject students i =
              CandidateSubject students start).
          { unfold belongs in Hbelongs. destruct (prop_dec
              (CandidateSubject students i = CandidateSubject students start));
              [assumption|discriminate]. }
          assert (Hother_subject : CandidateSubject students i =
              CandidateSubject students other).
          { destruct Hother_has as [_ [_ [_ Hall]]].
            apply Hall. exact Hother_range. }
          assert (other = start).
          { apply subject_block_start_unique__final_result with
              (students := students); try assumption.
            rewrite <- Hother_subject, Hisubject. reflexivity. }
          subst other. contradiction. }
        fold block. rewrite Hblock_empty. simpl.
        unfold SubjectContribution.
        destruct (prop_dec (SubjectHasK students start k));
          [contradiction|reflexivity]. }
    assert (Hcompleted :
      CompletedContribution students (Zlength students) k =
      ListLib.sum
        (map (fun start => SubjectContribution students start k) starts)).
    { unfold CompletedContribution.
      apply finite_sum_as_filter__final_result. apply Permutation_refl. }
    rewrite Hskill, Hpartition, Hblocks. symmetry. exact Hcompleted.
Qed.
Lemma NoDup_map_injective_on__final_result :
  forall {A B : Type} (f : A -> B) xs,
    NoDup xs ->
    (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
    NoDup (map f xs).
Proof.
  intros A B f xs Hnodup. induction Hnodup as [|x xs Hnotin Hnodup IH];
    intros Hinj; simpl; constructor.
  - intro Hinx. apply in_map_iff in Hinx as [y [Hfy Hy]].
    apply Hnotin. assert (x = y).
    { apply (Hinj x y); simpl; auto. }
    subst y. exact Hy.
  - apply IH. intros a b Ha Hb Hab.
    apply Hinj; simpl; auto.
Qed.
Lemma valid_delegation_permutation_transport__final_result :
  forall source dest chosen,
    Permutation dest source ->
    ValidDelegation source chosen ->
    exists transported,
      ValidDelegation dest transported /\
      DelegationSkill source chosen = DelegationSkill dest transported.
Proof.
  intros source dest chosen Hperm Hvalid.
  pose proof (proj1 (Permutation_nth dest source (0, 0)) Hperm) as Hnth_data.
  simpl in Hnth_data.
  destruct Hnth_data as [Hlength [f [Hfun [Hinj Hnth]]]].
  set (fz := fun i : Z => Z.of_nat (f (Z.to_nat i))).
  assert (Hzlength : Zlength source = Zlength dest).
  { rewrite !Zlength_correct, Hlength. reflexivity. }
  assert (Hnat_bound : forall i,
      0 <= i < Zlength source -> (Z.to_nat i < length dest)%nat).
  { intros i Hi. rewrite <- Hlength.
    replace (length source) with
      (Z.to_nat (Z.of_nat (length source))) by apply Nat2Z.id.
    apply (proj1 (Z2Nat.inj_lt i (Z.of_nat (length source))
      ltac:(lia) ltac:(lia))).
    rewrite <- Zlength_correct. exact (proj2 Hi). }
  assert (Hfz_bounds : forall i,
      0 <= i < Zlength source -> 0 <= fz i < Zlength dest).
  { intros i Hi. unfold fz. split; [lia|].
    rewrite Zlength_correct.
    apply Nat2Z.inj_lt.
    apply Hfun. apply Hnat_bound. exact Hi. }
  assert (Hfz_inj : forall i j,
      0 <= i < Zlength source -> 0 <= j < Zlength source ->
      fz i = fz j -> i = j).
  { intros i j Hi Hj Heq. unfold fz in Heq.
    apply Nat2Z.inj in Heq.
    apply Hinj in Heq.
    - rewrite <- (Z2Nat.id i), <- (Z2Nat.id j) by lia. now rewrite Heq.
    - apply Hnat_bound. exact Hi.
    - apply Hnat_bound. exact Hj. }
  assert (Hcandidate : forall i,
      0 <= i < Zlength source ->
      Znth i source (0, 0) = Znth (fz i) dest (0, 0)).
  { intros i Hi. unfold Znth, fz.
    rewrite Nat2Z.id. apply Hnth.
    apply Hnat_bound. exact Hi. }
  set (transported := fun j : Z => exists i,
    0 <= i < Zlength source /\ chosen i /\ j = fz i).
  exists transported. split.
  - destruct Hvalid as [Hchosen_bounds [size [Hsize Huniform]]].
    split.
    + intros j [i [Hi [Hchosen Hj]]]. subst j. apply Hfz_bounds. exact Hi.
    + exists size. split; [exact Hsize|]. intros subject Hex.
      assert (Hsource_exists : exists i,
        chosen i /\ fst (Znth i source (0, 0)) = subject).
      { destruct Hex as [j [[i [Hi [Hchosen Hj]]] Hsubject]].
        exists i. split; [exact Hchosen|].
        subst j. rewrite Hcandidate in * by exact Hi. exact Hsubject. }
      specialize (Huniform subject Hsource_exists).
      rewrite (set_card_as_filter_length__final_result
        0 (Zlength dest)
        (fun j => transported j /\ CandidateSubject dest j = subject)
        _ (Zrange 0 (Zlength dest)) (Permutation_refl _)).
      rewrite (set_card_as_filter_length__final_result
        0 (Zlength source)
        (fun i => chosen i /\ CandidateSubject source i = subject)
        _ (Zrange 0 (Zlength source)) (Permutation_refl _)) in Huniform.
      set (src := filter
        (fun i => if prop_dec
          (chosen i /\ CandidateSubject source i = subject)
          then true else false) (Zrange 0 (Zlength source))).
      set (dst := filter
        (fun j => if prop_dec
          (transported j /\ CandidateSubject dest j = subject)
          then true else false) (Zrange 0 (Zlength dest))).
      assert (Hsrc_bounds : forall i, In i src ->
          0 <= i < Zlength source).
      { intros i Hi. unfold src in Hi. apply filter_In in Hi as [Hi _].
        apply In_Zrange. exact Hi. }
      assert (Hindices : Permutation dst (map fz src)).
      { apply NoDup_Permutation.
        - unfold dst. apply NoDup_filter. apply NoDup_Zrange.
        - apply NoDup_map_injective_on__final_result.
          + unfold src. apply NoDup_filter. apply NoDup_Zrange.
          + intros i j Hi Hj Heq. apply Hfz_inj; try apply Hsrc_bounds;
              assumption.
        - intros j. rewrite in_map_iff. split.
          + intro Hj. unfold dst in Hj. apply filter_In in Hj as [Hjrange Htest].
            destruct (prop_dec
              (transported j /\ CandidateSubject dest j = subject))
              as [[Htrans Hsubject]|Hnot]; [|discriminate].
            destruct Htrans as [i [Hi [Hchosen Hj]]].
            exists i. split; [symmetry; exact Hj|].
            unfold src. apply filter_In. split.
            * apply In_Zrange. exact Hi.
            * destruct (prop_dec
                (chosen i /\ CandidateSubject source i = subject))
              as [Hyes|Hno]; [reflexivity|].
              exfalso. apply Hno. split; [exact Hchosen|].
              subst j. unfold CandidateSubject in Hsubject |- *.
              rewrite Hcandidate by exact Hi. exact Hsubject.
          + intros [i [Hji Hi]]. subst j.
            unfold src in Hi. apply filter_In in Hi as [Hirange Htest].
            apply In_Zrange in Hirange.
            destruct (prop_dec
              (chosen i /\ CandidateSubject source i = subject))
              as [[Hchosen Hsubject]|Hnot]; [|discriminate].
            unfold dst. apply filter_In. split.
            * apply In_Zrange. apply Hfz_bounds. exact Hirange.
            * destruct (prop_dec
                (transported (fz i) /\
                 CandidateSubject dest (fz i) = subject))
                as [Hyes|Hno]; [reflexivity|].
              exfalso. apply Hno. split.
              -- unfold transported. exists i. auto.
              -- unfold CandidateSubject in *.
                 rewrite <- Hcandidate by exact Hirange. exact Hsubject. }
      fold src in Huniform. fold dst.
      rewrite Zlength_correct, (Permutation_length Hindices), length_map.
      rewrite <- Zlength_correct. exact Huniform.
  - set (src := filter
      (fun i => if prop_dec (chosen i) then true else false)
      (Zrange 0 (Zlength source))).
    set (dst := filter
      (fun j => if prop_dec (transported j) then true else false)
      (Zrange 0 (Zlength dest))).
    assert (Hsrc_bounds : forall i, In i src ->
        0 <= i < Zlength source).
    { intros i Hi. unfold src in Hi. apply filter_In in Hi as [Hi _].
      apply In_Zrange. exact Hi. }
    assert (Hindices : Permutation dst (map fz src)).
    { apply NoDup_Permutation.
      - unfold dst. apply NoDup_filter. apply NoDup_Zrange.
      - apply NoDup_map_injective_on__final_result.
        + unfold src. apply NoDup_filter. apply NoDup_Zrange.
        + intros i j Hi Hj Heq. apply Hfz_inj; try apply Hsrc_bounds;
            assumption.
      - intros j. rewrite in_map_iff. split.
        + intro Hj. unfold dst in Hj. apply filter_In in Hj as [Hjrange Htest].
          destruct (prop_dec (transported j)) as [Htrans|Hnot];
            [|discriminate].
          destruct Htrans as [i [Hi [Hchosen Hj]]]. exists i.
          split; [symmetry; exact Hj|]. unfold src. apply filter_In. split.
          * apply In_Zrange. exact Hi.
          * destruct (prop_dec (chosen i)); [reflexivity|contradiction].
        + intros [i [Hji Hi]]. subst j. unfold src in Hi.
          apply filter_In in Hi as [Hirange Htest].
          apply In_Zrange in Hirange.
          destruct (prop_dec (chosen i)) as [Hchosen|Hnot];
            [|discriminate].
          unfold dst. apply filter_In. split.
          * apply In_Zrange. apply Hfz_bounds. exact Hirange.
          * destruct (prop_dec (transported (fz i)));
              [reflexivity|]. exfalso. apply n.
            unfold transported. exists i. auto. }
    unfold DelegationSkill, CandidateSkill.
    rewrite (finite_sum_as_filter__final_result
      0 (Zlength source) chosen _
      (fun i => snd (Znth i source (0, 0)))
      (Zrange 0 (Zlength source))
      (Permutation_refl _)).
    rewrite (finite_sum_as_filter__final_result
      0 (Zlength dest) transported _
      (fun j => snd (Znth j dest (0, 0)))
      (Zrange 0 (Zlength dest))
      (Permutation_refl _)).
    fold src dst.
    rewrite (sum_permutation__final_result _ _
      (Permutation_map (fun j => snd (Znth j dest (0, 0))) Hindices)).
    rewrite map_map. apply f_equal. apply map_ext_in. intros i Hi.
    rewrite <- Hcandidate by (apply Hsrc_bounds; exact Hi). reflexivity.
Qed.
Lemma competition_full_state_implies_spec__final_result :
  forall m original sorted totals answer,
    1 <= Zlength sorted ->
    Permutation original sorted ->
    CandidatesSorted sorted ->
    CompetitionOuterState sorted (Zlength sorted) totals ->
    CompetitionAnswerPrefix totals (Zlength sorted) (Zlength sorted) answer ->
    Spec m original answer.
Proof.
  intros m original sorted totals answer Hnonempty Hperm Hsorted Houter Hanswer.
  destruct Houter as [Hboundary [Htotals_length [Htotal0 Htotals]]].
  destruct Hanswer as [Hanswer_length [Hdone Hanswer]].
  assert (Hspec_sorted : Spec m sorted answer).
  { unfold Spec.
    destruct Hanswer as [[Hmaximum Hge]|[Hall Heq]].
    - left. split; [|exact Hge].
      destruct Hmaximum as [k [[Hk Hmax] Hanswer_eq]].
      destruct (completed_contribution_attainable__final_result
        sorted k Hsorted Hk) as [chosen [Hvalid Hskill]].
      exists chosen. split.
      + split; [exact Hvalid|]. intros other Hother.
        destruct (completed_contribution_upper__final_result
          sorted other Hsorted Hnonempty Hother) as [other_k [Hother_k Hupper]].
        specialize (Hmax other_k Hother_k).
        rewrite (Htotals other_k Hother_k) in Hmax.
        rewrite (Htotals k Hk) in Hmax.
        rewrite Htotals in Hanswer_eq by exact Hk.
        eapply Z.le_trans; [exact Hupper|].
        eapply Z.le_trans; [exact Hmax|].
        rewrite Hskill, Hanswer_eq. apply Z.le_refl.
      + rewrite Hskill, <- Hanswer_eq.
        symmetry. apply Htotals. exact Hk.
    - right. split; [|exact Heq]. intros chosen Hvalid.
      destruct (completed_contribution_upper__final_result
        sorted chosen Hsorted Hnonempty Hvalid) as [k [Hk Hupper]].
      specialize (Hall k Hk). rewrite Htotals in Hall by exact Hk. lia. }
  unfold Spec in Hspec_sorted |- *.
  eapply (max_default_eq_forward
    Z.le
    (DelegationSkill sorted) (DelegationSkill original)
    (ValidDelegation sorted) (ValidDelegation original) 0 answer).
  - exact Hspec_sorted.
  - intros chosen Hvalid.
    destruct (valid_delegation_permutation_transport__final_result
      sorted original chosen Hperm Hvalid) as
      [transported [Htransported Heq]].
    exists transported. split; [exact Htransported|]. lia.
  - intros chosen Hvalid.
    destruct (valid_delegation_permutation_transport__final_result
      original sorted chosen (Permutation_sym Hperm) Hvalid) as
      [transported [Htransported Heq]].
    exists transported. split; [exact Htransported|]. lia.
Qed.
