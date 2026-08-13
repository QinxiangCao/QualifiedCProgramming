Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** [true] is a push and [false] is a pop.  [stack_run depth ops]
    rejects exactly those traces which try to pop an empty stack. *)
Fixpoint stack_run (depth : nat) (ops : list bool) : option nat :=
  match ops with
  | nil => Some depth
  | true :: rest => stack_run (S depth) rest
  | false :: rest =>
      match depth with
      | O => None
      | S depth' => stack_run depth' rest
      end
  end.

Fixpoint stack_push_count (ops : list bool) : nat :=
  match ops with
  | nil => O
  | true :: rest => S (stack_push_count rest)
  | false :: rest => stack_push_count rest
  end.

(** All push/pop words of an exact length.  This is a canonical finite
    carrier used only to take the cardinality of the mathematical set. *)
Fixpoint all_stack_words (len : nat) : list (list bool) :=
  match len with
  | O => cons nil nil
  | S len' =>
      map (cons true) (all_stack_words len') ++
      map (cons false) (all_stack_words len')
  end.

Definition legal_stack_completion_nat
    (pushes depth : nat) (ops : list bool) : Prop :=
  length ops = (2 * pushes + depth)%nat /\
  stack_push_count ops = pushes /\
  stack_run depth ops = Some O.

Definition legal_stack_completionb
    (pushes depth : nat) (ops : list bool) : bool :=
  Nat.eqb (length ops) (2 * pushes + depth) &&
  Nat.eqb (stack_push_count ops) pushes &&
  match stack_run depth ops with
  | Some O => true
  | _ => false
  end.

Definition stack_completion_set (pushes depth : nat) : list (list bool) :=
  filter (legal_stack_completionb pushes depth)
    (all_stack_words (2 * pushes + depth)).

Definition LegalStackCompletion
    (pushes depth : Z) (ops : list bool) : Prop :=
  0 <= pushes /\
  0 <= depth /\
  legal_stack_completion_nat (Z.to_nat pushes) (Z.to_nat depth) ops.

Definition LegalStackBehavior (pushes : Z) (ops : list bool) : Prop :=
  LegalStackCompletion pushes 0 ops.

Definition StackSequenceSet (pushes : Z) : list (list bool) :=
  stack_completion_set (Z.to_nat pushes) O.

Definition StackCompletionCount
    (pushes depth value : Z) : Prop :=
  0 <= pushes /\
  0 <= depth /\
  value = Z.of_nat
    (length (stack_completion_set (Z.to_nat pushes) (Z.to_nat depth))).

(** The requested result is the cardinality of the finite set of legal
    push/pop traces which starts and ends with an empty stack. *)
Definition StackSequenceCount (pushes value : Z) : Prop :=
  0 <= pushes /\
  value = Z.of_nat (length (StackSequenceSet pushes)) /\
  forall ops,
    In ops (StackSequenceSet pushes) <->
    LegalStackBehavior pushes ops.

Definition StackCellIndex (n row col : Z) : Z :=
  row * (n + 1) + col.

(** The exponential bound counts all push/pop words of the required
    length; legal completions form a subset. *)
Definition StackCellBound (row col value : Z) : Prop :=
  0 <= row /\
  0 <= col /\
  0 <= value <= 2 ^ (2 * row + col).

(** Only the lower-left triangle can influence the requested cell.  The
    remaining cells are still tracked by [StackCellBound] for C safety. *)
Definition StackCellCorrect
    (n row col value : Z) : Prop :=
  row + col <= n -> StackCompletionCount row col value.

Definition StackTablePrefix
    (n : Z) (table : list Z) (written : Z) : Prop :=
  0 <= n /\
  (0 <= written /\ Zlength table = written) /\
  forall row col,
    0 <= row <= n ->
    0 <= col <= n ->
    0 <= StackCellIndex n row col < written ->
    StackCellBound row col
      (Znth (StackCellIndex n row col) table 0) /\
    StackCellCorrect n row col
      (Znth (StackCellIndex n row col) table 0).

Definition StackRowsDone
    (n : Z) (table : list Z) (rows_done : Z) : Prop :=
  0 <= rows_done /\
  StackTablePrefix n table (rows_done * (n + 1)).

Definition StackRowProgress
    (n : Z) (table : list Z) (row col : Z) : Prop :=
  0 <= row /\
  0 <= col <= n + 1 /\
  StackTablePrefix n table (row * (n + 1) + col).

Lemma all_stack_words_spec :
  forall len ops,
    In ops (all_stack_words len) <-> length ops = len.
Proof.
  induction len as [| len IH]; intros ops.
  - split.
    + simpl. intros [Heq | Hfalse].
      * subst ops. reflexivity.
      * contradiction.
    + intros Hlen. destruct ops as [| op rest].
      * simpl. auto.
      * discriminate.
  - simpl. rewrite in_app_iff.
    split.
    + intros [Hin | Hin].
      * apply in_map_iff in Hin.
        destruct Hin as [rest [Hop Hin]].
        subst ops. simpl. f_equal.
        apply (proj1 (IH rest)); exact Hin.
      * apply in_map_iff in Hin.
        destruct Hin as [rest [Hop Hin]].
        subst ops. simpl. f_equal.
        apply (proj1 (IH rest)); exact Hin.
    + intros Hlen.
      destruct ops as [| op rest]; [discriminate |].
      simpl in Hlen. injection Hlen as Hrest.
      destruct op.
      * left. apply in_map. apply (proj2 (IH rest)). exact Hrest.
      * right. apply in_map. apply (proj2 (IH rest)). exact Hrest.
Qed.

Lemma legal_stack_completionb_spec :
  forall pushes depth ops,
    legal_stack_completionb pushes depth ops = true <->
    legal_stack_completion_nat pushes depth ops.
Proof.
  intros pushes depth ops.
  unfold legal_stack_completionb, legal_stack_completion_nat.
  rewrite Bool.andb_true_iff, Bool.andb_true_iff.
  rewrite Nat.eqb_eq, Nat.eqb_eq.
  destruct (stack_run depth ops) as [result |] eqn:Hrun.
  - destruct result.
    + simpl. intuition congruence.
    + simpl. intuition congruence.
  - simpl. intuition congruence.
Qed.

Lemma stack_completion_set_spec :
  forall pushes depth ops,
    In ops (stack_completion_set pushes depth) <->
    legal_stack_completion_nat pushes depth ops.
Proof.
  intros pushes depth ops.
  unfold stack_completion_set.
  rewrite filter_In, all_stack_words_spec, legal_stack_completionb_spec.
  split.
  - intros [_ Hlegal]. exact Hlegal.
  - intros Hlegal. split; [exact (proj1 Hlegal) | exact Hlegal].
Qed.

Lemma StackSequenceSet_spec :
  forall pushes ops,
    0 <= pushes ->
    (In ops (StackSequenceSet pushes) <->
     LegalStackBehavior pushes ops).
Proof.
  intros pushes ops Hpushes.
  unfold StackSequenceSet, LegalStackBehavior, LegalStackCompletion.
  rewrite stack_completion_set_spec.
  split.
  - intros Hlegal.
    split; [exact Hpushes |].
    split; [lia | exact Hlegal].
  - intros [_ [_ Hlegal]]. exact Hlegal.
Qed.

Lemma StackCompletionCount_zero_to_StackSequenceCount :
  forall pushes value,
    StackCompletionCount pushes 0 value ->
    StackSequenceCount pushes value.
Proof.
  intros pushes value Hcount.
  unfold StackCompletionCount in Hcount.
  destruct Hcount as [Hpushes [_ Hvalue]].
  unfold StackSequenceCount, StackSequenceSet.
  split; [exact Hpushes |].
  split; [exact Hvalue |].
  exact (fun ops => StackSequenceSet_spec pushes ops Hpushes).
Qed.

Lemma bounded_0_7_cases__cell_dp :
  forall x : Z,
    0 <= x <= 7 ->
    x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7.
Proof. intros; lia. Qed.
Lemma bounded_1_7_cases__cell_dp :
  forall x : Z,
    1 <= x <= 7 ->
    x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7.
Proof. intros; lia. Qed.
Lemma StackTablePrefix_snoc__cell_dp :
  forall n table written row col v,
    StackTablePrefix n table written ->
    Zlength table = written ->
    0 <= row <= n ->
    0 <= col <= n ->
    StackCellIndex n row col = written ->
    StackCellBound row col v ->
    StackCellCorrect n row col v ->
    StackTablePrefix n (table ++ v :: nil) (written + 1).
Proof.
  intros n table written row col v Hprefix Hlen Hrow Hcol Hindex Hbound Hcorrect.
  unfold StackTablePrefix in *.
  destruct Hprefix as [Hn [Hwritten Hcells]].
  split; [exact Hn |].
  split.
  - rewrite Zlength_app_cons. lia.
  - intros r c Hr Hc Hlt.
    destruct (Z_lt_ge_dec (StackCellIndex n r c) written) as [Hold | Hnew].
    + specialize (Hcells r c Hr Hc ltac:(lia)).
      rewrite app_Znth1 by (rewrite Hlen; lia).
      exact Hcells.
    + assert (Hrrow : r = row) by
          (unfold StackCellIndex in *; nia).
      subst r.
      assert (Hccol : c = col) by
          (unfold StackCellIndex in *; nia).
      subst c.
      rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite Hlen, Hindex.
      replace (written - written) with 0 by lia.
      simpl.
      split; assumption.
Qed.
Lemma StackRowProgress_snoc__cell_dp :
  forall n table row col v,
    StackRowProgress n table row col ->
    Zlength table = row * (n + 1) + col ->
    0 <= row <= n ->
    0 <= col <= n ->
    StackCellBound row col v ->
    StackCellCorrect n row col v ->
    StackRowProgress n (table ++ v :: nil) row (col + 1).
Proof.
  intros n table row col v Hprogress Hlen Hrow Hcol Hbound Hcorrect.
  unfold StackRowProgress in *.
  destruct Hprogress as [Hrow0 [Hcolprog Hprefix]].
  split; [exact Hrow0 |].
  split; [lia |].
  replace (row * (n + 1) + (col + 1))
    with (row * (n + 1) + col + 1) by lia.
  eapply StackTablePrefix_snoc__cell_dp with
      (written := row * (n + 1) + col) (row := row) (col := col);
    eauto.
Qed.
Lemma StackCellBound_zero_row__cell_dp :
  forall col,
    0 <= col <= 7 ->
    StackCellBound 0 col 1.
Proof.
  intros col Hcol.
  unfold StackCellBound.
  split; [lia |].
  split; [lia |].
  split; [lia |].
  pose proof (Z.pow_pos_nonneg 2 col ltac:(lia) ltac:(lia)).
  lia.
Qed.
Lemma StackCellBound_copy_boundary__cell_dp :
  forall row value,
    1 <= row <= 7 ->
    StackCellBound (row - 1) 1 value ->
    StackCellBound row 0 value.
Proof.
  intros row value Hrow Hbound.
  unfold StackCellBound in *.
  destruct Hbound as [_ [_ [Hnonneg Hupper]]].
  split; [lia |].
  split; [lia |].
  split; [exact Hnonneg |].
  destruct (bounded_1_7_cases__cell_dp row Hrow)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    cbn [Z.pow] in Hupper |-; lia.
Qed.
Lemma StackCellBound_add_step__cell_dp :
  forall row col a b,
    1 <= row <= 7 ->
    1 <= col <= 7 ->
    StackCellBound (row - 1) (col + 1) a ->
    StackCellBound row (col - 1) b ->
    StackCellBound row col (a + b).
Proof.
  intros row col a b Hrow Hcol Ha Hb.
  unfold StackCellBound in *.
  destruct Ha as [_ [_ [Ha0 Hau]]].
  destruct Hb as [_ [_ [Hb0 Hbu]]].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  destruct (bounded_1_7_cases__cell_dp row Hrow)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
  destruct (bounded_1_7_cases__cell_dp col Hcol)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    cbn [Z.pow] in Hau, Hbu |-; lia.
Qed.
Lemma StackCellBound_normalize_row_end__cell_dp :
  forall row col value,
    1 <= row <= 7 ->
    1 <= col <= 7 ->
    StackCellBound row 0 value ->
    StackCellBound (row - 1) (col + 1) value.
Proof.
  intros row col value Hrow Hcol Hbound.
  unfold StackCellBound in *.
  destruct Hbound as [_ [_ [Hnonneg Hupper]]].
  split; [lia |].
  split; [lia |].
  split; [exact Hnonneg |].
  destruct (bounded_1_7_cases__cell_dp row Hrow)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
  destruct (bounded_1_7_cases__cell_dp col Hcol)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    cbn [Z.pow] in Hupper |-; lia.
Qed.
Lemma StackCellBound_int_range__cell_dp :
  forall row col value,
    0 <= row <= 7 ->
    0 <= col <= 7 ->
    StackCellBound row col value ->
    -2147483648 <= value <= 2147483647.
Proof.
  intros row col value Hrow Hcol Hbound.
  unfold StackCellBound in *.
  destruct Hbound as [_ [_ [Hnonneg Hupper]]].
  split; [lia |].
  destruct (bounded_0_7_cases__cell_dp row Hrow)
    as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  destruct (bounded_0_7_cases__cell_dp col Hcol)
    as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    cbn [Z.pow] in Hupper |-; lia.
Qed.
Lemma StackCompletionCount_zero_row__cell_dp :
  forall depth,
    0 <= depth <= 7 ->
    StackCompletionCount 0 depth 1.
Proof.
  intros depth Hdepth.
  unfold StackCompletionCount.
  split; [lia |].
  split; [lia |].
  destruct (bounded_0_7_cases__cell_dp depth Hdepth)
    as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    vm_compute; reflexivity.
Qed.
Lemma StackCompletionCount_push_boundary__cell_dp :
  forall pushes value,
    1 <= pushes <= 7 ->
    StackCompletionCount (pushes - 1) 1 value ->
    StackCompletionCount pushes 0 value.
Proof.
  intros pushes value Hpushes Hcount.
  unfold StackCompletionCount in *.
  destruct Hcount as [_ [_ Hvalue]].
  split; [lia |].
  split; [lia |].
  destruct (bounded_1_7_cases__cell_dp pushes Hpushes)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    vm_compute in Hvalue |-; exact Hvalue.
Qed.
Lemma StackCompletionCount_step__cell_dp :
  forall pushes depth a b,
    1 <= pushes ->
    1 <= depth ->
    pushes + depth <= 7 ->
    StackCompletionCount (pushes - 1) (depth + 1) a ->
    StackCompletionCount pushes (depth - 1) b ->
    StackCompletionCount pushes depth (a + b).
Proof.
  intros pushes depth a b Hpushes Hdepth Hsum Ha Hb.
  unfold StackCompletionCount in *.
  destruct Ha as [_ [_ Ha]].
  destruct Hb as [_ [_ Hb]].
  split; [lia |].
  split; [lia |].
  assert (Hpushes7 : 1 <= pushes <= 7) by lia.
  assert (Hdepth7 : 1 <= depth <= 7) by lia.
  destruct (bounded_1_7_cases__cell_dp pushes Hpushes7)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
  destruct (bounded_1_7_cases__cell_dp depth Hdepth7)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    try lia; vm_compute in Ha, Hb; subst a; subst b; vm_compute; reflexivity.
Qed.

(** The following three lemmas package the pure part of one table update.
    [StackTablePrefix] records the exact length of the written prefix, so the
    appended value is also the value at the newly written matrix cell. *)
Lemma StackRowProgress_zero_row_extend__cell_dp :
  forall n table col,
    0 <= n <= 7 ->
    0 <= col <= n ->
    StackRowProgress n table 0 col ->
    let table' := table ++ 1 :: nil in
    StackRowProgress n table' 0 (col + 1) /\
    StackCellCorrect n 0 col
      (Znth (StackCellIndex n 0 col) table' 0) /\
    StackCellBound 0 col
      (Znth (StackCellIndex n 0 col) table' 0).
Proof.
  intros n table col Hn Hcol Hprogress.
  cbn.
  assert (Hlen : Zlength table = col).
  { unfold StackRowProgress, StackTablePrefix in Hprogress.
    destruct Hprogress as [_ [_ [_ [[_ Hlen] _]]]].
    lia. }
  assert (Hnew : Znth col (table ++ 1 :: nil) 0 = 1).
  { rewrite app_Znth2 by lia.
    rewrite Hlen.
    replace (col - col) with 0 by lia.
    reflexivity. }
  assert (Hbound : StackCellBound 0 col 1).
  { apply StackCellBound_zero_row__cell_dp. lia. }
  assert (Hcorrect : StackCellCorrect n 0 col 1).
  { unfold StackCellCorrect.
    intros _.
    apply StackCompletionCount_zero_row__cell_dp.
    lia. }
  assert (Hprogress' :
      StackRowProgress n (table ++ 1 :: nil) 0 (col + 1)).
  { eapply StackRowProgress_snoc__cell_dp; eauto; lia. }
  split; [exact Hprogress' |].
  unfold StackCellIndex.
  replace (0 * (n + 1) + col) with col by lia.
  rewrite Hnew.
  split; assumption.
Qed.

Lemma StackRowProgress_copy_boundary_extend__cell_dp :
  forall n table row,
    0 <= n <= 7 ->
    1 <= row <= n ->
    StackRowProgress n table row 0 ->
    let v := Znth (StackCellIndex n (row - 1) 1) table 0 in
    let table' := table ++ v :: nil in
    StackRowProgress n table' row 1 /\
    StackCellCorrect n row 0
      (Znth (StackCellIndex n row 0) table' 0) /\
    StackCellBound row 0
      (Znth (StackCellIndex n row 0) table' 0).
Proof.
  intros n table row Hn Hrow Hprogress.
  cbn.
  set (v := Znth (StackCellIndex n (row - 1) 1) table 0).
  assert (Hlen : Zlength table = row * (n + 1)).
  { unfold StackRowProgress, StackTablePrefix in Hprogress.
    destruct Hprogress as [_ [_ [_ [[_ Hlen] _]]]].
    lia. }
  assert (Hnew :
      Znth (StackCellIndex n row 0) (table ++ v :: nil) 0 = v).
  { unfold StackCellIndex.
    rewrite app_Znth2 by lia.
    rewrite Hlen.
    replace (row * (n + 1) + 0 - row * (n + 1)) with 0 by lia.
    reflexivity. }
  unfold StackRowProgress in Hprogress.
  destruct Hprogress as [_ [_ Hprefix]].
  pose proof Hprefix as Hprefix_keep.
  unfold StackTablePrefix in Hprefix.
  destruct Hprefix as [_ [_ Hcells]].
  pose proof (Hcells (row - 1) 1 ltac:(lia) ltac:(lia)
    ltac:(unfold StackCellIndex; nia)) as [Hsrc_bound Hsrc_correct].
  fold v in Hsrc_bound, Hsrc_correct.
  assert (Hbound : StackCellBound row 0 v).
  { eapply StackCellBound_copy_boundary__cell_dp; eauto; lia. }
  assert (Hcorrect : StackCellCorrect n row 0 v).
  { unfold StackCellCorrect.
    intros Htri.
    unfold StackCellCorrect in Hsrc_correct.
    pose proof (Hsrc_correct ltac:(lia)) as Hsrc_count.
    eapply StackCompletionCount_push_boundary__cell_dp; eauto; lia. }
  assert (Hprogress' :
      StackRowProgress n (table ++ v :: nil) row 1).
  { eapply StackRowProgress_snoc__cell_dp with
      (row := row) (col := 0) (v := v).
    - unfold StackRowProgress.
      split; [lia |]. split; [lia | exact Hprefix_keep].
    - lia.
    - lia.
    - lia.
    - exact Hbound.
    - exact Hcorrect. }
  split; [exact Hprogress' |].
  rewrite Hnew.
  split; assumption.
Qed.

Lemma StackRowProgress_add_step_extend__cell_dp :
  forall n table row col,
    0 <= n <= 7 ->
    1 <= row <= n ->
    1 <= col <= n ->
    StackRowProgress n table row col ->
    let a := Znth (StackCellIndex n (row - 1) (col + 1)) table 0 in
    let b := Znth (StackCellIndex n row (col - 1)) table 0 in
    let v := a + b in
    let table' := table ++ v :: nil in
    StackRowProgress n table' row (col + 1) /\
    StackCellCorrect n row col
      (Znth (StackCellIndex n row col) table' 0) /\
    StackCellBound row col
      (Znth (StackCellIndex n row col) table' 0).
Proof.
  intros n table row col Hn Hrow Hcol Hprogress.
  cbn.
  set (a := Znth (StackCellIndex n (row - 1) (col + 1)) table 0).
  set (b := Znth (StackCellIndex n row (col - 1)) table 0).
  set (v := a + b).
  assert (Hlen : Zlength table = row * (n + 1) + col).
  { unfold StackRowProgress, StackTablePrefix in Hprogress.
    destruct Hprogress as [_ [_ [_ [[_ Hlen] _]]]].
    lia. }
  assert (Hnew :
      Znth (StackCellIndex n row col) (table ++ v :: nil) 0 = v).
  { unfold StackCellIndex.
    rewrite app_Znth2 by lia.
    rewrite Hlen.
    replace (row * (n + 1) + col - (row * (n + 1) + col)) with 0 by lia.
    reflexivity. }
  unfold StackRowProgress in Hprogress.
  destruct Hprogress as [_ [_ Hprefix]].
  pose proof Hprefix as Hprefix_keep.
  unfold StackTablePrefix in Hprefix.
  destruct Hprefix as [_ [_ Hcells]].
  assert (Ha_bound : StackCellBound (row - 1) (col + 1) a).
  { unfold a.
    destruct (Z_lt_ge_dec col n) as [Hcol_lt | Hcol_end].
    - exact (proj1 (Hcells (row - 1) (col + 1) ltac:(lia) ltac:(lia)
        ltac:(unfold StackCellIndex; nia))).
    - assert (Hcol_eq : col = n) by lia.
      pose proof (proj1 (Hcells row 0 ltac:(lia) ltac:(lia)
        ltac:(unfold StackCellIndex; lia))) as Ha0.
      assert (Hidxeq : StackCellIndex n row 0 =
                       StackCellIndex n (row - 1) (col + 1)) by
        (unfold StackCellIndex; nia).
      rewrite Hidxeq in Ha0.
      eapply StackCellBound_normalize_row_end__cell_dp; eauto; lia. }
  pose proof (Hcells row (col - 1) ltac:(lia) ltac:(lia)
    ltac:(unfold StackCellIndex; lia)) as [Hb_bound Hb_correct].
  fold b in Hb_bound, Hb_correct.
  assert (Hbound : StackCellBound row col v).
  { unfold v. eapply StackCellBound_add_step__cell_dp; eauto; lia. }
  assert (Hcorrect : StackCellCorrect n row col v).
  { unfold StackCellCorrect.
    intros Htri.
    assert (Hcol_lt : col < n) by lia.
    unfold a.
    pose proof (proj2 (Hcells (row - 1) (col + 1) ltac:(lia) ltac:(lia)
      ltac:(unfold StackCellIndex; nia))) as Ha_correct.
    unfold StackCellCorrect in Ha_correct, Hb_correct.
    pose proof (Ha_correct ltac:(lia)) as Ha_count.
    pose proof (Hb_correct ltac:(lia)) as Hb_count.
    unfold v.
    eapply StackCompletionCount_step__cell_dp; eauto; lia. }
  assert (Hprogress' :
      StackRowProgress n (table ++ v :: nil) row (col + 1)).
  { eapply StackRowProgress_snoc__cell_dp.
    - unfold StackRowProgress.
      split; [lia |]. split; [lia | exact Hprefix_keep].
    - exact Hlen.
    - lia.
    - lia.
    - exact Hbound.
    - exact Hcorrect. }
  split; [exact Hprogress' |].
  rewrite Hnew.
  split; assumption.
Qed.
