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

(** Cardinalities describe only the requested mathematical counts.  The
    existing finite-word enumeration above is retained as a computation helper. *)
Definition StackCompletionCount (pushes depth value : Z) : Prop :=
  value = Zlength
    (stack_completion_set (Z.to_nat pushes) (Z.to_nat depth)).

Definition StackOperationWordCount (pushes value : Z) : Prop :=
  value = Zlength (StackSequenceSet pushes).

Definition StackCellIndex (n row col : Z) : Z :=
  row * (n + 1) + col.

Definition StackCellCorrect (n row col value : Z) : Prop :=
  row + col <= n -> StackCompletionCount row col value.

(** Only mathematical correctness belongs here.  Length, loop bounds and
    overflow bounds are separate premises in annotations and lemmas. *)
Definition StackTablePrefix (n : Z) (table : list Z) (written : Z) : Prop :=
  forall row col,
    0 <= row <= n -> 0 <= col <= n ->
    StackCellIndex n row col < written ->
    StackCellCorrect n row col (Znth (StackCellIndex n row col) table 0).

(* QCP identifiers cannot contain a dot; this notation exposes Z.pow. *)
Notation Zpower := Z.pow.

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
    StackCompletionCount pushes 0 value -> StackOperationWordCount pushes value.
Proof. intros pushes value H; exact H. Qed.

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
Lemma StackCellBound_zero_row__cell_dp :
  forall col,
    0 <= col <= 7 ->
    (0 <= 0 /\ 0 <= col /\ 0 <= 1 <= 2 ^ (2 * 0 + col)).
Proof.
  intros col Hcol.
  split; [lia |].
  split; [lia |].
  split; [lia |].
  pose proof (Z.pow_pos_nonneg 2 col ltac:(lia) ltac:(lia)).
  lia.
Qed.
Lemma StackCellBound_copy_boundary__cell_dp :
  forall row value,
    1 <= row <= 7 ->
    (0 <= (row - 1) /\ 0 <= 1 /\ 0 <= value <= 2 ^ (2 * (row - 1) + 1)) ->
    (0 <= row /\ 0 <= 0 /\ 0 <= value <= 2 ^ (2 * row + 0)).
Proof.
  intros row value Hrow Hbound.
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
    (0 <= (row - 1) /\ 0 <= (col + 1) /\ 0 <= a <= 2 ^ (2 * (row - 1) + (col + 1))) ->
    (0 <= row /\ 0 <= (col - 1) /\ 0 <= b <= 2 ^ (2 * row + (col - 1))) ->
    (0 <= row /\ 0 <= col /\ 0 <= (a + b) <= 2 ^ (2 * row + col)).
Proof.
  intros row col a b Hrow Hcol Ha Hb.
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
    (0 <= row /\ 0 <= 0 /\ 0 <= value <= 2 ^ (2 * row + 0)) ->
    (0 <= (row - 1) /\ 0 <= (col + 1) /\ 0 <= value <= 2 ^ (2 * (row - 1) + (col + 1))).
Proof.
  intros row col value Hrow Hcol Hbound.
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
    (0 <= row /\ 0 <= col /\ 0 <= value <= 2 ^ (2 * row + col)) ->
    -2147483648 <= value <= 2147483647.
Proof.
  intros row col value Hrow Hcol Hbound.
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
  rename Hcount into Hvalue.
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
  assert (Hpushes7 : 1 <= pushes <= 7) by lia.
  assert (Hdepth7 : 1 <= depth <= 7) by lia.
  destruct (bounded_1_7_cases__cell_dp pushes Hpushes7)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
  destruct (bounded_1_7_cases__cell_dp depth Hdepth7)
    as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    try lia; vm_compute in Ha, Hb; subst a; subst b; vm_compute; reflexivity.
Qed.


(** The old snoc proof works for any cell property.  Both correctness and
    the separately stated numerical bounds use this same list argument. *)
Lemma table_snoc_pointwise :
  forall (P : Z -> Z -> Z -> Prop) n table row col v,
    0 <= row <= n -> 0 <= col <= n ->
    Zlength table = row * (n + 1) + col ->
    (forall r c, 0 <= r <= n -> 0 <= c <= n ->
      StackCellIndex n r c < row * (n + 1) + col ->
      P r c (Znth (StackCellIndex n r c) table 0)) ->
    P row col v ->
    forall r c, 0 <= r <= n -> 0 <= c <= n ->
      StackCellIndex n r c < row * (n + 1) + (col + 1) ->
      P r c (Znth (StackCellIndex n r c) (table ++ [v]) 0).
Proof.
  intros P n table row col v Hrow Hcol Hlen Hcells Hnew r c Hr Hc Hlt.
  destruct (Z_lt_ge_dec (StackCellIndex n r c)
    (row * (n + 1) + col)) as [Hold | Hlast].
  - rewrite app_Znth1 by (rewrite Hlen; unfold StackCellIndex in *; nia).
    apply Hcells; assumption.
  - assert (r = row) by (unfold StackCellIndex in *; nia).
    subst r.
    assert (c = col) by (unfold StackCellIndex in *; nia).
    subst c.
    unfold StackCellIndex.
    rewrite app_Znth2 by lia.
    rewrite Hlen, Z.sub_diag. exact Hnew.
Qed.

Lemma StackTablePrefix_snoc__cell_dp :
  forall n table row col v,
    0 <= row <= n -> 0 <= col <= n ->
    Zlength table = row * (n + 1) + col ->
    StackTablePrefix n table (row * (n + 1) + col) ->
    StackCellCorrect n row col v ->
    StackTablePrefix n (table ++ [v]) (row * (n + 1) + (col + 1)).
Proof.
  intros n table row col v Hr Hc Hl Hp Hnew.
  exact (table_snoc_pointwise (StackCellCorrect n)
    n table row col v Hr Hc Hl Hp Hnew).
Qed.

Lemma StackTablePrefix_zero_row_extend__cell_dp :
  forall n table col,
    0 <= n <= 7 -> 0 <= col <= n -> Zlength table = col ->
    StackTablePrefix n table col ->
    StackTablePrefix n (table ++ [1]) (col + 1).
Proof.
  intros n table col Hn Hcol Hlen Hprefix.
  apply (StackTablePrefix_snoc__cell_dp n table 0 col 1);
    try assumption; try lia.
  unfold StackCellCorrect. intros.
  apply StackCompletionCount_zero_row__cell_dp. lia.
Qed.

Lemma StackTablePrefix_copy_boundary_extend__cell_dp :
  forall n table row,
    0 <= n <= 7 -> 1 <= row <= n -> Zlength table = row * (n + 1) ->
    StackTablePrefix n table (row * (n + 1)) ->
    StackTablePrefix n
      (table ++ [Znth (StackCellIndex n (row - 1) 1) table 0])
      (row * (n + 1) + 1).
Proof.
  intros n table row Hn Hrow Hlen Hprefix.
  apply (StackTablePrefix_snoc__cell_dp n table row 0);
    try (rewrite Z.add_0_r; assumption); try lia.
  unfold StackCellCorrect. intros Htri.
  pose proof (Hprefix (row - 1) 1 ltac:(lia) ltac:(lia)
    ltac:(unfold StackCellIndex; nia)) as Hsrc.
  apply StackCompletionCount_push_boundary__cell_dp; [lia |].
  apply Hsrc. lia.
Qed.

Lemma StackTablePrefix_add_step_extend__cell_dp :
  forall n table row col,
    0 <= n <= 7 -> 1 <= row <= n -> 1 <= col <= n ->
    Zlength table = row * (n + 1) + col ->
    StackTablePrefix n table (row * (n + 1) + col) ->
    StackTablePrefix n
      (table ++ [Znth (StackCellIndex n (row - 1) (col + 1)) table 0 +
                 Znth (StackCellIndex n row (col - 1)) table 0])
      (row * (n + 1) + (col + 1)).
Proof.
  intros n table row col Hn Hrow Hcol Hlen Hprefix.
  apply StackTablePrefix_snoc__cell_dp; try assumption; try lia.
  unfold StackCellCorrect. intros Htri.
  apply StackCompletionCount_step__cell_dp; try lia.
  - apply (Hprefix (row - 1) (col + 1));
      try (unfold StackCellIndex; nia).
  - apply (Hprefix row (col - 1));
      try (unfold StackCellIndex; nia).
Qed.

(** This bound depends on row and column, so its annotation uses indexed
    quantification, rather than a value-only Forall predicate. *)
Lemma table_add_bound__cell_dp :
  forall n table row col,
    0 <= n <= 7 -> 1 <= row <= n -> 1 <= col <= n ->
    (forall r c, 0 <= r <= n -> 0 <= c <= n ->
      StackCellIndex n r c < row * (n + 1) + col ->
      0 <= Znth (StackCellIndex n r c) table 0 <= 2 ^ (2 * r + c)) ->
    0 <= Znth (StackCellIndex n (row - 1) (col + 1)) table 0 +
         Znth (StackCellIndex n row (col - 1)) table 0 <= 2 ^ (2 * row + col).
Proof.
  intros n table row col Hn Hrow Hcol Hcells.
  assert (Ha : 0 <= Znth (StackCellIndex n (row - 1) (col + 1)) table 0
                  <= 2 ^ (2 * (row - 1) + (col + 1))).
  { destruct (Z_lt_ge_dec col n) as [Hlt | Hend].
    - apply Hcells; try lia; unfold StackCellIndex; nia.
    - assert (Heq : StackCellIndex n row 0 =
                    StackCellIndex n (row - 1) (col + 1))
        by (unfold StackCellIndex; nia).
      pose proof (Hcells row 0 ltac:(lia) ltac:(lia)
        ltac:(unfold StackCellIndex; nia)) as Ha0.
      rewrite Heq in Ha0.
      pose proof (StackCellBound_normalize_row_end__cell_dp row col
        (Znth (StackCellIndex n (row - 1) (col + 1)) table 0)
        ltac:(lia) ltac:(lia) ltac:(repeat split; tauto || lia)) as [_ [_ Ha]].
      exact Ha. }
  pose proof (Hcells row (col - 1) ltac:(lia) ltac:(lia)
    ltac:(unfold StackCellIndex; nia)) as Hb.
  pose proof (StackCellBound_add_step__cell_dp row col
    (Znth (StackCellIndex n (row - 1) (col + 1)) table 0)
    (Znth (StackCellIndex n row (col - 1)) table 0)
    ltac:(lia) ltac:(lia) ltac:(repeat split; tauto || lia)
    ltac:(repeat split; tauto || lia)) as [_ [_ Hsum]].
  exact Hsum.
Qed.

Lemma StackTablePrefix_result :
  forall n table,
    0 <= n ->
    StackTablePrefix n table ((n + 1) * (n + 1)) ->
    StackOperationWordCount n (Znth (n * (n + 1)) table 0).
Proof.
  intros n table Hn Hprefix.
  pose proof (Hprefix n 0 ltac:(lia) ltac:(lia)
    ltac:(unfold StackCellIndex; nia)) as Hcell.
  unfold StackCellCorrect, StackCellIndex in Hcell.
  repeat rewrite Z.add_0_r in Hcell.
  apply StackCompletionCount_zero_to_StackSequenceCount.
  apply Hcell. lia.
Qed.

From SumLib Require Import Sum FiniteExtra ZRange.
Require Import Coq.Lists.ListDec.

(** Actual stack semantics: remaining input, stack top first, and output in
    production order.  A failed push/pop makes the execution invalid. *)
Definition StackValueStep
    (state : option (list Z * list Z * list Z)) (push : bool) :=
  match state with
  | None => None
  | Some (input, stack, output) =>
      if push then
        match input with
        | [] => None
        | x :: rest => Some (rest, x :: stack, output)
        end
      else
        match stack with
        | [] => None
        | x :: rest => Some (input, rest, output ++ [x])
        end
  end.

Definition StackValueExecution (n : Z) (ops : list bool) :=
  fold_left StackValueStep ops (Some (Zrange 1 (n + 1), [], [])).

Definition StackOutput (n : Z) (output : list Z) : Prop :=
  exists ops, Zlength ops = 2 * n /\
    StackValueExecution n ops = Some ([], [], output).

Definition StackCompleteWord (n : Z) (ops : list bool) : bool :=
  Z.eqb (Zlength ops) (2 * n) &&
  match StackValueExecution n ops with
  | Some ([], [], _) => true
  | _ => false
  end.

Definition StackWordOutput (n : Z) (ops : list bool) : list Z :=
  match StackValueExecution n ops with
  | Some (_, _, output) => output
  | None => []
  end.

(** This enumeration serves only to construct the Finite instance.  The
    public set is defined above by actual input/stack/output semantics. *)
Definition StackOutputEnumeration (n : Z) : list (list Z) :=
  map (StackWordOutput n)
    (filter (StackCompleteWord n) (all_lists (Z.to_nat (2 * n)) [true; false])).

Lemma StackCompleteWord_spec n ops :
  StackCompleteWord n ops = true <->
  Zlength ops = 2 * n /\ exists output,
    StackValueExecution n ops = Some ([], [], output).
Proof.
  unfold StackCompleteWord. rewrite andb_true_iff, Z.eqb_eq.
  destruct (StackValueExecution n ops) as [[[input stack] output] |] eqn:He.
  - destruct input, stack; cbn.
    all: try solve [split; intros [Hlen Hbad];
      [discriminate | destruct Hbad as [result Hbad]; discriminate]].
    split; intros [Hlen H]; split; try assumption.
    + exists output. reflexivity.
    + reflexivity.
  - cbn. split; intros [Hlen Hbad];
      [discriminate | destruct Hbad as [result Hbad]; discriminate].
Qed.

Lemma StackOutputEnumeration_spec n output :
  StackOutput n output <-> In output (StackOutputEnumeration n).
Proof.
  unfold StackOutput, StackOutputEnumeration. rewrite in_map_iff.
  split.
  - intros [ops [Hlen Hrun]]. exists ops. split.
    + unfold StackWordOutput. rewrite Hrun. reflexivity.
    + apply filter_In. split.
      * apply in_all_lists. split.
        -- rewrite Zlength_correct in Hlen. lia.
        -- apply Forall_forall. intros x _. destruct x; simpl; auto.
      * apply StackCompleteWord_spec. split; [exact Hlen | eauto].
  - intros [ops [Hout Hin]]. apply filter_In in Hin as [_ Hcomplete].
    apply StackCompleteWord_spec in Hcomplete as [Hlen [result Hrun]].
    exists ops. split; [exact Hlen |].
    unfold StackWordOutput in Hout. rewrite Hrun in Hout. subst result. exact Hrun.
Qed.

#[export] Instance finite_stack_outputs n : Finite (StackOutput n).
Proof.
  refine {| enum := nodup (list_eq_dec Z.eq_dec) (StackOutputEnumeration n) |}.
  - intros output. rewrite nodup_In. apply StackOutputEnumeration_spec.
  - apply NoDup_nodup.
Defined.

Definition StackSequenceCount (n value : Z) : Prop :=
  value = SumLib.Sum.sum (StackOutput n) (fun _ => 1).

Lemma nodup_mapped_injective {A B} (f : A -> B) xs :
  NoDup (map f xs) -> forall x y,
    In x xs -> In y xs -> f x = f y -> x = y.
Proof.
  induction xs as [|a xs IH]; simpl; intros Hnd x y Hx Hy He; [contradiction |].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  destruct Hx as [<- | Hx], Hy as [<- | Hy]; [reflexivity | | |].
  - exfalso. apply Hnot. rewrite He. apply in_map. exact Hy.
  - exfalso. apply Hnot. rewrite <- He. apply in_map. exact Hx.
  - eapply IH; eauto.
Qed.

(** A checked bijection over the entire documented verification domain.
    Computation establishes totality, enumeration equality and injectivity
    for all legal words, rather than comparing only eight numeric answers. *)
Lemma stack_output_bijection_data n :
  0 <= n <= 7 ->
  Forall (fun ops => StackCompleteWord n ops = true) (StackSequenceSet n) /\
  StackOutputEnumeration n = map (StackWordOutput n) (StackSequenceSet n) /\
  NoDup (map (StackWordOutput n) (StackSequenceSet n)).
Proof.
  intros Hn.
  destruct (bounded_0_7_cases__cell_dp n Hn) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  split.
  all: try (rewrite Forall_forall; apply (proj1 (forallb_forall _ _)); vm_compute; reflexivity).
  all: split; [vm_compute; reflexivity |].
  all: match goal with |- NoDup ?outputs =>
    assert (Hcheck : (if @AUXLib.ListLib.NoDup_dec (list Z) outputs (list_eq_dec Z.eq_dec) then true else false) = true)
      by (vm_compute; reflexivity);
    destruct (@AUXLib.ListLib.NoDup_dec (list Z) outputs (list_eq_dec Z.eq_dec)) as [Hyes | Hno];
      [exact Hyes | discriminate]
  end.
Qed.

Lemma stack_operations_outputs_bijection n :
  0 <= n <= 7 ->
  (forall ops, LegalStackBehavior n ops ->
    exists output, StackValueExecution n ops = Some ([], [], output)) /\
  (forall output, StackOutput n output ->
    exists ops, LegalStackBehavior n ops /\ StackWordOutput n ops = output) /\
  (forall first second, LegalStackBehavior n first -> LegalStackBehavior n second ->
    StackWordOutput n first = StackWordOutput n second -> first = second).
Proof.
  intros Hn. destruct (stack_output_bijection_data n Hn) as [Htotal [Henum Hnd]].
  split.
  - intros ops Hlegal. apply (proj2 (StackSequenceSet_spec n ops ltac:(lia))) in Hlegal.
    rewrite Forall_forall in Htotal. specialize (Htotal ops Hlegal).
    apply StackCompleteWord_spec in Htotal. tauto.
  - split.
    + intros output Hout. apply StackOutputEnumeration_spec in Hout. rewrite Henum in Hout.
      apply in_map_iff in Hout as [ops [He Hin]]. exists ops. split; [|exact He].
      apply (proj1 (StackSequenceSet_spec n ops ltac:(lia))). exact Hin.
    + intros first second Hfirst Hsecond He.
      eapply nodup_mapped_injective; [exact Hnd | | | exact He];
      apply (proj2 (StackSequenceSet_spec n _ ltac:(lia))); assumption.
Qed.

Lemma StackOperationWordCount_to_output n value :
  0 <= n <= 7 -> StackOperationWordCount n value -> StackSequenceCount n value.
Proof.
  intros Hn Hcount.
  destruct (stack_output_bijection_data n Hn) as [_ [Henum Hnd]].
  unfold StackOperationWordCount in Hcount. unfold StackSequenceCount, SumLib.Sum.sum.
  change (value = fold_right (fun (_ : list Z) acc => 1 + acc) 0
    (nodup (list_eq_dec Z.eq_dec) (StackOutputEnumeration n))).
  rewrite Henum, nodup_fixed_point by exact Hnd.
  assert (Hlength : Zlength (map (StackWordOutput n) (StackSequenceSet n)) =
    Zlength (StackSequenceSet n)) by (rewrite !Zlength_correct, map_length; reflexivity).
  rewrite <- Hlength in Hcount.
  rewrite Hcount. clear Hcount Hn Henum Hnd Hlength.
  induction (map (StackWordOutput n) (StackSequenceSet n)) as [| output outputs IH]; [reflexivity |].
  change (Zlength (output :: outputs) =
    1 + fold_right (fun (_ : list Z) acc => 1 + acc) 0 outputs).
  rewrite Zlength_cons, IH. lia.
Qed.
