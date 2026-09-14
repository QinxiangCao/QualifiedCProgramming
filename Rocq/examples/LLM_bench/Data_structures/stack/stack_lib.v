Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

(**
  [sll] is the abstract, singly-linked-list-shaped sequence used to describe
  stack contents.  It is deliberately independent of the concrete memory
  representation: this case stores the sequence in a contiguous C array.
  The head of an [sll] is the logical top of the stack.
 *)
Definition sll : Type := list Z.

Definition sll_empty : sll := [].

Definition sll_cons (x : Z) (contents : sll) : sll :=
  x :: contents.

Definition sll_from_array (concrete : list Z) : sll :=
  rev concrete.

Definition stack_capacity : Z := 100000.

(**
  Physical array index 0 is the bottom of the stack, so the concrete array is
  the reverse of the abstract [sll].  Keeping the size in the relation makes
  every public stack state carry the capacity and exact-length invariants.
 *)
Definition stack_representation
    (contents : sll) (concrete : list Z) (size : Z) : Prop :=
  0 <= size /\
  size <= stack_capacity /\
  Zlength contents = size /\
  Zlength concrete = size /\
  concrete = rev contents.

Definition store_stack
    (p : Z) (contents : sll) (size : Z) : Assertion :=
  EX concrete : list Z,
    “ stack_representation contents concrete size ” &&
    IntArray.full p size concrete.

(**
  Mathematical state shared by the incremental [build] annotations.  The C
  invariant owns the loop bounds and the array resources; this predicate owns
  only the abstract meaning of the already processed input prefix.
 *)
Definition BuildStackPrefix
    (contents : sll) (input : list Z) (processed : Z) : Prop :=
  contents = sll_from_array (sublist 0 processed input).

(**
  Body-facing view of the frozen public representation relation.  Keeping a
  separate internal root preserves the frozen [store_stack] dependency
  surface while allowing QCP assertions to open its concrete array facts.
 *)
Definition StackConcreteView
    (contents : sll) (concrete : list Z) (size : Z) : Prop :=
  stack_representation contents concrete size.

Lemma stack_representation_push__push_state :
  forall (before : sll) (concrete : list Z) (n x : Z),
    stack_representation before concrete n ->
    n < stack_capacity ->
    stack_representation
      (sll_cons x before) (concrete ++ [x]) (n + 1).
Proof.
  intros before concrete n x Hrep Hcapacity.
  unfold stack_representation in Hrep |- *.
  destruct Hrep as
      (Hnonnegative & Hbound & Habstract_length & Hconcrete_length & Hreverse).
  unfold sll_cons.
  repeat split.
  - lia.
  - lia.
  - rewrite Zlength_cons.
    lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - rewrite Hreverse.
    reflexivity.
Qed.
Lemma stack_representation_pop__pop_state :
  forall top rest concrete size,
    1 <= size ->
    stack_representation (sll_cons top rest) concrete size ->
    concrete = rev rest ++ [top] /\
    Zlength (rev rest) = size - 1 /\
    stack_representation rest (rev rest) (size - 1) /\
    Znth (size - 1) concrete 0 = top.
Proof.
  intros top rest concrete size Hpositive Hrepresentation.
  unfold stack_representation in Hrepresentation.
  unfold sll_cons in Hrepresentation.
  destruct Hrepresentation as
    [Hnonnegative
      [Hcapacity
        [Hcontents_length [Hconcrete_length Hconcrete]]]].
  assert (Hrest_length : Zlength rest = size - 1).
  {
    rewrite Zlength_cons in Hcontents_length.
    lia.
  }
  assert (Hrev_rest_length : Zlength (rev rest) = size - 1).
  {
    rewrite Zlength_correct, length_rev, <- Zlength_correct.
    exact Hrest_length.
  }
  assert (Hconcrete_pop : concrete = rev rest ++ [top]).
  {
    rewrite Hconcrete.
    simpl.
    reflexivity.
  }
  split.
  - exact Hconcrete_pop.
  - split.
    + exact Hrev_rest_length.
    + split.
      * unfold stack_representation.
        repeat split.
        -- lia.
        -- lia.
        -- exact Hrest_length.
        -- exact Hrev_rest_length.
      * rewrite Hconcrete_pop.
        rewrite app_Znth2 by lia.
        replace (size - 1 - Zlength (rev rest)) with 0 by lia.
        apply Znth0_cons.
Qed.
Lemma stack_representation_prefix__build_loop :
  forall (input : list Z) (k : Z),
    0 <= k <= Zlength input ->
    k <= stack_capacity ->
    stack_representation
      (sll_from_array (sublist 0 k input)) (sublist 0 k input) k.
Proof.
  intros input k Hrange Hcapacity.
  unfold stack_representation, sll_from_array.
  repeat split; try lia.
  - rewrite Zlength_correct, length_rev, <- Zlength_correct.
    rewrite Zlength_sublist by lia.
    lia.
  - rewrite Zlength_sublist by lia.
    lia.
  - rewrite rev_involutive.
    reflexivity.
Qed.
Lemma build_stack_prefix_succ__build_loop :
  forall (prefix : sll) (input : list Z) (i x : Z),
    0 <= i < Zlength input ->
    BuildStackPrefix prefix input i ->
    x = Znth i input 0 ->
    BuildStackPrefix (sll_cons x prefix) input (i + 1).
Proof.
  intros prefix input i x Hrange Hprefix Hx.
  unfold BuildStackPrefix, sll_cons, sll_from_array in *.
  subst prefix x.
  rewrite (sublist_split 0 (i + 1) i input) by lia.
  rewrite (sublist_single 0 i input) by lia.
  rewrite rev_app_distr.
  reflexivity.
Qed.
Lemma build_stack_prefix_complete__build_completion :
  forall prefix input processed size,
    processed >= size ->
    processed <= size ->
    Zlength input = size ->
    BuildStackPrefix prefix input processed ->
    processed = size /\ prefix = sll_from_array input.
Proof.
  intros prefix input processed size Hge Hle Hlength Hprefix.
  assert (Hprocessed : processed = size) by lia.
  subst processed.
  split.
  - reflexivity.
  - unfold BuildStackPrefix in Hprefix.
    rewrite sublist_self in Hprefix by lia.
    exact Hprefix.
Qed.
