Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.ClassicalDescription.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

(**
  A reusable multiset has exactly one piece of data: an arbitrary list
  representative.  Two representatives denote the same bag precisely when
  they are permutations.  In particular, no array layout or heap-order proof
  is stored in [multiset].
 *)

Record multiset (A : Type) : Type := {
  mlist : list A
}.

Arguments mlist {A} _.

Definition list_to_multiset {A} (l : list A) : multiset A :=
  {| mlist := l |}.

Definition multiset_empty {A} : multiset A :=
  list_to_multiset [].

Definition multiset_size {A} (S : multiset A) : Z :=
  Zlength (mlist S).

Definition multiset_equiv {A} (S1 S2 : multiset A) : Prop :=
  Permutation (mlist S1) (mlist S2).

Definition multiset_insert {A}
    (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (x :: mlist S).

Definition multiset_union {A}
    (S1 S2 : multiset A) : multiset A :=
  list_to_multiset (mlist S1 ++ mlist S2).

Definition multiset_map {A B}
    (f : A -> B) (S : multiset A) : multiset B :=
  list_to_multiset (map f (mlist S)).

Definition multiset_member_by {A}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (S : multiset A) (x : A) : bool :=
  existsb (fun y => if eq_dec x y then true else false)
    (mlist S).

Definition multiset_count_by {A}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (S : multiset A) (x : A) : nat :=
  count_occ eq_dec (mlist S) x.

(**
  Removal is total.  Its public specification below uses [In x (mlist S)] as
  the successful-removal guard directly: exactly one occurrence is removed
  when present, while an absent element leaves the multiset unchanged.
 *)
Definition multiset_remove {A}
    (S : multiset A) (x : A) : multiset A :=
  let fix remove_one (l : list A) : list A :=
    match l with
    | [] => []
    | y :: ys =>
        if excluded_middle_informative (x = y)
        then ys
        else y :: remove_one ys
    end
  in list_to_multiset (remove_one (mlist S)).

Lemma mlist_list_to_multiset :
  forall A (l : list A),
    mlist (list_to_multiset l) = l.
Proof.
  reflexivity.
Qed.

Lemma list_to_multiset_mlist :
  forall A (S : multiset A),
    list_to_multiset (mlist S) = S.
Proof.
  intros A [l]. reflexivity.
Qed.

Lemma multiset_size_from_list :
  forall A (l : list A),
    multiset_size (list_to_multiset l) = Zlength l.
Proof.
  reflexivity.
Qed.

Lemma multiset_size_empty :
  forall A,
    multiset_size (@multiset_empty A) = 0.
Proof.
  reflexivity.
Qed.

Lemma multiset_insert_mlist :
  forall A (S : multiset A) x,
    mlist (multiset_insert S x) =
    x :: mlist S.
Proof.
  reflexivity.
Qed.

Lemma multiset_insert_size :
  forall A (S : multiset A) x,
    multiset_size (multiset_insert S x) =
    multiset_size S + 1.
Proof.
  intros. unfold multiset_size, multiset_insert. simpl.
  rewrite Zlength_cons. lia.
Qed.

Lemma multiset_insert_member :
  forall A (S : multiset A) x,
    In x (mlist (multiset_insert S x)).
Proof.
  intros. simpl. now left.
Qed.

Lemma multiset_insert_contents :
  forall A (S : multiset A) x,
    Permutation
      (mlist (multiset_insert S x))
      (x :: mlist S).
Proof.
  intros. apply Permutation_refl.
Qed.

Lemma multiset_union_mlist :
  forall A (S1 S2 : multiset A),
    mlist (multiset_union S1 S2) =
    mlist S1 ++ mlist S2.
Proof.
  reflexivity.
Qed.

Lemma multiset_union_size :
  forall A (S1 S2 : multiset A),
    multiset_size (multiset_union S1 S2) =
    multiset_size S1 + multiset_size S2.
Proof.
  intros. unfold multiset_size, multiset_union. simpl.
  rewrite Zlength_app. lia.
Qed.

#[export] Instance multiset_equiv_Equivalence (A : Type) :
  Equivalence (@multiset_equiv A).
Proof.
  split.
  - intros S. apply Permutation_refl.
  - intros S1 S2 H. now apply Permutation_sym.
  - intros S1 S2 S3 H12 H23.
    eapply Permutation_trans; eauto.
Qed.

Lemma multiset_equiv_size :
  forall A (S1 S2 : multiset A),
    multiset_equiv S1 S2 ->
    multiset_size S1 = multiset_size S2.
Proof.
  intros A S1 S2 Hperm.
  unfold multiset_equiv, multiset_size in *.
  pose proof (Permutation_length Hperm) as Hlen.
  now rewrite !Zlength_correct, Hlen.
Qed.

Lemma multiset_equiv_insert :
  forall A (S1 S2 : multiset A) x,
    multiset_equiv S1 S2 ->
    multiset_equiv
      (multiset_insert S1 x)
      (multiset_insert S2 x).
Proof.
  intros A S1 S2 x Hperm.
  unfold multiset_equiv, multiset_insert in *. simpl.
  now apply perm_skip.
Qed.

Lemma multiset_equiv_union :
  forall A (S1 S1' S2 S2' : multiset A),
    multiset_equiv S1 S1' ->
    multiset_equiv S2 S2' ->
    multiset_equiv
      (multiset_union S1 S2)
      (multiset_union S1' S2').
Proof.
  intros A S1 S1' S2 S2' H1 H2.
  unfold multiset_equiv, multiset_union in *. simpl.
  now apply Permutation_app.
Qed.

Lemma multiset_union_comm :
  forall A (S1 S2 : multiset A),
    multiset_equiv
      (multiset_union S1 S2)
      (multiset_union S2 S1).
Proof.
  intros A S1 S2.
  unfold multiset_equiv, multiset_union. simpl.
  apply Permutation_app_comm.
Qed.

Lemma multiset_union_assoc :
  forall A (S1 S2 S3 : multiset A),
    multiset_equiv
      (multiset_union (multiset_union S1 S2) S3)
      (multiset_union S1 (multiset_union S2 S3)).
Proof.
  intros A S1 S2 S3.
  unfold multiset_equiv, multiset_union. simpl.
  rewrite app_assoc. apply Permutation_refl.
Qed.

Lemma multiset_equiv_in :
  forall A (S1 S2 : multiset A) x,
    multiset_equiv S1 S2 ->
    (In x (mlist S1) <->
     In x (mlist S2)).
Proof.
  intros A S1 S2 x Hperm. split; intro Hin.
  - eapply Permutation_in; eauto.
  - eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin].
Qed.

Lemma multiset_remove_spec :
  forall {A} (S : multiset A) x,
    (In x (mlist S) ->
      multiset_size (multiset_remove S x) =
        multiset_size S - 1 /\
      Permutation
        (mlist S)
        (x :: mlist (multiset_remove S x))) /\
    (~ In x (mlist S) ->
      multiset_remove S x = S).
Proof.
  intros A [l] x.
  unfold multiset_remove, multiset_size.
  simpl.
  induction l as [|y ys IH].
  - split.
    + contradiction.
    + intros _. reflexivity.
  - destruct (excluded_middle_informative (x = y))
      as [Heq | Hneq].
    + subst y.
      split.
      * intros _. split.
        -- rewrite Zlength_cons. lia.
        -- apply Permutation_refl.
      * intro Hnotin.
        exfalso. apply Hnotin. now left.
    + destruct IH as [IHpresent IHabsent].
      split.
      * intro Hin.
        destruct Hin as [Heq | Hin].
        -- exfalso. apply Hneq. symmetry. exact Heq.
        -- destruct (IHpresent Hin) as [Hsize Hpermutation].
           split.
           ++ rewrite !Zlength_cons, Hsize. lia.
           ++ eapply Permutation_trans.
              ** apply perm_skip. exact Hpermutation.
              ** apply perm_swap.
      * intro Hnotin.
        assert (Hnotin_tail : ~ In x ys).
        {
          intro Hin. apply Hnotin. now right.
        }
        injection (IHabsent Hnotin_tail) as Htail.
        now rewrite Htail.
Qed.

(** Deterministic maximum for nonempty integer multisets. *)

Definition multiset_max (S : multiset Z) : Z :=
  match mlist S with
  | [] => 0
  | x :: xs => fold_right Z.max x xs
  end.

Definition multiset_maximum
    (S : multiset Z) (value : Z) : Prop :=
  In value (mlist S) /\
  forall x,
    In x (mlist S) ->
    x <= value.

Lemma fold_right_Zmax_member :
  forall xs base,
    In (fold_right Z.max base xs) (base :: xs).
Proof.
  induction xs as [|x xs IH]; intro base.
  - simpl. now left.
  - simpl.
    destruct (Z_le_gt_dec x (fold_right Z.max base xs)) as [Hle | Hgt].
    + rewrite Z.max_r by exact Hle.
      specialize (IH base).
      simpl. destruct IH as [IH | IH].
      * now left.
      * right. now right.
    + rewrite Z.max_l by lia.
      simpl. now right; left.
Qed.

Lemma fold_right_Zmax_upper_bound :
  forall xs base value,
    In value (base :: xs) ->
    value <= fold_right Z.max base xs.
Proof.
  induction xs as [|x xs IH]; intros base value Hin.
  - simpl in *. destruct Hin as [-> | []]. lia.
  - simpl in *.
    destruct Hin as [-> | [-> | Hin]].
    + eapply Z.le_trans.
      * apply IH. now left.
      * apply Z.le_max_r.
    + apply Z.le_max_l.
    + eapply Z.le_trans.
      * apply IH. now right.
      * apply Z.le_max_r.
Qed.

Lemma multiset_max_is_maximum :
  forall S,
    mlist S <> [] ->
    multiset_maximum S (multiset_max S).
Proof.
  intros S Hnonempty.
  unfold multiset_max, multiset_maximum.
  destruct (mlist S) as [|x xs] eqn:Hlist.
  - contradiction.
  - split.
    + apply fold_right_Zmax_member.
    + intros value Hin.
      now apply fold_right_Zmax_upper_bound.
Qed.

Lemma multiset_max_member :
  forall S,
    mlist S <> [] ->
    In (multiset_max S) (mlist S).
Proof.
  intros S Hnonempty.
  now destruct (multiset_max_is_maximum S Hnonempty).
Qed.

Lemma multiset_max_upper_bound :
  forall S value,
    mlist S <> [] ->
    In value (mlist S) ->
    value <= multiset_max S.
Proof.
  intros S value Hnonempty Hin.
  destruct (multiset_max_is_maximum S Hnonempty) as [_ Hbound].
  now apply Hbound.
Qed.

Lemma multiset_max_equiv :
  forall S1 S2,
    multiset_equiv S1 S2 ->
    mlist S1 <> [] ->
    multiset_max S1 = multiset_max S2.
Proof.
  intros S1 S2 Hperm Hnonempty1.
  assert (Hmax1in : In (multiset_max S1) (mlist S1)).
  { now apply multiset_max_member. }
  assert (Hmax1in2 : In (multiset_max S1) (mlist S2)).
  { eapply Permutation_in; eauto. }
  assert (Hnonempty2 : mlist S2 <> []).
  { intro Hnil. rewrite Hnil in Hmax1in2. contradiction. }
  assert (Hmax2in2 : In (multiset_max S2) (mlist S2)).
  { now apply multiset_max_member. }
  assert (Hmax2in1 : In (multiset_max S2) (mlist S1)).
  {
    eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hmax2in2.
  }
  pose proof
    (multiset_max_upper_bound S2 (multiset_max S1)
      Hnonempty2 Hmax1in2) as H12.
  pose proof
    (multiset_max_upper_bound S1 (multiset_max S2)
      Hnonempty1 Hmax2in1) as H21.
  lia.
Qed.

Lemma multiset_remove_max_size :
  forall S,
    mlist S <> [] ->
    multiset_size (multiset_remove S (multiset_max S)) =
    multiset_size S - 1.
Proof.
  intros S Hnonempty.
  destruct
    (multiset_remove_spec S (multiset_max S))
    as [Hpresent _].
  apply Hpresent.
  now apply multiset_max_member.
Qed.

(**
  Priority-queue representation.  [heap_relation] is the constructive bridge:
  its [Permutation] proof relates the reusable multiset representative to the
  actual heap-array order.  Heap order belongs here, outside [multiset].
 *)

Definition heap_capacity : Z := 100000.

Definition heap_parent (child : Z) : Z :=
  Z.quot (child - 1) 2.

Definition heap_left_child (index : Z) : Z :=
  index * 2 + 1.

Definition heap_right_child (index : Z) : Z :=
  index * 2 + 2.

Definition heap_selected_child
    (concrete : list Z) (size index : Z) : Z :=
  let left := heap_left_child index in
  let right := heap_right_child index in
  match Z_lt_dec right size with
  | left _ =>
      match
        Z_lt_dec
          (Znth left concrete 0)
          (Znth right concrete 0)
      with
      | left _ => right
      | right _ => left
      end
  | right _ => left
  end.

Definition heap_ordered (concrete : list Z) (size : Z) : Prop :=
  forall child,
    0 < child /\ child < size ->
    Znth (heap_parent child) concrete 0 >= Znth child concrete 0.

Definition heap_relation
    (S : multiset Z) (concrete : list Z) : Prop :=
  Permutation (mlist S) concrete.

Definition heap_representation
    (S : multiset Z) (concrete : list Z) (size : Z) : Prop :=
  0 <= size /\
  size <= heap_capacity /\
  multiset_size S = size /\
  Zlength concrete = size /\
  heap_relation S concrete /\
  heap_ordered concrete size.

Definition store_heap
    (p : Z) (S : multiset Z) (size : Z) : Assertion :=
  EX concrete : list Z,
    “ heap_representation S concrete size ” &&
    IntArray.full p size concrete.

Definition heap_spare (p size : Z) : Assertion :=
  IntArray.undef_seg p size (size + 1).

Definition heap_retired_cell (p index value : Z) : Assertion :=
  IntArray.seg p index (index + 1) [value].

Lemma heap_relation_size :
  forall S concrete,
    heap_relation S concrete ->
    multiset_size S = Zlength concrete.
Proof.
  intros S concrete Hperm.
  unfold heap_relation, multiset_size in *.
  pose proof (Permutation_length Hperm) as Hlen.
  now rewrite !Zlength_correct, Hlen.
Qed.

Lemma heap_representation_relation :
  forall S concrete size,
    heap_representation S concrete size ->
    heap_relation S concrete.
Proof.
  intros S concrete size [_ [_ [_ [_ [H _]]]]].
  exact H.
Qed.

Lemma heap_representation_ordered :
  forall S concrete size,
    heap_representation S concrete size ->
    heap_ordered concrete size.
Proof.
  intros S concrete size [_ [_ [_ [_ [_ H]]]]].
  exact H.
Qed.

(**
  Annotation-facing predicates describe the mathematical partial heap facts
  maintained by sift-up, incremental build, and sift-down.  They are relations,
  not executable copies of the C loops.
 *)

Definition PrefixMaximum
    (concrete : list Z) (size value : Z) : Prop :=
  0 < size /\
  size <= Zlength concrete /\
  Znth 0 concrete 0 = value /\
  forall i,
    0 <= i /\ i < size ->
    Znth i concrete 0 <= value.

Definition HeapOrderExceptUp
    (concrete : list Z) (size child : Z) : Prop :=
  0 <= child /\
  child < size /\
  forall node,
    0 < node /\ node < size /\ node <> child ->
    Znth (heap_parent node) concrete 0 >= Znth node concrete 0.

Definition PushHoleChildrenPreserved
    (concrete : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node /\ node < size /\ heap_parent node = child ->
    Znth (heap_parent child) concrete 0 >= Znth node concrete 0.

Definition PushSource
    (written : list Z) (before : multiset Z) (size x : Z) : Prop :=
  Zlength written = size + 1 /\
  Permutation written (x :: mlist before) /\
  heap_ordered (sublist 0 size written) size.

Definition PushLoopState
    (written current : list Z) (size child x : Z) : Prop :=
  0 <= size /\
  Zlength written = size + 1 /\
  Zlength current = size + 1 /\
  0 <= child /\
  child <= size /\
  Znth child current 0 = x /\
  Permutation written current /\
  HeapOrderExceptUp current (size + 1) child /\
  PushHoleChildrenPreserved current (size + 1) child.

Definition PushResult
    (before : multiset Z) (result : list Z) (size x : Z) : Prop :=
  0 <= size /\
  Zlength result = size + 1 /\
  Permutation result (x :: mlist before) /\
  heap_ordered result (size + 1).

Definition BuildPrefixState
    (prefix : multiset Z) (input : list Z) (processed : Z) : Prop :=
  1 <= processed /\
  processed <= Zlength input /\
  multiset_equiv
    prefix
    (list_to_multiset (sublist 0 processed input)).

Definition HeapOrderExceptDown
    (concrete : list Z) (size index : Z) : Prop :=
  0 <= index /\
  index < size /\
  forall child,
    0 < child /\ child < size /\ heap_parent child <> index ->
    Znth (heap_parent child) concrete 0 >= Znth child concrete 0.

Definition PopHoleParentDominatesChildren
    (current : list Z) (size index : Z) : Prop :=
  index = 0 \/
  forall child,
    0 < child /\ child < size /\ heap_parent child = index ->
    Znth (heap_parent index) current 0 >= Znth child current 0.

Definition PopSelectedChild
    (current : list Z) (size index selected : Z) : Prop :=
  0 <= index /\
  index < size /\
  index < selected /\
  0 <= selected /\
  selected < size /\
  heap_parent selected = index /\
  selected = heap_selected_child current size index /\
  forall child,
    0 < child /\ child < size /\ heap_parent child = index ->
    Znth selected current 0 >= Znth child current 0.

Definition PopRemainingElements
    (before current : list Z) (size : Z) : Prop :=
  1 <= size /\
  size <= Zlength before /\
  size <= Zlength current /\
  Permutation
    (sublist 0 (size - 1) current)
    (sublist 1 size before).

Definition PopLoopState
    (before current : list Z) (size index : Z) : Prop :=
  1 < size /\
  Zlength before = size /\
  Zlength current = size /\
  0 <= index /\
  index < size - 1 /\
  heap_ordered before size /\
  Znth index current 0 = Znth (size - 1) before 0 /\
  Znth (size - 1) current 0 = Znth (size - 1) before 0 /\
  PopRemainingElements before current size /\
  HeapOrderExceptDown current (size - 1) index /\
  PopHoleParentDominatesChildren current (size - 1) index.

Definition PopReadyState
    (before current : list Z) (size result : Z) : Prop :=
  1 < size /\
  Zlength before = size /\
  Zlength current = size /\
  heap_ordered before size /\
  PrefixMaximum before size result /\
  Znth (size - 1) current 0 = Znth (size - 1) before 0 /\
  PopRemainingElements before current size /\
  heap_ordered current (size - 1).

Definition PopResult
    (S : multiset Z) (before result : list Z)
    (size value : Z) : Prop :=
  1 <= size /\
  Zlength before = size /\
  Zlength result = size /\
  value = multiset_max S /\
  heap_ordered (sublist 0 (size - 1) result) (size - 1) /\
  Permutation
    (sublist 0 (size - 1) result)
    (mlist (multiset_remove S value)).

(**
  [HeapSortState] is the mathematical state of the in-place heap-sort
  extraction loop.  The still-active priority queue and the retired suffix
  together are a permutation of the original input.  The suffix is already
  nondecreasing, and every active value belongs to the left of every retired
  value in the final ordering.

  This relation deliberately does not describe how [build] or [pop] execute;
  any max-priority-queue implementation satisfying their public contracts can
  be used to establish and preserve it.
 *)
Definition HeapSortState
    (input : list Z) (active : multiset Z) (suffix : list Z) : Prop :=
  Permutation input (mlist active ++ suffix) /\
  increasing suffix /\
  forall active_value suffix_value,
    In active_value (mlist active) ->
    In suffix_value suffix ->
    active_value <= suffix_value.

Lemma push_appended_source__push_initialization :
  forall (S : multiset Z) (base : list Z) (size x : Z),
    heap_representation S base size ->
    PushSource (base ++ [x]) S size x.
Proof.
  intros S base size x Hrep.
  destruct Hrep as
    [Hsize_nonneg
      [Hcapacity
        [Hmultiset_size
          [Hbase_length [Hrelation Hordered]]]]].
  unfold PushSource.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - split.
    + eapply Permutation_trans.
      * apply Permutation_app.
        -- apply Permutation_sym.
           exact Hrelation.
        -- apply Permutation_refl.
      * exact (Permutation_app_comm (mlist S) [x]).
    + replace (sublist 0 size (base ++ [x])) with base.
      * exact Hordered.
      * rewrite <- Hbase_length at 1.
        symmetry.
        apply sublist_app_exact1.
Qed.
Lemma push_appended_loop_state__push_initialization :
  forall (S : multiset Z) (base : list Z) (size x : Z),
    heap_representation S base size ->
    PushLoopState (base ++ [x]) (base ++ [x]) size size x.
Proof.
  intros S base size x Hrep.
  destruct Hrep as
    [Hsize_nonneg
      [Hcapacity
        [Hmultiset_size
          [Hbase_length [Hrelation Hordered]]]]].
  unfold PushLoopState.
  split; [exact Hsize_nonneg |].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + split; [exact Hsize_nonneg |].
      split; [lia |].
      split.
      * rewrite app_Znth2 by lia.
        rewrite Hbase_length.
        replace (size - size) with 0 by lia.
        reflexivity.
      * split.
        -- apply Permutation_refl.
        -- split.
           ++ unfold HeapOrderExceptUp.
              split; [exact Hsize_nonneg |].
              split; [lia |].
              intros node [Hnode_positive [Hnode_bound Hnode_not_hole]].
              assert (Hnode_lt_size : node < size) by lia.
              assert (Hparent_nonneg : 0 <= heap_parent node).
              {
                unfold heap_parent.
                apply Z.quot_pos; lia.
              }
              assert (Hparent_lt_node : heap_parent node < node).
              {
                unfold heap_parent.
                apply Z.quot_lt_upper_bound; lia.
              }
              rewrite app_Znth1 by (rewrite Hbase_length; lia).
              rewrite app_Znth1 by (rewrite Hbase_length; lia).
              apply Hordered.
              lia.
           ++ unfold PushHoleChildrenPreserved.
              intros node [Hnode_positive [Hnode_bound Hparent_is_hole]].
              assert (Hparent_lt_node : heap_parent node < node).
              {
                unfold heap_parent.
                apply Z.quot_lt_upper_bound; lia.
              }
              lia.
Qed.
Lemma heap_parent_positive_bounds__push_sift_up :
  forall child size,
    0 < child ->
    child <= size ->
    0 <= heap_parent child /\
    heap_parent child < child /\
    heap_parent child <= size.
Proof.
  intros child size Hchild Hbound.
  unfold heap_parent.
  split.
  - apply Z.quot_pos; lia.
  - split.
    + apply Z.quot_lt_upper_bound; lia.
    + apply Z.quot_le_upper_bound; lia.
Qed.
Lemma push_break_establishes_result__push_sift_up :
  forall before written current size child parent x,
    PushSource written before size x ->
    PushLoopState written current size child x ->
    parent = heap_parent child ->
    Znth parent current 0 >= Znth child current 0 ->
    PushResult before current size x.
Proof.
  intros before written current size child parent x
    Hsource Hloop Hparent Hdominates.
  unfold PushSource in Hsource.
  destruct Hsource as [Hwritten_len [Hsource_perm Hwritten_order]].
  unfold PushLoopState in Hloop.
  destruct Hloop as
    [Hsize [Hwritten_len' [Hcurrent_len
      [Hchild_nonneg [Hchild_bound [Hchild_value
        [Hwritten_current [Hexcept Hchildren]]]]]]]].
  unfold HeapOrderExceptUp in Hexcept.
  destruct Hexcept as [_ [_ Hexcept]].
  unfold PushResult.
  repeat split.
  - exact Hsize.
  - exact Hcurrent_len.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hwritten_current.
    + exact Hsource_perm.
  - unfold heap_ordered.
    intros node Hnode.
    destruct (Z.eq_dec node child) as [Heq | Hneq].
    + subst node. rewrite <- Hparent. exact Hdominates.
    + apply Hexcept. lia.
Qed.
Lemma replace_Znth_swap_form__push_sift_up :
  forall (l1 l2 l3 : list Z) (xi xj : Z),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj
        (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xi :: l2 ++ xj :: l3) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := Z) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert
    (H0 :
      replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
      xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by (subst n2; lia).
  rewrite
    (replace_Znth_nothing (A := Z)
      (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace
    (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with
    (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := Z) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3)
    by reflexivity.
  rewrite H1.
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__push_sift_up :
  forall (l : list Z) i j (d : Z),
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d)
        (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hrange.
  destruct Hrange as [Hi [Hij Hj]].
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj; lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr : (nj < length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert
        (Hnat :
          (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat =
          Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm.
      rewrite Hnat.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3)
    by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_Znth_swap_form__push_sift_up.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.
Lemma replace_nth_comm_Z__push_sift_up :
  forall ni nj (l : list Z) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros ni nj l a b Hneq.
  revert nj l Hneq.
  induction ni; intros nj l Hneq; destruct l as [|x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal.
      apply IHni.
      intros Heq.
      apply Hneq.
      now f_equal.
Qed.
Lemma replace_Znth_comm__push_sift_up :
  forall (l : list Z) i j (a b : Z),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm_Z__push_sift_up.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.
Lemma permutation_swap_Znth__push_sift_up :
  forall (l : list Z) i j (d : Z),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d)
        (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_Znth_lt__push_sift_up.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm__push_sift_up by lia.
      apply permutation_swap_Znth_lt__push_sift_up.
      lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.
Lemma Znth_swap_Znth__push_sift_up :
  forall (l : list Z) i j (d : Z),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    i <> j ->
    let swapped :=
      replace_Znth j (Znth i l d)
        (replace_Znth i (Znth j l d) l) in
    Znth i swapped d = Znth j l d /\
    Znth j swapped d = Znth i l d /\
    (forall k,
      0 <= k < Zlength l ->
      k <> i ->
      k <> j ->
      Znth k swapped d = Znth k l d).
Proof.
  intros l i j d Hi Hj Hneq.
  simpl.
  split.
  - rewrite Znth_replace_Znth_Diff by
      (rewrite ?Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - split.
    + rewrite Znth_replace_Znth_Same by
        (rewrite Zlength_replace_Znth; lia).
      reflexivity.
    + intros k Hk Hki Hkj.
      rewrite Znth_replace_Znth_Diff by
        (rewrite ?Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      reflexivity.
Qed.
Lemma push_swap_advances_loop__push_sift_up :
  forall written current size child parent x,
    PushLoopState written current size child x ->
    0 < child ->
    parent = heap_parent child ->
    Znth parent current 0 < Znth child current 0 ->
    Znth child
      (replace_Znth child (Znth parent current 0)
        (replace_Znth parent (Znth child current 0) current)) 0 =
      Znth parent current 0 /\
    PushLoopState written
      (replace_Znth child (Znth parent current 0)
        (replace_Znth parent (Znth child current 0) current))
      size parent x.
Proof.
  intros written current size child parent x
    Hloop Hchild_pos Hparent Hstrict.
  unfold PushLoopState in Hloop.
  destruct Hloop as
    [Hsize [Hwritten_len [Hcurrent_len
      [Hchild_nonneg [Hchild_bound [Hchild_value
        [Hwritten_current [Hexcept Hchildren]]]]]]]].
  unfold HeapOrderExceptUp in Hexcept.
  destruct Hexcept as [_ [_ Hexcept]].
  unfold PushHoleChildrenPreserved in Hchildren.
  pose proof
    (heap_parent_positive_bounds__push_sift_up
      child size Hchild_pos Hchild_bound)
    as [Hparent_nonneg [Hparent_lt Hparent_bound]].
  rewrite <- Hparent in
    Hparent_nonneg, Hparent_lt, Hparent_bound.
  assert (Hparent_ne_child : parent <> child) by lia.
  assert (Hparent_range : 0 <= parent < Zlength current) by lia.
  assert (Hchild_range : 0 <= child < Zlength current) by lia.
  set
    (swapped :=
      replace_Znth child (Znth parent current 0)
        (replace_Znth parent (Znth child current 0) current)).
  pose proof
    (Znth_swap_Znth__push_sift_up
      current parent child 0
      Hparent_range Hchild_range Hparent_ne_child)
    as Hswap.
  fold swapped in Hswap.
  destruct Hswap as [Hswap_parent [Hswap_child Hswap_other]].
  assert (Hswapped_len : Zlength swapped = size + 1).
  {
    subst swapped.
    repeat rewrite Zlength_replace_Znth.
    exact Hcurrent_len.
  }
  assert (Hwritten_swapped : Permutation written swapped).
  {
    eapply Permutation_trans.
    - exact Hwritten_current.
    - subst swapped.
      apply permutation_swap_Znth__push_sift_up;
        assumption.
  }
  assert (Hnew_except : HeapOrderExceptUp swapped (size + 1) parent).
  {
    unfold HeapOrderExceptUp.
    split; [exact Hparent_nonneg |].
    split; [lia |].
    intros node [Hnode_pos [Hnode_lt Hnode_ne_parent]].
    pose proof
      (heap_parent_positive_bounds__push_sift_up
        node size Hnode_pos ltac:(lia))
      as [Hnode_parent_nonneg
        [Hnode_parent_lt Hnode_parent_bound]].
    assert
      (Hnode_range : 0 <= node < Zlength current) by lia.
    destruct (Z.eq_dec node child) as [Hnode_child | Hnode_ne_child].
    - subst node.
      rewrite <- Hparent.
      rewrite Hswap_parent, Hswap_child.
      lia.
    - assert
        (Hnode_same :
          Znth node swapped 0 = Znth node current 0).
      {
        apply Hswap_other; try assumption.
      }
      assert
        (Hold :
          Znth (heap_parent node) current 0 >=
          Znth node current 0).
      {
        apply Hexcept.
        repeat split; assumption.
      }
      destruct
        (Z.eq_dec (heap_parent node) parent)
        as [Hnode_parent_eq | Hnode_parent_ne].
      + rewrite Hnode_parent_eq, Hswap_parent, Hnode_same.
        rewrite Hnode_parent_eq in Hold.
        lia.
      + destruct
          (Z.eq_dec (heap_parent node) child)
          as [Hnode_parent_child | Hnode_parent_ne_child].
        * rewrite Hnode_parent_child, Hswap_child, Hnode_same.
          assert
            (Hpreserved :
              Znth (heap_parent child) current 0 >=
              Znth node current 0).
          {
            apply Hchildren.
            repeat split; assumption.
          }
          rewrite <- Hparent in Hpreserved.
          exact Hpreserved.
        * assert
            (Hnode_parent_same :
              Znth (heap_parent node) swapped 0 =
              Znth (heap_parent node) current 0).
          {
            apply Hswap_other; try assumption.
            lia.
          }
          rewrite Hnode_parent_same, Hnode_same.
          exact Hold.
  }
  assert
    (Hnew_children :
      PushHoleChildrenPreserved swapped (size + 1) parent).
  {
    unfold PushHoleChildrenPreserved.
    intros node [Hnode_pos [Hnode_lt Hnode_parent]].
    pose proof
      (heap_parent_positive_bounds__push_sift_up
        node size Hnode_pos ltac:(lia))
      as [Hnode_parent_nonneg
        [Hnode_parent_lt Hnode_parent_bound]].
    assert
      (Hnode_range : 0 <= node < Zlength current) by lia.
    destruct (Z.eq_dec parent 0) as [Hparent_zero | Hparent_positive].
    - rewrite Hparent_zero in Hswap_parent, Hswap_child, Hstrict.
      rewrite Hparent_zero.
      destruct (Z.eq_dec node child) as [Hnode_child | Hnode_ne_child].
      + rewrite Hnode_child.
        change (Znth 0 swapped 0 >= Znth child swapped 0).
        rewrite Hswap_parent, Hswap_child.
        lia.
      + assert (Hnode_ne_parent : node <> parent) by lia.
        assert
          (Hnode_same :
            Znth node swapped 0 = Znth node current 0).
        {
          apply Hswap_other; try assumption.
        }
        assert
          (Hold :
            Znth (heap_parent node) current 0 >=
            Znth node current 0).
        {
          apply Hexcept.
          repeat split; assumption.
        }
        rewrite Hnode_parent, Hparent_zero in Hold.
        change (Znth 0 swapped 0 >= Znth node swapped 0).
        rewrite Hswap_parent, Hnode_same.
        lia.
    - assert (Hparent_pos : 0 < parent) by lia.
      pose proof
        (heap_parent_positive_bounds__push_sift_up
          parent size Hparent_pos Hparent_bound)
        as [Hgrand_nonneg [Hgrand_lt Hgrand_bound]].
      assert
        (Hgrand_same :
          Znth (heap_parent parent) swapped 0 =
          Znth (heap_parent parent) current 0).
      {
        apply Hswap_other.
        - lia.
        - lia.
        - lia.
      }
      assert
        (Hparent_order :
          Znth (heap_parent parent) current 0 >=
          Znth parent current 0).
      {
        apply Hexcept.
        repeat split; try lia.
      }
      destruct (Z.eq_dec node child) as [Hnode_child | Hnode_ne_child].
      + subst node.
        rewrite Hgrand_same, Hswap_child.
        exact Hparent_order.
      + assert (Hnode_ne_parent : node <> parent) by lia.
        assert
          (Hnode_same :
            Znth node swapped 0 = Znth node current 0).
        {
          apply Hswap_other; try assumption.
        }
        assert
          (Hnode_order :
            Znth (heap_parent node) current 0 >=
            Znth node current 0).
        {
          apply Hexcept.
          repeat split; assumption.
        }
        rewrite Hnode_parent in Hnode_order.
        rewrite Hgrand_same, Hnode_same.
        lia.
  }
  split.
  - exact Hswap_child.
  - unfold PushLoopState.
    split; [exact Hsize |].
    split; [exact Hwritten_len |].
    split; [exact Hswapped_len |].
    split; [exact Hparent_nonneg |].
    split; [exact Hparent_bound |].
    split.
    + rewrite Hswap_parent.
      exact Hchild_value.
    + split; [exact Hwritten_swapped |].
      split; [exact Hnew_except | exact Hnew_children].
Qed.
Lemma push_zero_exit_result__push_finalization :
  forall before written current size x,
    PushSource written before size x ->
    PushLoopState written current size 0 x ->
    PushResult before current size x.
Proof.
  intros before written current size x Hsource Hloop.
  destruct Hsource as [Hwritten_length [Hwritten_perm _]].
  destruct Hloop as
    [Hsize
      [_
        [Hcurrent_length
          [_
            [_
              [_
                [Hwritten_current
                  [Hexcept _]]]]]]]].
  unfold PushResult.
  repeat split.
  - exact Hsize.
  - exact Hcurrent_length.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hwritten_current.
    + exact Hwritten_perm.
  - unfold HeapOrderExceptUp in Hexcept.
    destruct Hexcept as [_ [_ Hordered]].
    unfold heap_ordered.
    intros child [Hchild_positive Hchild_bound].
    apply Hordered.
    repeat split; lia.
Qed.
Lemma push_result_representation__push_finalization :
  forall before result size x,
    size < heap_capacity ->
    PushResult before result size x ->
    heap_representation
      (multiset_insert before x) result (size + 1).
Proof.
  intros before result size x Hcapacity Hresult.
  destruct Hresult as
    [Hsize [Hresult_length [Hresult_perm Hresult_ordered]]].
  unfold heap_representation.
  repeat split.
  - lia.
  - lia.
  - unfold multiset_size, multiset_insert. simpl.
    rewrite <- Hresult_length.
    rewrite !Zlength_correct.
    rewrite (Permutation_length Hresult_perm).
    reflexivity.
  - exact Hresult_length.
  - unfold heap_relation. simpl.
    apply Permutation_sym. exact Hresult_perm.
  - exact Hresult_ordered.
Qed.
Lemma build_initial_prefix__build_progress :
  forall (input : list Z) n,
    Zlength input = n ->
    1 <= n ->
    BuildPrefixState
      (list_to_multiset [Znth 0 input 0]) input 1 /\
    heap_representation
      (list_to_multiset [Znth 0 input 0])
      (sublist 0 1 input) 1.
Proof.
  intros input n Hlen Hpositive.
  assert (Hsingle :
    sublist 0 1 input = [Znth 0 input 0]).
  {
    apply (sublist_single 0 0 input).
    lia.
  }
  split.
  - unfold BuildPrefixState, multiset_equiv.
    repeat split; try lia.
    simpl.
    rewrite Hsingle.
    apply Permutation_refl.
  - unfold heap_representation.
    repeat split.
    + lia.
    + unfold heap_capacity; lia.
    + rewrite Hsingle.
      reflexivity.
    + unfold heap_relation.
      simpl.
      rewrite Hsingle.
      apply Permutation_refl.
    + unfold heap_ordered.
      intros child Hchild.
      lia.
Qed.
Lemma build_split_next_cell__build_progress :
  forall heap i n (input : list Z),
    0 <= i < n ->
    n <= Zlength input ->
    IntArray.seg heap i n (sublist i n input)
    |-- heap_spare heap i **
        IntArray.seg heap (i + 1) n (sublist (i + 1) n input).
Proof.
  intros heap i n input Hirange Hlen.
  unfold heap_spare.
  sep_apply
    (IntArray.seg_split_to_seg
      heap i (i + 1) n (sublist i n input));
    try lia.
  sep_apply
    (IntArray.seg_to_undef_seg
      heap i (i + 1)
      (sublist 0 (i + 1 - i) (sublist i n input))).
  replace
    (sublist (i + 1 - i) (n - i) (sublist i n input))
    with (sublist (i + 1) n input).
  2: {
    rewrite Zsublist_Zsublist by lia.
    f_equal; lia.
  }
  entailer!.
Qed.
Lemma build_prefix_extend__build_progress :
  forall (prefix : multiset Z) (input : list Z) i x,
    1 <= i ->
    i < Zlength input ->
    x = Znth i input 0 ->
    BuildPrefixState prefix input i ->
    BuildPrefixState (multiset_insert prefix x) input (i + 1).
Proof.
  intros prefix input i x Hi Hbound Hx Hprefix.
  unfold BuildPrefixState in *.
  destruct Hprefix as [Hone [Hprocessed Hperm]].
  repeat split; try lia.
  unfold multiset_equiv, multiset_insert in *.
  simpl in *.
  rewrite (sublist_split 0 (i + 1) i input) by lia.
  rewrite (sublist_single 0 i input) by lia.
  subst x.
  eapply Permutation_trans.
  - apply perm_skip.
    exact Hperm.
  - apply Permutation_cons_append.
Qed.
Lemma store_heap_equiv_transport__build_finalization :
  forall S1 S2 concrete size,
    multiset_equiv S1 S2 ->
    heap_representation S1 concrete size ->
    heap_representation S2 concrete size.
Proof.
  intros S1 S2 concrete size Hequiv Hrep.
  unfold heap_representation in *.
  destruct Hrep as
    [Hnonneg [Hcapacity [Hsize [Hlength [Hrelation Hordered]]]]].
  repeat split; try assumption.
  - pose proof
      (multiset_equiv_size Z S1 S2 Hequiv)
      as Hsize_equiv.
    lia.
  - unfold multiset_equiv in Hequiv.
    unfold heap_relation in *.
    eapply Permutation_trans.
    + apply Permutation_sym.
      exact Hequiv.
    + exact Hrelation.
Qed.
Lemma build_prefix_complete__build_finalization :
  forall prefix input processed,
    BuildPrefixState prefix input processed ->
    processed = Zlength input ->
    multiset_equiv prefix (list_to_multiset input).
Proof.
  intros prefix input processed Hprefix Hcomplete.
  subst processed.
  unfold BuildPrefixState in Hprefix.
  destruct Hprefix as [_ [_ Hprefix]].
  rewrite sublist_self in Hprefix by reflexivity.
  exact Hprefix.
Qed.
Lemma heap_ordered_root_upper_bound__pop_initialization :
  forall concrete size index,
    heap_ordered concrete size ->
    0 <= index < size ->
    Znth index concrete 0 <= Znth 0 concrete 0.
Proof.
  intros concrete size index Hordered Hindex.
  remember (Z.to_nat index) as n eqn:Hn.
  assert (Hindex_nat : index = Z.of_nat n).
  {
    subst n.
    symmetry.
    apply Z2Nat.id.
    lia.
  }
  subst index.
  clear Hn.
  revert Hindex.
  induction n as [n IH] using lt_wf_ind.
  intro Hindex.
  destruct n as [|n].
  - simpl. lia.
  - set (parent := heap_parent (Z.of_nat (S n))).
    assert (Hchild_pos : 0 < Z.of_nat (S n)) by lia.
    assert (Hparent_nonneg : 0 <= parent).
    {
      unfold parent, heap_parent.
      apply Z.quot_pos; lia.
    }
    assert (Hparent_lt : parent < Z.of_nat (S n)).
    {
      unfold parent, heap_parent.
      apply Z.quot_lt_upper_bound; lia.
    }
    assert (Hparent_nat_lt : (Z.to_nat parent < S n)%nat).
    {
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      lia.
    }
    specialize (IH (Z.to_nat parent) Hparent_nat_lt).
    assert (Hparent_range :
      0 <= Z.of_nat (Z.to_nat parent) < size).
    {
      rewrite Z2Nat.id by lia.
      lia.
    }
    specialize (IH Hparent_range).
    rewrite Z2Nat.id in IH by lia.
    pose proof
      (Hordered (Z.of_nat (S n))
        (conj Hchild_pos (proj2 Hindex))) as Hedge.
    fold parent in Hedge.
    apply Z.ge_le in Hedge.
    eapply Z.le_trans.
    + exact Hedge.
    + exact IH.
Qed.
Lemma heap_root_is_multiset_max__pop_initialization :
  forall S concrete size,
    1 <= size ->
    heap_representation S concrete size ->
    PrefixMaximum concrete size (Znth 0 concrete 0) /\
    Znth 0 concrete 0 = multiset_max S /\
    multiset_maximum S (Znth 0 concrete 0).
Proof.
  intros S concrete size Hsize Hrepresentation.
  destruct Hrepresentation as
    [Hsize_nonneg
      [Hcapacity
        [Hmultiset_size
          [Hconcrete_length [Hrelation Hordered]]]]].
  assert (Hroot_bound :
    forall index,
      0 <= index < size ->
      Znth index concrete 0 <= Znth 0 concrete 0).
  {
    intros index Hindex.
    eapply heap_ordered_root_upper_bound__pop_initialization; eauto.
  }
  assert (Hnonempty : mlist S <> []).
  {
    intro Hnil.
    unfold multiset_size in Hmultiset_size.
    rewrite Hnil in Hmultiset_size.
    rewrite Zlength_nil in Hmultiset_size.
    lia.
  }
  assert (Hroot_in_concrete : In (Znth 0 concrete 0) concrete).
  {
    unfold Znth.
    apply nth_In.
    apply Nat2Z.inj_lt.
    simpl.
    rewrite <- Zlength_correct.
    lia.
  }
  assert (Hroot_in_multiset : In (Znth 0 concrete 0) (mlist S)).
  {
    eapply Permutation_in.
    - apply Permutation_sym. exact Hrelation.
    - exact Hroot_in_concrete.
  }
  pose proof
    (multiset_max_is_maximum S Hnonempty) as Hmaximum.
  assert (Hroot_le_max :
    Znth 0 concrete 0 <= multiset_max S).
  {
    destruct Hmaximum as [_ Hbound].
    now apply Hbound.
  }
  assert (Hmax_in_concrete : In (multiset_max S) concrete).
  {
    eapply Permutation_in.
    - exact Hrelation.
    - apply multiset_max_member. exact Hnonempty.
  }
  destruct
    (In_nth concrete (multiset_max S) 0 Hmax_in_concrete)
    as [index [Hindex_length Hindex_value]].
  assert (Hmax_le_root :
    multiset_max S <= Znth 0 concrete 0).
  {
    rewrite <- Hindex_value.
    assert (Hnth_as_Znth :
      nth index concrete 0 = Znth (Z.of_nat index) concrete 0).
    {
      unfold Znth.
      rewrite Nat2Z.id.
      reflexivity.
    }
    rewrite Hnth_as_Znth.
    apply Hroot_bound.
    apply Nat2Z.inj_lt in Hindex_length.
    rewrite Zlength_correct in Hconcrete_length.
    lia.
  }
  assert (Hroot_eq : Znth 0 concrete 0 = multiset_max S) by lia.
  split.
  - unfold PrefixMaximum.
    repeat split; try lia.
    intros position Hposition.
    now apply Hroot_bound.
  - split.
    + exact Hroot_eq.
    + rewrite Hroot_eq.
      exact Hmaximum.
Qed.
Lemma pop_root_replacement_remaining_permutation__pop_initialization :
  forall before size,
    1 < size ->
    Zlength before = size ->
    Permutation
      (sublist 0 (size - 1)
        (replace_Znth 0 (Znth (size - 1) before 0) before))
      (sublist 1 size before).
Proof.
  intros before size Hsize Hlength.
  destruct before as [|head tail].
  - rewrite Zlength_nil in Hlength. lia.
  - rewrite Zlength_cons in Hlength.
    change
      (Permutation
        (sublist 0 (size - 1)
          (Znth (size - 1) (head :: tail) 0 :: tail))
        (sublist 1 size (head :: tail))).
    rewrite Znth_cons by lia.
    rewrite sublist_cons1 by lia.
    rewrite sublist_cons2 by (rewrite ?Zlength_cons; lia).
    replace (1 - 1) with 0 by lia.
    replace (size - 1 - 1) with (size - 2) by lia.
    rewrite (sublist_split 0 (size - 1) (size - 2) tail) by lia.
    replace (size - 1) with (size - 2 + 1) by lia.
    rewrite (sublist_single 0 (size - 2) tail) by lia.
    change
      (Permutation
        ([Znth (size - 2) tail 0] ++ sublist 0 (size - 2) tail)
        (sublist 0 (size - 2) tail ++ [Znth (size - 2) tail 0])).
    apply Permutation_app_comm.
Qed.
Lemma pop_root_replacement_loop_state__pop_initialization :
  forall before size,
    1 < size ->
    Zlength before = size ->
    heap_ordered before size ->
    PopLoopState before
      (replace_Znth 0 (Znth (size - 1) before 0) before)
      size 0.
Proof.
  intros before size Hsize Hlength Hordered.
  unfold PopLoopState.
  split; [exact Hsize|].
  split; [exact Hlength|].
  split.
  - rewrite Zlength_replace_Znth. exact Hlength.
  - split; [lia|].
    split; [lia|].
    split; [exact Hordered|].
    split.
    + rewrite Znth_replace_Znth_Same by lia.
      reflexivity.
    + split.
      * rewrite Znth_replace_Znth_Diff by lia.
        reflexivity.
      * split.
        -- unfold PopRemainingElements.
           repeat split; try lia.
           ++ rewrite Zlength_replace_Znth, Hlength. lia.
           ++ now apply
                pop_root_replacement_remaining_permutation__pop_initialization.
        -- split.
           ++ unfold HeapOrderExceptDown.
              split; [lia|].
              split; [lia|].
              intros child
                [Hchild_pos [Hchild_bound Hparent_not_root]].
              assert (Hparent_nonneg : 0 <= heap_parent child).
              {
                unfold heap_parent.
                apply Z.quot_pos; lia.
              }
              assert (Hparent_lt : heap_parent child < child).
              {
                unfold heap_parent.
                apply Z.quot_lt_upper_bound; lia.
              }
              assert (Hchild_size : child < size) by lia.
              pose proof
                (Hordered child
                  (conj Hchild_pos Hchild_size)) as Hedge.
              rewrite Znth_replace_Znth_Diff by
                (rewrite ?Hlength; lia).
              rewrite Znth_replace_Znth_Diff by
                (rewrite ?Hlength; lia).
              exact Hedge.
           ++ unfold PopHoleParentDominatesChildren.
              left. reflexivity.
Qed.
Lemma remove_max_singleton_empty__pop_singleton :
  forall S : multiset Z,
    multiset_size S = 1 ->
    mlist (multiset_remove S (multiset_max S)) = [].
Proof.
  intros S Hsize.
  assert (Hnonempty : mlist S <> []).
  {
    intro Hnil.
    unfold multiset_size in Hsize.
    rewrite Hnil, Zlength_nil in Hsize.
    lia.
  }
  pose proof (multiset_remove_max_size S Hnonempty) as Hremoved.
  unfold multiset_size in Hsize, Hremoved.
  apply Zlength_nil_inv.
  lia.
Qed.
Lemma singleton_full_split_retired__pop_singleton :
  forall (p : Z) (before : list Z) (value : Z),
    Zlength before = 1 ->
    Znth 0 before 0 = value ->
    IntArray.full p 1 before |--
      IntArray.full p 0 [] ** heap_spare p 0.
Proof.
  intros p before value Hlength Hvalue.
  destruct before as [|a before].
  - rewrite Zlength_nil in Hlength.
    lia.
  - destruct before as [|b before].
    + simpl in Hvalue.
      subst value.
      unfold heap_spare.
      rewrite IntArray.full_empty.
      sep_apply IntArray.full_to_seg.
      sep_apply IntArray.seg_to_undef_seg.
      entailer!.
    + rewrite !Zlength_cons in Hlength.
      pose proof (Zlength_nonneg before).
      lia.
Qed.
Lemma heap_children_characterization__pop_child_selection :
  forall index child,
    0 <= index ->
    0 < child ->
    heap_parent child = index ->
    child = heap_left_child index \/
    child = heap_right_child index.
Proof.
  intros index child Hindex Hchild Hparent.
  unfold heap_parent in Hparent.
  pose proof
    (Z.rem_bound_pos_pos (child - 1) 2 ltac:(lia) ltac:(lia))
    as Hrem.
  pose proof (Z.quot_rem (child - 1) 2 ltac:(lia)) as Hquot.
  rewrite Hparent in Hquot.
  assert (Z.rem (child - 1) 2 = 0 \/
          Z.rem (child - 1) 2 = 1) as [Hr | Hr] by lia.
  - left. unfold heap_left_child. lia.
  - right. unfold heap_right_child. lia.
Qed.
Lemma pop_select_left__pop_child_selection :
  forall current size index,
    0 <= index ->
    heap_left_child index < size ->
    (heap_right_child index >= size \/
     Znth (heap_left_child index) current 0 >=
       Znth (heap_right_child index) current 0) ->
    PopSelectedChild current size index (heap_left_child index).
Proof.
  intros current size index Hindex Hleft_bound Hselect.
  unfold PopSelectedChild.
  assert (Hleft_pos : 0 < heap_left_child index).
  { unfold heap_left_child. lia. }
  assert (Hparent_left :
      heap_parent (heap_left_child index) = index).
  {
    unfold heap_parent, heap_left_child.
    replace (index * 2 + 1 - 1) with (index * 2) by ring.
    rewrite Z.quot_mul by lia.
    reflexivity.
  }
  repeat split.
  - exact Hindex.
  - unfold heap_left_child in Hleft_bound |- *.
    lia.
  - unfold heap_left_child. lia.
  - exact (Z.lt_le_incl _ _ Hleft_pos).
  - exact Hleft_bound.
  - exact Hparent_left.
  - unfold heap_selected_child.
    destruct (Z_lt_dec (heap_right_child index) size) as [Hright | Hright].
    + destruct Hselect as [Houtside | Hvalues]; [lia |].
      destruct
        (Z_lt_dec
          (Znth (heap_left_child index) current 0)
          (Znth (heap_right_child index) current 0));
        [lia | reflexivity].
    + reflexivity.
  - intros child [Hchild_pos [Hchild_bound Hparent]].
    pose proof
      (heap_children_characterization__pop_child_selection
        index child Hindex Hchild_pos Hparent)
      as [-> | ->].
    + lia.
    + destruct Hselect as [Houtside | Hvalues].
      * lia.
      * exact Hvalues.
Qed.
Lemma pop_select_right__pop_child_selection :
  forall current size index,
    0 <= index ->
    heap_right_child index < size ->
    Znth (heap_left_child index) current 0 <
      Znth (heap_right_child index) current 0 ->
    PopSelectedChild current size index (heap_right_child index).
Proof.
  intros current size index Hindex Hright_bound Hvalues.
  unfold PopSelectedChild.
  assert (Hright_pos : 0 < heap_right_child index).
  { unfold heap_right_child. lia. }
  assert (Hparent_right :
      heap_parent (heap_right_child index) = index).
  {
    unfold heap_parent, heap_right_child.
    replace (index * 2 + 2 - 1) with (index * 2 + 1) by ring.
    pose proof
      (Z.rem_bound_pos_pos (index * 2 + 1) 2 ltac:(lia) ltac:(lia))
      as Hrem.
    pose proof (Z.quot_rem (index * 2 + 1) 2 ltac:(lia)) as Hquot.
    assert (Z.rem (index * 2 + 1) 2 = 1) by lia.
    lia.
  }
  repeat split.
  - exact Hindex.
  - unfold heap_right_child in Hright_bound. lia.
  - unfold heap_right_child. lia.
  - lia.
  - exact Hright_bound.
  - exact Hparent_right.
  - unfold heap_selected_child.
    destruct (Z_lt_dec (heap_right_child index) size); [|lia].
    destruct
      (Z_lt_dec
        (Znth (heap_left_child index) current 0)
        (Znth (heap_right_child index) current 0));
      [reflexivity | lia].
  - intros child [Hchild_pos [Hchild_bound Hparent]].
    pose proof
      (heap_children_characterization__pop_child_selection
        index child Hindex Hchild_pos Hparent)
      as [-> | ->];
      lia.
Qed.
Lemma pop_comparison_ready__pop_ready_exit :
  forall before current size result index selected,
    PrefixMaximum before size result ->
    PopLoopState before current size index ->
    PopSelectedChild current (size - 1) index selected ->
    Znth index current 0 >= Znth selected current 0 ->
    PopReadyState before current size result.
Proof.
  intros before current size result index selected
    Hmaximum Hloop Hselected Hdominates.
  unfold PopLoopState in Hloop.
  destruct Hloop as
    (Hsize & Hbefore_length & Hcurrent_length &
     Hindex_nonnegative & Hindex_bound & Hbefore_ordered &
     Hhole_value & Hretired_value & Hremaining &
     Hexcept & Hparent_dominates).
  assert (Hcurrent_ordered : heap_ordered current (size - 1)).
  {
    unfold heap_ordered.
    intros child Hchild.
    unfold HeapOrderExceptDown in Hexcept.
    destruct Hexcept as (_ & _ & Hordered).
    destruct (Z.eq_dec (heap_parent child) index) as [Hparent | Hparent].
    + unfold PopSelectedChild in Hselected.
      destruct Hselected as
        (_ & _ & _ & _ & _ & _ & _ & Hselected_dominates).
      specialize (Hselected_dominates child ltac:(tauto)).
      rewrite Hparent.
      lia.
    + apply Hordered.
      tauto.
  }
  unfold PopReadyState.
  exact
    (conj Hsize
      (conj Hbefore_length
        (conj Hcurrent_length
          (conj Hbefore_ordered
            (conj Hmaximum
              (conj Hretired_value
                (conj Hremaining Hcurrent_ordered))))))).
Qed.
Lemma pop_leaf_ready__pop_ready_exit :
  forall before current size result index,
    PrefixMaximum before size result ->
    PopLoopState before current size index ->
    heap_left_child index >= size - 1 ->
    PopReadyState before current size result.
Proof.
  intros before current size result index Hmaximum Hloop Hleft_outside.
  unfold PopLoopState in Hloop.
  destruct Hloop as
    (Hsize & Hbefore_length & Hcurrent_length &
     Hindex_nonnegative & Hindex_bound & Hbefore_ordered &
     Hhole_value & Hretired_value & Hremaining &
     Hexcept & Hparent_dominates).
  assert (Hcurrent_ordered : heap_ordered current (size - 1)).
  {
    unfold heap_ordered.
    intros child Hchild.
    unfold HeapOrderExceptDown in Hexcept.
    destruct Hexcept as (_ & _ & Hordered).
    apply Hordered.
    destruct Hchild as [Hchild_positive Hchild_bound].
    repeat split; try assumption.
    intro Hparent.
    unfold heap_parent in Hparent.
    pose proof
      (Z.quot_rem (child - 1) 2 ltac:(lia))
      as Hquotient_remainder.
    pose proof
      (Z.rem_nonneg (child - 1) 2 ltac:(lia) ltac:(lia))
      as Hremainder_nonnegative.
    rewrite Hparent in Hquotient_remainder.
    unfold heap_left_child in Hleft_outside.
    lia.
  }
  unfold PopReadyState.
  exact
    (conj Hsize
      (conj Hbefore_length
        (conj Hcurrent_length
          (conj Hbefore_ordered
            (conj Hmaximum
              (conj Hretired_value
                (conj Hremaining Hcurrent_ordered))))))).
Qed.
Lemma replace_Znth_swap_form__pop_swap_transition :
  forall (l1 l2 l3 : list Z) (xi xj : Z),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj
        (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r
    with (l1 := l1) (l2 := xi :: l2 ++ xj :: l3)
    by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := Z) n1 l1 xj)
    by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert
    (H0 :
      replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
      xj :: l2 ++ xj :: l3)
    by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r
    with (l1 := l1) (l2 := xj :: l2 ++ xj :: l3)
    by (subst n2; lia).
  rewrite
    (replace_Znth_nothing
      (A := Z) (n1 + 1 + Zlength l2) l1 xi)
    by (subst n1; lia).
  replace
    (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2)
    by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r
    with (l1 := l2) (l2 := xj :: l3)
    by lia.
  rewrite
    (replace_Znth_nothing (A := Z) (Zlength l2) l2 xi)
    by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3)
    by reflexivity.
  rewrite H1.
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__pop_swap_transition :
  forall (l : list Z) i j (d : Z),
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d)
        (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hrange.
  destruct Hrange as [Hi [Hij Hj]].
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr : (nj < length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert
        (Hnat :
          (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat =
          Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm.
      rewrite Hnat.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3)
    by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_Znth_swap_form__pop_swap_transition.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.
Lemma sublist0_replace_Znth_inside__pop_swap_transition :
  forall (l : list Z) hi i value,
    0 <= i < hi ->
    hi <= Zlength l ->
    sublist 0 hi (replace_Znth i value l) =
    replace_Znth i value (sublist 0 hi l).
Proof.
  intros l hi i value Hi Hhi.
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite Zlength_sublist0 by
      (rewrite Zlength_replace_Znth; lia).
    rewrite Zlength_replace_Znth.
    rewrite Zlength_sublist0 by lia.
    reflexivity.
  - intros k Hk.
    rewrite Zlength_sublist0 in Hk by
      (rewrite Zlength_replace_Znth; lia).
    rewrite Znth_sublist0 by lia.
    destruct (Z.eq_dec k i) as [-> | Hki].
    + rewrite !Znth_replace_Znth_Same.
      * reflexivity.
      * rewrite Zlength_sublist0 by lia. lia.
      * lia.
    + rewrite !Znth_replace_Znth_Diff.
      * rewrite Znth_sublist0 by lia.
        reflexivity.
      * rewrite Zlength_sublist0 by lia. lia.
      * rewrite Zlength_sublist0 by lia. lia.
      * lia.
      * lia.
      * lia.
      * lia.
Qed.
Lemma heap_parent_nonnegative_lt__pop_swap_transition :
  forall child,
    0 < child ->
    0 <= heap_parent child < child.
Proof.
  intros child Hchild.
  unfold heap_parent.
  split.
  - apply Z.quot_pos; lia.
  - apply Z.quot_lt_upper_bound; lia.
Qed.
Lemma pop_next_index_arithmetic__pop_swap_transition :
  forall current size index selected,
    0 <= index ->
    selected < size ->
    selected = heap_selected_child current size index ->
    0 <= heap_left_child index /\
    heap_left_child index < size /\
    0 <= heap_right_child index /\
    heap_right_child index <= size.
Proof.
  intros current size index selected Hindex Hselected Hchoice.
  unfold heap_selected_child in Hchoice.
  unfold heap_left_child, heap_right_child in Hchoice |- *.
  destruct
    (Z_lt_dec (index * 2 + 2) size)
    as [Hright | Hright].
  - destruct
      (Z_lt_dec
        (Znth (index * 2 + 1) current 0)
        (Znth (index * 2 + 2) current 0))
      as [Hvalues | Hvalues];
      simpl in Hchoice;
      subst selected;
      repeat split;
      lia.
  - simpl in Hchoice.
    subst selected.
    repeat split;
    lia.
Qed.
Lemma pop_swap_advances_loop__pop_swap_transition :
  forall before current size index selected,
    PopLoopState before current size index ->
    PopSelectedChild current (size - 1) index selected ->
    Znth index current 0 < Znth selected current 0 ->
    PopLoopState before
      (replace_Znth selected (Znth index current 0)
        (replace_Znth index (Znth selected current 0) current))
      size selected.
Proof.
  intros before current size index selected Hloop Hselected Hlt.
  unfold PopLoopState in Hloop |- *.
  destruct Hloop as
    [Hsize
      [Hbefore_len
        [Hcurrent_len
          [Hindex_nonneg
            [Hindex_bound
              [Hbefore_ordered
                [Hindex_value
                  [Hlast_value
                    [Hremaining
                      [Hexcept Hparent_hole]]]]]]]]]].
  unfold PopSelectedChild in Hselected.
  destruct Hselected as
    [Hselected_index_nonneg
      [Hselected_index_bound
        [Hindex_selected
          [Hselected_nonneg
            [Hselected_bound
              [Hselected_parent
                [Hselected_choice Hselected_dominates]]]]]]].
  set
    (swapped :=
      replace_Znth selected (Znth index current 0)
        (replace_Znth index (Znth selected current 0) current)).
  assert
    (Hindex_current : 0 <= index < Zlength current)
    by (rewrite Hcurrent_len; lia).
  assert
    (Hselected_current : 0 <= selected < Zlength current)
    by (rewrite Hcurrent_len; lia).
  assert
    (Hswapped_len : Zlength swapped = Zlength current).
  {
    unfold swapped.
    repeat rewrite Zlength_replace_Znth.
    reflexivity.
  }
  assert
    (Hswap_index :
      Znth index swapped 0 = Znth selected current 0).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by exact Hindex_current.
    reflexivity.
  }
  assert
    (Hswap_selected :
      Znth selected swapped 0 = Znth index current 0).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_replace_Znth; exact Hselected_current).
    reflexivity.
  }
  assert
    (Hswap_other :
      forall k,
        0 <= k < Zlength current ->
        k <> index ->
        k <> selected ->
        Znth k swapped 0 = Znth k current 0).
  {
    intros k Hk Hki Hks.
    unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
  }
  split.
  - exact Hsize.
  - split.
    + exact Hbefore_len.
    + split.
      * rewrite Hswapped_len.
        exact Hcurrent_len.
      * split.
        -- exact Hselected_nonneg.
        -- split.
           ++ exact Hselected_bound.
           ++ split.
              ** exact Hbefore_ordered.
              ** split.
                 --- rewrite Hswap_selected.
                     exact Hindex_value.
                 --- split.
                     +++ rewrite Hswap_other by
                           (rewrite ?Hcurrent_len; lia).
                         exact Hlast_value.
                     +++ split.
                         {
    unfold PopRemainingElements in Hremaining |- *.
    destruct Hremaining as
      [Hremaining_size
        [Hremaining_before
          [Hremaining_current Hremaining_perm]]].
    split.
    + exact Hremaining_size.
    + split.
      * exact Hremaining_before.
      * split.
        -- rewrite Hswapped_len.
           exact Hremaining_current.
        -- assert
        (Hprefix :
          sublist 0 (size - 1) swapped =
          replace_Znth selected (Znth index current 0)
            (replace_Znth index (Znth selected current 0)
              (sublist 0 (size - 1) current))).
           {
             unfold swapped.
             rewrite
               sublist0_replace_Znth_inside__pop_swap_transition
               by (rewrite ?Zlength_replace_Znth, ?Hcurrent_len; lia).
             rewrite
               sublist0_replace_Znth_inside__pop_swap_transition
               by (rewrite ?Hcurrent_len; lia).
             reflexivity.
           }
           rewrite Hprefix.
           eapply Permutation_trans.
           ++ apply Permutation_sym.
              replace
          (Znth index current 0)
          with
          (Znth index (sublist 0 (size - 1) current) 0).
              2:{
                rewrite Znth_sublist0 by lia.
                reflexivity.
              }
              replace
          (Znth selected current 0)
          with
          (Znth selected (sublist 0 (size - 1) current) 0).
              2:{
                rewrite Znth_sublist0 by lia.
                reflexivity.
              }
              apply
                permutation_swap_Znth_lt__pop_swap_transition.
              rewrite Zlength_sublist0 by
                (rewrite Hcurrent_len; lia).
              lia.
           ++ exact Hremaining_perm.
                         }
                         {
                           unfold HeapOrderExceptDown in Hexcept.
                           destruct Hexcept as
                             [Hexcept_index_nonneg
                               [Hexcept_index_bound Hexcept_edges]].
                           split.
  - unfold HeapOrderExceptDown.
    repeat split.
    + exact Hselected_nonneg.
    + exact Hselected_bound.
    + intros child
        [Hchild_pos [Hchild_bound Hchild_parent_not_selected]].
      pose proof
        (heap_parent_nonnegative_lt__pop_swap_transition
          child Hchild_pos)
        as Hparent_bounds.
      destruct
        (Z.eq_dec (heap_parent child) index)
        as [Hparent_index | Hparent_not_index].
      * destruct (Z.eq_dec child selected)
          as [Hchild_selected | Hchild_not_selected].
        -- subst child.
           rewrite Hparent_index, Hswap_index, Hswap_selected.
           lia.
        -- assert (Hchild_not_index : child <> index) by lia.
           rewrite Hparent_index, Hswap_index.
           rewrite Hswap_other by
             (rewrite ?Hcurrent_len; lia).
           apply Hselected_dominates.
           repeat split; assumption.
      * destruct (Z.eq_dec child index)
          as [Hchild_index | Hchild_not_index].
        -- subst child.
           assert
             (Hparent_not_selected :
               heap_parent index <> selected)
             by exact Hchild_parent_not_selected.
           rewrite Hswap_other by
             (rewrite ?Hcurrent_len; lia).
           rewrite Hswap_index.
           destruct Hparent_hole as
             [Hindex_zero | Hparent_dominates].
           ++ lia.
           ++ apply Hparent_dominates.
              repeat split.
              ** lia.
              ** exact Hselected_bound.
              ** exact Hselected_parent.
        -- assert (Hchild_not_selected : child <> selected).
           {
             intro Hchild_selected.
             subst child.
             contradiction.
           }
           rewrite Hswap_other by
             (rewrite ?Hcurrent_len; lia).
           rewrite Hswap_other by
             (rewrite ?Hcurrent_len; lia).
           apply Hexcept_edges.
           repeat split; assumption.
  - unfold PopHoleParentDominatesChildren.
    right.
    intros child
      [Hchild_pos [Hchild_bound Hchild_parent_selected]].
    pose proof
      (heap_parent_nonnegative_lt__pop_swap_transition
        child Hchild_pos)
      as Hparent_bounds.
    assert (Hchild_not_selected : child <> selected) by lia.
    assert (Hchild_not_index : child <> index) by lia.
    rewrite Hselected_parent.
    rewrite Hswap_index.
    rewrite Hswap_other by
      (rewrite ?Hcurrent_len; lia).
    specialize
      (Hexcept_edges child
        ltac:(repeat split; try assumption; lia)).
    rewrite Hchild_parent_selected in Hexcept_edges.
    exact Hexcept_edges.
                         }
Qed.
Lemma sublist_replace_last__pop_finalization :
  forall (A : Type) (d v : A) (l : list A) n,
    0 < n ->
    Zlength l = n ->
    sublist 0 (n - 1) (replace_Znth (n - 1) v l) =
    sublist 0 (n - 1) l.
Proof.
  intros A d v l n Hn Hlen.
  apply (proj2 (list_eq_ext _ _ d)).
  split.
  - rewrite !Zlength_sublist0.
    + reflexivity.
    + lia.
    + rewrite Zlength_replace_Znth. lia.
  - intros i Hi.
    rewrite Zlength_sublist0 in Hi.
    2: rewrite Zlength_replace_Znth; lia.
    rewrite !Znth_sublist0 by lia.
    apply Znth_replace_Znth_Diff; rewrite ?Zlength_replace_Znth; lia.
Qed.
Lemma heap_ordered_sublist0__pop_finalization :
  forall concrete size,
    heap_ordered concrete size ->
    heap_ordered (sublist 0 size concrete) size.
Proof.
  intros concrete size Hordered.
  unfold heap_ordered in *.
  intros child Hchild.
  assert (Hparent_nonnegative : 0 <= heap_parent child).
  {
    unfold heap_parent.
    apply Z.quot_pos; lia.
  }
  assert (Hparent_upper : heap_parent child <= child - 1).
  {
    unfold heap_parent.
    apply Z.quot_le_upper_bound; lia.
  }
  rewrite !Znth_sublist0 by lia.
  apply Hordered. exact Hchild.
Qed.
Lemma pop_ready_write_result__pop_finalization :
  forall S before current size value,
    value = multiset_max S ->
    heap_representation S before size ->
    PopReadyState before current size value ->
    PopResult S before current size value.
Proof.
  intros S before current size value Hvalue Hrepresentation Hready.
  destruct Hrepresentation as
    [Hsize0 [Hcapacity [Hmultiset_size
      [Hbefore_length [Hrelation Hbefore_ordered]]]]].
  unfold PopReadyState in Hready.
  destruct Hready as
    [Hsize [Hbefore_length' [Hcurrent_length
      [Hbefore_ordered' [Hmaximum
        [Hlast [Hremaining Hcurrent_ordered]]]]]]].
  unfold PrefixMaximum in Hmaximum.
  destruct Hmaximum as
    [Hpositive [Hprefix_bound [Hroot Hupper]]].
  unfold PopRemainingElements in Hremaining.
  destruct Hremaining as
    [Hremaining_size [Hremaining_before
      [Hremaining_current Hremaining_perm]]].
  assert (Hbefore_split :
    before = value :: sublist 1 size before).
  {
    assert (Hfirst :
      sublist 0 1 before = [Znth 0 before 0]).
    {
      replace 1 with (0 + 1) by lia.
      apply sublist_single. lia.
    }
    rewrite <-
      (sublist_self before size (eq_sym Hbefore_length)) at 1.
    rewrite (sublist_split 0 size 1 before) by lia.
    rewrite Hfirst.
    rewrite Hroot. reflexivity.
  }
  assert (Hmember : In value (mlist S)).
  {
    eapply Permutation_in.
    - apply Permutation_sym. exact Hrelation.
    - rewrite Hbefore_split. now left.
  }
  destruct
    (proj1
      (multiset_remove_spec S value)
      Hmember) as [Hremove_size Hremove_perm].
  assert (Hremoved_tail :
    Permutation
      (sublist 1 size before)
      (mlist (multiset_remove S value))).
  {
    apply Permutation_cons_inv with (a := value).
    eapply Permutation_trans.
    - rewrite <- Hbefore_split.
      apply Permutation_sym. exact Hrelation.
    - exact Hremove_perm.
  }
  unfold PopResult.
  repeat split.
  - lia.
  - exact Hbefore_length.
  - exact Hcurrent_length.
  - exact Hvalue.
  - apply heap_ordered_sublist0__pop_finalization.
    exact Hcurrent_ordered.
  - eapply Permutation_trans.
    + exact Hremaining_perm.
    + exact Hremoved_tail.
Qed.
Lemma pop_result_store_retired__pop_finalization :
  forall p S before result size value,
    size <= heap_capacity ->
    PopResult S before result size value ->
    IntArray.full p size result |--
      store_heap p (multiset_remove S value) (size - 1) **
      IntArray.undef_seg p (size - 1) size.
Proof.
  intros p S before result size value Hcapacity Hresult.
  unfold PopResult in Hresult.
  destruct Hresult as
    [Hsize [Hbefore_length [Hresult_length
      [Hvalue [Hordered Hpermutation]]]]].
  assert (Hprefix_length :
    Zlength (sublist 0 (size - 1) result) = size - 1).
  {
    rewrite Zlength_sublist0; lia.
  }
  assert (Hrepresentation :
    heap_representation
      (multiset_remove S value)
      (sublist 0 (size - 1) result)
      (size - 1)).
  {
    unfold heap_representation, heap_relation.
    repeat split.
    - lia.
    - lia.
    - unfold multiset_size.
      pose proof (Permutation_length Hpermutation) as Hlength.
      rewrite !Zlength_correct.
      rewrite <- Hlength.
      now rewrite <- Zlength_correct.
    - exact Hprefix_length.
    - apply Permutation_sym. exact Hpermutation.
    - exact Hordered.
  }
  unfold store_heap.
  Exists (sublist 0 (size - 1) result).
  sep_apply_l_atomic
    (IntArray.full_split_to_seg
      p (size - 1) size result ltac:(lia)).
  sep_apply_l_atomic
    (IntArray.seg_to_full
      p 0 (size - 1) (sublist 0 (size - 1) result)).
  sep_apply_l_atomic
    (IntArray.seg_to_undef_seg
      p (size - 1) size (sublist (size - 1) size result)).
  replace (p + 0 * sizeof(INT)) with p by lia.
  replace (size - 1 - 0) with (size - 1) by lia.
  entailer!.
Qed.

Lemma heap_sort_spare_is_write_slot__heap_sort_write :
  forall p i,
    heap_spare p (i - 1) |--
      IntArray.undef_seg p (i - 1) i.
Proof.
  intros p i.
  unfold heap_spare.
  replace (i - 1 + 1) with i by lia.
  entailer!.
Qed.

Lemma heap_sort_written_slot_split__heap_sort_write :
  forall p i n extracted suffix,
    1 <= i ->
    i <= n ->
    IntArray.seg p (i - 1) n (extracted :: suffix) |--
      heap_retired_cell p (i - 1) extracted **
      IntArray.seg p i n suffix.
Proof.
  intros p i n extracted suffix Hi Hin.
  unfold heap_retired_cell.
  replace (i - 1 + 1) with i by lia.
  rewrite
    (IntArray.seg_unfold
      p (i - 1) n suffix extracted).
  replace (i - 1 + 1) with i by lia.
  sep_apply_l_atomic
    (IntArray.seg_single p (i - 1) extracted).
  replace (i - 1 + 1) with i by lia.
  cancel.
Qed.

Lemma heap_sort_initial_state__heap_sort_setup :
  forall input,
    HeapSortState input (list_to_multiset input) [].
Proof.
  intros input.
  unfold HeapSortState, list_to_multiset.
  simpl.
  split.
  - rewrite app_nil_r.
    apply Permutation_refl.
  - split.
    + exact I.
    + intros active_value suffix_value _ Hsuffix.
      inversion Hsuffix.
Qed.
Lemma heap_sort_extract_step__heap_sort_transition :
  forall input active suffix extracted,
    extracted = multiset_max active ->
    multiset_maximum active extracted ->
    HeapSortState input active suffix ->
    multiset_size
      (multiset_remove active (multiset_max active)) =
      multiset_size active - 1 /\
    HeapSortState input
      (multiset_remove active (multiset_max active))
      (extracted :: suffix).
Proof.
  intros input active suffix extracted
    Hextracted Hmaximum Hstate.
  subst extracted.
  destruct Hmaximum as [Hmax_member Hmax_upper].
  destruct Hstate as [Hpermutation [Hincreasing Hcross_order]].
  destruct
    (proj1
      (multiset_remove_spec active (multiset_max active))
      Hmax_member) as [Hremove_size Hremove_permutation].
  split.
  - exact Hremove_size.
  - unfold HeapSortState.
    repeat split.
    + eapply Permutation_trans.
      * exact Hpermutation.
      * eapply Permutation_trans.
        -- apply Permutation_app_tail.
           exact Hremove_permutation.
        -- apply Permutation_middle.
    + destruct suffix as [| suffix_head suffix_tail].
      * simpl. exact I.
      * simpl in *.
        split.
        -- apply Hcross_order.
           ++ exact Hmax_member.
           ++ now left.
        -- exact Hincreasing.
    + intros active_value suffix_value
        Hactive_value Hsuffix_value.
      assert (Hactive_value_original :
        In active_value (mlist active)).
      {
        eapply Permutation_in.
        - apply Permutation_sym.
          exact Hremove_permutation.
        - now right.
      }
      destruct Hsuffix_value as
        [Hsuffix_value | Hsuffix_value].
      * subst suffix_value.
        now apply Hmax_upper.
      * eapply Hcross_order; eauto.
Qed.
Lemma heap_sort_empty_state_output__heap_sort_finalization :
  forall (input : list Z) (active : multiset Z) (suffix : list Z),
    multiset_size active = 0 ->
    HeapSortState input active suffix ->
    mlist active = [] /\
    Permutation input suffix /\
    increasing suffix.
Proof.
  intros input active suffix Hsize Hstate.
  assert (Hactive_nil : mlist active = []).
  {
    unfold multiset_size in Hsize.
    destruct (mlist active) as [|x xs] eqn:Hactive.
    - reflexivity.
    - rewrite Zlength_cons in Hsize.
      pose proof (Zlength_nonneg xs).
      lia.
  }
  unfold HeapSortState in Hstate.
  destruct Hstate as [Hperm [Hincreasing _]].
  rewrite Hactive_nil, app_nil_l in Hperm.
  repeat split; assumption.
Qed.
Lemma heap_sort_zero_store_join__heap_sort_finalization :
  forall (p n : Z) (active : multiset Z) (suffix : list Z),
    0 <= n ->
    store_heap p active 0 **
    IntArray.seg p 0 n suffix |--
    IntArray.full p n suffix.
Proof.
  intros p n active suffix Hn.
  unfold store_heap.
  Intros concrete.
  match goal with
  | Hrepresentation : heap_representation active concrete 0 |- _ =>
      destruct Hrepresentation as
        [_ [_ [_ [Hconcrete_length [_ _]]]]]
  end.
  assert (Hconcrete_nil : concrete = []).
  {
    destruct concrete as [|x xs].
    - reflexivity.
    - rewrite Zlength_cons in Hconcrete_length.
      pose proof (Zlength_nonneg xs).
      lia.
  }
  subst concrete.
  sep_apply_l_atomic
    (IntArray.full_to_seg p 0 ([] : list Z)).
  sep_apply_l_atomic
    (IntArray.seg_merge_to_full
      p 0 0 n ([] : list Z) suffix ltac:(lia)).
  replace (p + 0 * sizeof(INT)) with p by lia.
  replace (n - 0) with n by lia.
  simpl.
  entailer!.
Qed.
