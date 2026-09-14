Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
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

Record multiset (A : Type) : Type := {
  mlist : list A
}.

Arguments mlist {A} _.

Definition list_to_multiset {A} (l : list A) : multiset A :=
  {| mlist := l |}.

Definition multiset_size {A} (S : multiset A) : Z :=
  Zlength (mlist S).

Definition multiset_equiv {A} (S1 S2 : multiset A) : Prop :=
  Permutation (mlist S1) (mlist S2).

Definition multiset_insert {A}
    (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (x :: mlist S).

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

Definition heap_item (key data : Z) : Z * Z := (key, data).

Definition item_key (item : Z * Z) : Z := fst item.

Definition item_data (item : Z * Z) : Z := snd item.

Definition pair_list (key_values data_values : list Z) : list (Z * Z) :=
  combine key_values data_values.

Definition multiset_min (S : multiset (Z * Z)) : Z * Z :=
  match mlist S with
  | [] => heap_item 0 0
  | x :: xs =>
      fold_right
        (fun y best =>
          if Z.leb (item_key y) (item_key best) then y else best)
        x xs
  end.

Definition multiset_minimum
    (S : multiset (Z * Z)) (item : Z * Z) : Prop :=
  In item (mlist S) /\
  forall x,
    In x (mlist S) ->
    item_key item <= item_key x.

Definition heap_capacity : Z := 100000.

Definition heap_parent (child : Z) : Z :=
  Z.quot (child - 1) 2.

Definition heap_left_child (index : Z) : Z :=
  index * 2 + 1.

Definition heap_right_child (index : Z) : Z :=
  index * 2 + 2.

Definition heap_selected_child
    (key_values : list Z) (size index : Z) : Z :=
  let left := heap_left_child index in
  let right := heap_right_child index in
  match Z_lt_dec right size with
  | left _ =>
      if Z.leb (Znth left key_values 0) (Znth right key_values 0)
      then left
      else right
  | right _ => left
  end.

Definition heap_relation
    (S : multiset (Z * Z)) (key_values data_values : list Z) : Prop :=
  Permutation (mlist S) (pair_list key_values data_values).

Definition heap_ordered (key_values : list Z) (size : Z) : Prop :=
  forall child,
    0 < child /\ child < size ->
    Znth (heap_parent child) key_values 0 <= Znth child key_values 0.

Definition heap_representation
    (S : multiset (Z * Z))
    (key_values data_values : list Z) (size : Z) : Prop :=
  0 <= size /\
  size <= heap_capacity /\
  multiset_size S = size /\
  Zlength key_values = size /\
  Zlength data_values = size /\
  heap_relation S key_values data_values /\
  heap_ordered key_values size.

Definition heap_spare (p size : Z) : Assertion :=
  IntArray.undef_seg p size (size + 1).

Definition heap_tail (p size : Z) : Assertion :=
  match Z_lt_dec size heap_capacity with
  | left _ =>
      heap_spare p size **
      IntArray.undef_seg p (size + 1) heap_capacity
  | right _ =>
      IntArray.undef_seg p size heap_capacity
  end.

Definition store_heap
    (key data : addr) (S : multiset (Z * Z)) (size : Z)
    : Assertion :=
  EX key_values : list Z,
  EX data_values : list Z,
    “ heap_representation S key_values data_values size ” &&
    IntArray.full key size key_values **
    heap_tail key size **
    IntArray.full data size data_values **
    heap_tail data size.

Lemma heap_tail_to_undef_seg :
  forall p size,
    0 <= size <= heap_capacity ->
    heap_tail p size |-- IntArray.undef_seg p size heap_capacity.
Proof.
  intros p size Hrange.
  unfold heap_tail.
  destruct (Z_lt_dec size heap_capacity) as [Hlt | Hnot].
  - unfold heap_spare.
    sep_apply
      (IntArray.undef_seg_merge_to_undef_seg
        p size (size + 1) heap_capacity ltac:(lia)).
    entailer!.
  - assert (size = heap_capacity) by lia.
    subst size.
    entailer!.
Qed.

Lemma undef_seg_to_heap_tail :
  forall p size,
    0 <= size <= heap_capacity ->
    IntArray.undef_seg p size heap_capacity |-- heap_tail p size.
Proof.
  intros p size Hrange.
  unfold heap_tail.
  destruct (Z_lt_dec size heap_capacity) as [Hlt | Hnot].
  - unfold heap_spare.
    sep_apply
      (IntArray.undef_seg_split_to_undef_seg
        p size (size + 1) heap_capacity ltac:(lia)).
    entailer!.
  - assert (size = heap_capacity) by lia.
    subst size.
    entailer!.
Qed.

Lemma concrete_arrays_to_store_heap__build_finalization :
  forall key data S key_values data_values size,
    0 <= size <= heap_capacity ->
    heap_representation S key_values data_values size ->
    IntArray.full key size key_values **
    IntArray.undef_seg key size heap_capacity **
    IntArray.full data size data_values **
    IntArray.undef_seg data size heap_capacity
    |-- store_heap key data S size.
Proof.
  intros key data S key_values data_values size Hbounds Hrepresentation.
  unfold store_heap.
  Exists key_values data_values.
  sep_apply_l_atomic
    (undef_seg_to_heap_tail key size Hbounds).
  sep_apply_l_atomic
    (undef_seg_to_heap_tail data size Hbounds).
  entailer!.
Qed.

Definition heap_retired_pair
    (key data index : Z) (item : Z * Z) : Assertion :=
  IntArray.seg key index (index + 1) [item_key item] **
  IntArray.seg data index (index + 1) [item_data item].

Definition KeyWriteState
    (before : multiset (Z * Z))
    (key_base data_base key_written : list Z)
    (size key_x : Z) : Prop :=
  heap_representation before key_base data_base size /\
  key_written = key_base ++ [key_x].

Definition HeapOrderExceptUp
    (key_values : list Z) (size child : Z) : Prop :=
  0 <= child /\
  child < size /\
  forall node,
    0 < node /\ node < size /\ node <> child ->
    Znth (heap_parent node) key_values 0 <= Znth node key_values 0.

Definition PushHoleChildrenPreserved
    (key_values : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node /\ node < size /\ heap_parent node = child ->
    Znth (heap_parent child) key_values 0 <= Znth node key_values 0.

Definition PushSource
    (key_written data_written : list Z)
    (before : multiset (Z * Z))
    (size data_x key_x : Z) : Prop :=
  Zlength key_written = size + 1 /\
  Zlength data_written = size + 1 /\
  Permutation
    (pair_list key_written data_written)
    (heap_item key_x data_x :: mlist before) /\
  heap_ordered (sublist 0 size key_written) size.

Definition PushLoopState
    (key_written data_written key_current data_current : list Z)
    (size child data_x key_x : Z) : Prop :=
  0 <= size /\
  Zlength key_written = size + 1 /\
  Zlength data_written = size + 1 /\
  Zlength key_current = size + 1 /\
  Zlength data_current = size + 1 /\
  0 <= child /\
  child <= size /\
  Znth child key_current 0 = key_x /\
  Znth child data_current 0 = data_x /\
  Permutation
    (pair_list key_written data_written)
    (pair_list key_current data_current) /\
  HeapOrderExceptUp key_current (size + 1) child /\
  PushHoleChildrenPreserved key_current (size + 1) child.

Definition PushResult
    (before : multiset (Z * Z))
    (key_result data_result : list Z)
    (size data_x key_x : Z) : Prop :=
  0 <= size /\
  Zlength key_result = size + 1 /\
  Zlength data_result = size + 1 /\
  Permutation
    (pair_list key_result data_result)
    (heap_item key_x data_x :: mlist before) /\
  heap_ordered key_result (size + 1).

Definition BuildPrefixState
    (prefix : multiset (Z * Z))
    (key_input data_input : list Z) (processed : Z) : Prop :=
  1 <= processed /\
  processed <= Zlength key_input /\
  processed <= Zlength data_input /\
  multiset_equiv
    prefix
    (list_to_multiset
      (pair_list
        (sublist 0 processed key_input)
        (sublist 0 processed data_input))).

Definition PrefixMinimum
    (key_values data_values : list Z)
    (size : Z) (item : Z * Z) : Prop :=
  0 < size /\
  size <= Zlength key_values /\
  size <= Zlength data_values /\
  item = heap_item (Znth 0 key_values 0) (Znth 0 data_values 0) /\
  forall i,
    0 <= i /\ i < size ->
    item_key item <= Znth i key_values 0.

Definition HeapOrderExceptDown
    (key_values : list Z) (size index : Z) : Prop :=
  0 <= index /\
  index < size /\
  forall child,
    0 < child /\ child < size /\ heap_parent child <> index ->
    Znth (heap_parent child) key_values 0 <= Znth child key_values 0.

Definition PopHoleParentDominatesChildren
    (key_values : list Z) (size index : Z) : Prop :=
  index = 0 \/
  forall child,
    0 < child /\ child < size /\ heap_parent child = index ->
    Znth (heap_parent index) key_values 0 <= Znth child key_values 0.

Definition PopSelectedChild
    (key_values : list Z) (size index selected : Z) : Prop :=
  0 <= index /\
  index < size /\
  index < selected /\
  0 <= selected /\
  selected < size /\
  heap_parent selected = index /\
  selected = heap_selected_child key_values size index /\
  forall child,
    0 < child /\ child < size /\ heap_parent child = index ->
    Znth selected key_values 0 <= Znth child key_values 0.

Definition PopRemainingElements
    (before_key before_data current_key current_data : list Z)
    (size : Z) : Prop :=
  1 <= size /\
  size <= Zlength before_key /\
  size <= Zlength before_data /\
  size <= Zlength current_key /\
  size <= Zlength current_data /\
  Permutation
    (pair_list
      (sublist 0 (size - 1) current_key)
      (sublist 0 (size - 1) current_data))
    (pair_list
      (sublist 1 size before_key)
      (sublist 1 size before_data)).

Definition PopLoopState
    (before_key before_data current_key current_data : list Z)
    (size index : Z) : Prop :=
  1 < size /\
  Zlength before_key = size /\
  Zlength before_data = size /\
  Zlength current_key = size /\
  Zlength current_data = size /\
  0 <= index /\
  index < size - 1 /\
  heap_ordered before_key size /\
  Znth index current_key 0 = Znth (size - 1) before_key 0 /\
  Znth index current_data 0 = Znth (size - 1) before_data 0 /\
  PopRemainingElements before_key before_data current_key current_data size /\
  HeapOrderExceptDown current_key (size - 1) index /\
  PopHoleParentDominatesChildren current_key (size - 1) index.

Definition PopReadyState
    (before_key before_data current_key current_data : list Z)
    (size : Z) (item : Z * Z) : Prop :=
  1 < size /\
  Zlength before_key = size /\
  Zlength before_data = size /\
  Zlength current_key = size /\
  Zlength current_data = size /\
  heap_ordered before_key size /\
  PrefixMinimum before_key before_data size item /\
  PopRemainingElements before_key before_data current_key current_data size /\
  heap_ordered current_key (size - 1).

Definition PopResult
    (S : multiset (Z * Z))
    (before_key before_data result_key result_data : list Z)
    (size : Z) (item : Z * Z) : Prop :=
  1 <= size /\
  Zlength before_key = size /\
  Zlength before_data = size /\
  Zlength result_key = size /\
  Zlength result_data = size /\
  heap_ordered (sublist 0 (size - 1) result_key) (size - 1) /\
  Permutation
    (pair_list
      (sublist 0 (size - 1) result_key)
      (sublist 0 (size - 1) result_data))
    (mlist (multiset_remove S item)).

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

Lemma fold_right_item_min_member :
  forall xs base,
    In
      (fold_right
        (fun y best =>
          if Z.leb (item_key y) (item_key best) then y else best)
        base xs)
      (base :: xs).
Proof.
  induction xs as [|x xs IH]; intro base.
  - simpl. now left.
  - simpl.
    destruct
      (Z.leb (item_key x)
        (item_key
          (fold_right
            (fun y best =>
              if Z.leb (item_key y) (item_key best)
              then y else best)
            base xs))) eqn:Hcmp.
    + simpl. now right; left.
    + specialize (IH base).
      simpl. destruct IH as [IH | IH].
      * now left.
      * right. now right.
Qed.

Lemma fold_right_item_min_lower_bound :
  forall xs base value,
    In value (base :: xs) ->
    item_key
      (fold_right
        (fun y best =>
          if Z.leb (item_key y) (item_key best) then y else best)
        base xs) <= item_key value.
Proof.
  induction xs as [|x xs IH]; intros base value Hin.
  - simpl in *. destruct Hin as [-> | []]. lia.
  - simpl in *.
    destruct
      (Z.leb (item_key x)
        (item_key
          (fold_right
            (fun y best =>
              if Z.leb (item_key y) (item_key best)
              then y else best)
            base xs))) eqn:Hcmp.
    + apply Z.leb_le in Hcmp.
      destruct Hin as [-> | [-> | Hin]].
      * eapply Z.le_trans.
        -- exact Hcmp.
        -- apply IH. now left.
      * lia.
      * eapply Z.le_trans.
        -- exact Hcmp.
        -- apply IH. now right.
    + apply Z.leb_gt in Hcmp.
      destruct Hin as [-> | [-> | Hin]].
      * apply IH. now left.
      * lia.
      * apply IH. now right.
Qed.

Lemma multiset_min_is_minimum :
  forall S,
    mlist S <> [] ->
    multiset_minimum S (multiset_min S).
Proof.
  intros S Hnonempty.
  unfold multiset_min, multiset_minimum.
  destruct (mlist S) as [|x xs] eqn:Hlist.
  - contradiction.
  - split.
    + apply fold_right_item_min_member.
    + intros value Hin.
      now apply fold_right_item_min_lower_bound.
Qed.

Lemma multiset_min_member :
  forall S,
    mlist S <> [] ->
    In (multiset_min S) (mlist S).
Proof.
  intros S Hnonempty.
  now destruct (multiset_min_is_minimum S Hnonempty).
Qed.

Lemma multiset_min_lower_bound :
  forall S value,
    mlist S <> [] ->
    In value (mlist S) ->
    item_key (multiset_min S) <= item_key value.
Proof.
  intros S value Hnonempty Hin.
  destruct (multiset_min_is_minimum S Hnonempty) as [_ Hbound].
  now apply Hbound.
Qed.

Lemma multiset_remove_min_size :
  forall S,
    mlist S <> [] ->
    multiset_size (multiset_remove S (multiset_min S)) =
    multiset_size S - 1.
Proof.
  intros S Hnonempty.
  destruct
    (multiset_remove_spec S (multiset_min S))
    as [Hpresent _].
  apply Hpresent.
  now apply multiset_min_member.
Qed.

Lemma Zlength_combine_eq :
  forall {A B : Type} (l1 : list A) (l2 : list B),
    Zlength l1 = Zlength l2 ->
    Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros A B l1 l2 Hlen.
  rewrite !Zlength_correct in *.
  rewrite length_combine.
  rewrite Nat.min_l.
  - reflexivity.
  - apply Nat2Z.inj_le.
    lia.
Qed.

Lemma Znth_combine_eq :
  forall {A B : Type} i (l1 : list A) (l2 : list B) d1 d2,
    0 <= i < Zlength l1 ->
    Zlength l1 = Zlength l2 ->
    Znth i (combine l1 l2) (d1, d2) =
      (Znth i l1 d1, Znth i l2 d2).
Proof.
  intros A B i l1.
  revert i.
  induction l1 as [|a l1 IH]; intros.
  - rewrite Zlength_correct in H. simpl in H. lia.
  - destruct l2 as [|b l2].
    + rewrite !Zlength_correct in H0. simpl in H0. lia.
    + simpl.
      destruct (Z_le_lt_eq_dec 0 i ltac:(lia)) as [Hi | Hi].
      * rewrite (Znth_cons (d1, d2) i (a, b) (combine l1 l2))
          by lia.
        rewrite (Znth_cons d1 i a l1) by lia.
        rewrite (Znth_cons d2 i b l2) by lia.
        apply IH.
        -- rewrite Zlength_correct in *. simpl in *. lia.
        -- rewrite !Zlength_correct in *. simpl in *. lia.
      * subst i.
        rewrite (Znth0_cons (d1, d2) (a, b) (combine l1 l2)).
        rewrite (Znth0_cons d1 a l1).
        rewrite (Znth0_cons d2 b l2).
        reflexivity.
Qed.

Lemma pair_list_app_single :
  forall key_values data_values key_x data_x,
    Zlength key_values = Zlength data_values ->
    pair_list (key_values ++ [key_x]) (data_values ++ [data_x]) =
    pair_list key_values data_values ++ [heap_item key_x data_x].
Proof.
  intros key_values data_values key_x data_x Hlen.
  unfold pair_list, heap_item.
  rewrite combine_app.
  - reflexivity.
  - apply Nat2Z.inj.
    now rewrite <- !Zlength_correct.
Qed.

Lemma pair_list_sublist_snoc :
  forall key_values data_values i,
    Zlength key_values = Zlength data_values ->
    0 <= i < Zlength key_values ->
    pair_list
      (sublist 0 (i + 1) key_values)
      (sublist 0 (i + 1) data_values) =
    pair_list
      (sublist 0 i key_values)
      (sublist 0 i data_values) ++
    [heap_item (Znth i key_values 0) (Znth i data_values 0)].
Proof.
  intros key_values data_values i Hlen Hi.
  unfold pair_list, heap_item.
  rewrite (sublist_split 0 (i + 1) i key_values) by lia.
  rewrite (sublist_split 0 (i + 1) i data_values) by lia.
  rewrite (sublist_single 0 i key_values) by lia.
  rewrite (sublist_single 0 i data_values) by lia.
  rewrite combine_app.
  - reflexivity.
  - apply Nat2Z.inj.
    rewrite <- !Zlength_correct.
    rewrite !Zlength_sublist by lia.
    lia.
Qed.

Lemma pair_list_sublist_self :
  forall key_values data_values n,
    Zlength key_values = n ->
    Zlength data_values = n ->
    pair_list
      (sublist 0 n key_values)
      (sublist 0 n data_values) =
    pair_list key_values data_values.
Proof.
  intros key_values data_values n Hkey Hdata.
  rewrite (sublist_self key_values n) by exact (eq_sym Hkey).
  rewrite (sublist_self data_values n) by exact (eq_sym Hdata).
  reflexivity.
Qed.

Lemma pair_list_cons_split :
  forall key_values data_values size,
    0 < size ->
    Zlength key_values = size ->
    Zlength data_values = size ->
    pair_list key_values data_values =
      heap_item (Znth 0 key_values 0) (Znth 0 data_values 0) ::
      pair_list
        (sublist 1 size key_values)
        (sublist 1 size data_values).
Proof.
  intros key_values data_values size Hsize Hkey Hdata.
  destruct key_values as [|key_head key_tail].
  - rewrite Zlength_nil in Hkey. lia.
  - destruct data_values as [|data_head data_tail].
    + rewrite Zlength_nil in Hdata. lia.
    + simpl.
      rewrite !Znth0_cons.
      rewrite (sublist_cons2 1 size key_head key_tail) by lia.
      rewrite (sublist_cons2 1 size data_head data_tail) by lia.
      replace (1 - 1) with 0 by lia.
      rewrite (sublist_self key_tail (size - 1)).
      2:{ rewrite Zlength_cons in Hkey. lia. }
      rewrite (sublist_self data_tail (size - 1)).
      2:{ rewrite Zlength_cons in Hdata. lia. }
      reflexivity.
Qed.

Lemma pair_list_sublist :
  forall key_values data_values lo hi,
    Zlength key_values = Zlength data_values ->
    0 <= lo <= hi ->
    hi <= Zlength key_values ->
    pair_list
      (sublist lo hi key_values)
      (sublist lo hi data_values) =
    sublist lo hi (pair_list key_values data_values).
Proof.
  intros key_values data_values lo hi Hlen Hlohi Hhi.
  apply (proj2 (list_eq_ext _ _ (heap_item 0 0))).
  split.
  - unfold pair_list.
    rewrite Zlength_combine_eq.
    + rewrite Zlength_sublist by lia.
      rewrite Zlength_sublist.
      * reflexivity.
      * rewrite Zlength_combine_eq by exact Hlen.
        lia.
    + rewrite !Zlength_sublist by lia.
      lia.
  - intros k Hk.
    unfold pair_list, heap_item in *.
    rewrite Zlength_combine_eq in Hk.
    2:{
      rewrite !Zlength_sublist by lia.
      lia.
    }
    rewrite Zlength_sublist in Hk by lia.
    rewrite
      (@Znth_combine_eq Z Z k
        (sublist lo hi key_values)
        (sublist lo hi data_values) 0 0).
    2:{
      rewrite Zlength_sublist by lia.
      lia.
    }
    2:{
      rewrite !Zlength_sublist by lia.
      lia.
    }
    rewrite Znth_sublist by lia.
    rewrite Znth_sublist by lia.
    rewrite Znth_sublist by lia.
    rewrite
      (@Znth_combine_eq Z Z (k + lo)
        key_values data_values 0 0).
    2:{ lia. }
    2:{ exact Hlen. }
    reflexivity.
Qed.

Lemma combine_replace_Znth_both :
  forall i key_values data_values key_x data_x,
    0 <= i < Zlength key_values ->
    Zlength key_values = Zlength data_values ->
    pair_list
      (replace_Znth i key_x key_values)
      (replace_Znth i data_x data_values) =
    replace_Znth i (heap_item key_x data_x)
      (pair_list key_values data_values).
Proof.
  intros i key_values data_values key_x data_x Hi Hlen.
  unfold pair_list, heap_item.
  assert
    (Hreplace_len :
      Zlength (replace_Znth i key_x key_values) =
      Zlength (replace_Znth i data_x data_values)).
  {
    rewrite !Zlength_replace_Znth.
    exact Hlen.
  }
  apply (proj2 (list_eq_ext _ _ (0, 0))).
  split.
  - rewrite Zlength_combine_eq.
    + rewrite Zlength_replace_Znth.
      rewrite Zlength_replace_Znth.
      rewrite Zlength_combine_eq by exact Hlen.
      reflexivity.
    + exact Hreplace_len.
  - intros k Hk.
    rewrite Zlength_combine_eq in Hk by exact Hreplace_len.
    assert (Hi_pair : 0 <= i < Zlength (combine key_values data_values)).
    {
      rewrite Zlength_combine_eq by exact Hlen.
      exact Hi.
    }
    rewrite Znth_combine_eq.
    2:{ exact Hk. }
    2:{ rewrite !Zlength_replace_Znth. exact Hlen. }
    destruct (Z.eq_dec k i) as [-> | Hki].
    + rewrite
        (@Znth_replace_Znth_Same
          (Z * Z) (0, 0) (combine key_values data_values)
          i (key_x, data_x)) by exact Hi_pair.
      rewrite (@Znth_replace_Znth_Same Z 0 key_values i key_x)
        by exact Hi.
      rewrite (@Znth_replace_Znth_Same Z 0 data_values i data_x)
        by (rewrite <- Hlen; exact Hi).
      reflexivity.
    + assert (Hk_orig : 0 <= k < Zlength key_values).
      {
        rewrite Zlength_replace_Znth in Hk.
        exact Hk.
      }
      assert
        (Hk_pair : 0 <= k < Zlength (combine key_values data_values)).
      {
        rewrite Zlength_combine_eq by exact Hlen.
        exact Hk_orig.
      }
      rewrite
        (@Znth_replace_Znth_Diff
          (Z * Z) (0, 0) (combine key_values data_values)
          i k (key_x, data_x))
        by (try exact Hi_pair; try exact Hk_pair; lia).
      rewrite (@Znth_replace_Znth_Diff Z 0 key_values i k key_x)
        by (try exact Hi; try exact Hk_orig; lia).
      rewrite (@Znth_replace_Znth_Diff Z 0 data_values i k data_x)
        by (try rewrite <- Hlen; try exact Hi; try exact Hk_orig; lia).
      rewrite Znth_combine_eq by lia.
      reflexivity.
Qed.

Lemma replace_Znth_swap_form :
  forall {A : Type} (l1 l2 l3 : list A) (xi xj : A),
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
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert
    (H0 :
      replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
      xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by (subst n2; lia).
  rewrite
    (replace_Znth_nothing (A := A)
      (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace
    (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with
    (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi)
    by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3)
    by reflexivity.
  rewrite H1.
  reflexivity.
Qed.

Lemma permutation_swap_Znth_lt :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d)
        (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hrange.
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
  rewrite replace_Znth_swap_form.
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

Lemma replace_nth_comm :
  forall {A : Type} ni nj (l : list A) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros A ni nj l a b Hneq.
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

Lemma replace_Znth_comm :
  forall {A : Type} (l : list A) i j (a b : A),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros A l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma permutation_swap_Znth :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d)
        (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_Znth_lt.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm by lia.
      apply permutation_swap_Znth_lt.
      lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma Znth_swap_Znth :
  forall {A : Type} (l : list A) i j (d : A),
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
  intros A l i j d Hi Hj Hneq.
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

Lemma pair_list_swap_Znth :
  forall key_values data_values i j,
    Zlength key_values = Zlength data_values ->
    0 <= i < Zlength key_values ->
    0 <= j < Zlength key_values ->
    Permutation
      (pair_list key_values data_values)
      (pair_list
        (replace_Znth j (Znth i key_values 0)
          (replace_Znth i (Znth j key_values 0) key_values))
        (replace_Znth j (Znth i data_values 0)
          (replace_Znth i (Znth j data_values 0) data_values))).
Proof.
  intros key_values data_values i j Hlen Hi Hj.
  rewrite combine_replace_Znth_both.
  2:{ rewrite Zlength_replace_Znth. lia. }
  2:{ rewrite !Zlength_replace_Znth. exact Hlen. }
  rewrite combine_replace_Znth_both.
  2:{ exact Hi. }
  2:{ exact Hlen. }
  replace (heap_item (Znth i key_values 0) (Znth i data_values 0))
    with (Znth i (pair_list key_values data_values) (heap_item 0 0)).
  2:{
    unfold pair_list, heap_item.
    rewrite (Znth_combine_eq i key_values data_values 0 0)
      by lia.
    reflexivity.
  }
  replace (heap_item (Znth j key_values 0) (Znth j data_values 0))
    with (Znth j (pair_list key_values data_values) (heap_item 0 0)).
  2:{
    unfold pair_list, heap_item.
    rewrite (Znth_combine_eq j key_values data_values 0 0)
      by lia.
    reflexivity.
  }
  apply permutation_swap_Znth.
  - unfold pair_list.
    rewrite Zlength_combine_eq by exact Hlen.
    exact Hi.
  - unfold pair_list.
    rewrite Zlength_combine_eq by exact Hlen.
    exact Hj.
Qed.

Lemma push_appended_source__push_initialization :
  forall (S : multiset (Z * Z))
    (key_base data_base : list Z) (size data_x key_x : Z),
    heap_representation S key_base data_base size ->
    PushSource
      (key_base ++ [key_x]) (data_base ++ [data_x])
      S size data_x key_x.
Proof.
  intros S key_base data_base size data_x key_x Hrep.
  destruct Hrep as
    [Hsize_nonneg
      [Hcapacity
        [Hmultiset_size
          [Hkey_length [Hdata_length [Hrelation Hordered]]]]]].
  unfold PushSource.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + split.
      * replace
        (pair_list (key_base ++ [key_x]) (data_base ++ [data_x]))
        with
        (pair_list key_base data_base ++ [heap_item key_x data_x]).
        2:{ symmetry. apply pair_list_app_single. lia. }
        eapply Permutation_trans.
        -- apply Permutation_app.
           ++ apply Permutation_sym.
              exact Hrelation.
           ++ apply Permutation_refl.
        -- exact (Permutation_app_comm (mlist S) [heap_item key_x data_x]).
      * replace
        (sublist 0 size (key_base ++ [key_x]))
        with key_base.
        -- exact Hordered.
        -- rewrite <- Hkey_length at 1.
           symmetry.
           apply sublist_app_exact1.
Qed.

Lemma push_appended_loop_state__push_initialization :
  forall (S : multiset (Z * Z))
    (key_base data_base : list Z) (size data_x key_x : Z),
    heap_representation S key_base data_base size ->
    PushLoopState
      (key_base ++ [key_x]) (data_base ++ [data_x])
      (key_base ++ [key_x]) (data_base ++ [data_x])
      size size data_x key_x.
Proof.
  intros S key_base data_base size data_x key_x Hrep.
  destruct Hrep as
    [Hsize_nonneg
      [Hcapacity
        [Hmultiset_size
          [Hkey_length [Hdata_length [Hrelation Hordered]]]]]].
  unfold PushLoopState.
  split; [exact Hsize_nonneg |].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil.
        lia.
      * split.
        -- rewrite Zlength_app, Zlength_cons, Zlength_nil.
           lia.
        -- split; [exact Hsize_nonneg |].
           split; [lia |].
           split.
           ++ rewrite app_Znth2 by lia.
              rewrite Hkey_length.
              replace (size - size) with 0 by lia.
              reflexivity.
           ++ split.
              ** rewrite app_Znth2 by lia.
                 rewrite Hdata_length.
                 replace (size - size) with 0 by lia.
                 reflexivity.
              ** split.
                 --- apply Permutation_refl.
                 --- split.
                     +++ unfold HeapOrderExceptUp.
                         split; [exact Hsize_nonneg |].
                         split; [lia |].
                         intros node
                           [Hnode_positive [Hnode_bound Hnode_not_hole]].
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
                         rewrite app_Znth1 by
                           (rewrite Hkey_length; lia).
                         rewrite app_Znth1 by
                           (rewrite Hkey_length; lia).
                         apply Hordered.
                         lia.
                     +++ unfold PushHoleChildrenPreserved.
                         intros node
                           [Hnode_positive [Hnode_bound Hparent_is_hole]].
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
  forall before key_written data_written key_current data_current
    size child parent data_x key_x,
    PushSource key_written data_written before size data_x key_x ->
    PushLoopState
      key_written data_written key_current data_current
      size child data_x key_x ->
    parent = heap_parent child ->
    Znth parent key_current 0 <= Znth child key_current 0 ->
    PushResult before key_current data_current size data_x key_x.
Proof.
  intros before key_written data_written key_current data_current
    size child parent data_x key_x
    Hsource Hloop Hparent Hdominates.
  unfold PushSource in Hsource.
  destruct Hsource as
    [Hkey_written_len
      [Hdata_written_len [Hsource_perm Hwritten_order]]].
  unfold PushLoopState in Hloop.
  destruct Hloop as
    (Hsize & Hkey_written_len' & Hdata_written_len' &
     Hkey_current_len & Hdata_current_len &
     Hchild_nonneg & Hchild_bound & Hchild_key &
     Hchild_data & Hwritten_current & Hexcept & Hchildren).
  unfold HeapOrderExceptUp in Hexcept.
  destruct Hexcept as [_ [_ Hexcept]].
  unfold PushResult.
  repeat split.
  - exact Hsize.
  - exact Hkey_current_len.
  - exact Hdata_current_len.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hwritten_current.
    + exact Hsource_perm.
  - unfold heap_ordered.
    intros node Hnode.
    destruct (Z.eq_dec node child) as [Heq | Hneq].
    + subst node. rewrite <- Hparent. exact Hdominates.
    + apply Hexcept. lia.
Qed.

Lemma push_swap_advances_loop__push_sift_up :
  forall key_written data_written key_current data_current
    size child parent data_x key_x,
    PushLoopState
      key_written data_written key_current data_current
      size child data_x key_x ->
    0 < child ->
    parent = heap_parent child ->
    Znth parent key_current 0 > Znth child key_current 0 ->
    let key_swapped :=
      replace_Znth child (Znth parent key_current 0)
        (replace_Znth parent (Znth child key_current 0) key_current) in
    let data_swapped :=
      replace_Znth child (Znth parent data_current 0)
        (replace_Znth parent (Znth child data_current 0) data_current) in
    Znth child key_swapped 0 = Znth parent key_current 0 /\
    Znth child data_swapped 0 = Znth parent data_current 0 /\
    PushLoopState
      key_written data_written key_swapped data_swapped
      size parent data_x key_x.
Proof.
  intros key_written data_written key_current data_current
    size child parent data_x key_x
    Hloop Hchild_pos Hparent Hstrict.
  unfold PushLoopState in Hloop.
  destruct Hloop as
    (Hsize & Hkey_written_len & Hdata_written_len &
     Hkey_current_len & Hdata_current_len &
     Hchild_nonneg & Hchild_bound & Hchild_key &
     Hchild_data & Hwritten_current & Hexcept & Hchildren).
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
  assert (Hparent_range_key : 0 <= parent < Zlength key_current)
    by lia.
  assert (Hchild_range_key : 0 <= child < Zlength key_current)
    by lia.
  assert (Hparent_range_data : 0 <= parent < Zlength data_current)
    by lia.
  assert (Hchild_range_data : 0 <= child < Zlength data_current)
    by lia.
  set
    (key_swapped :=
      replace_Znth child (Znth parent key_current 0)
        (replace_Znth parent (Znth child key_current 0) key_current)).
  set
    (data_swapped :=
      replace_Znth child (Znth parent data_current 0)
        (replace_Znth parent (Znth child data_current 0) data_current)).
  pose proof
    (Znth_swap_Znth
      key_current parent child 0
      Hparent_range_key Hchild_range_key Hparent_ne_child)
    as Hkey_swap.
  fold key_swapped in Hkey_swap.
  destruct Hkey_swap as [Hkey_swap_parent [Hkey_swap_child Hkey_swap_other]].
  pose proof
    (Znth_swap_Znth
      data_current parent child 0
      Hparent_range_data Hchild_range_data Hparent_ne_child)
    as Hdata_swap.
  fold data_swapped in Hdata_swap.
  destruct Hdata_swap as
    [Hdata_swap_parent [Hdata_swap_child Hdata_swap_other]].
  assert (Hkey_swapped_len : Zlength key_swapped = size + 1).
  {
    subst key_swapped.
    repeat rewrite Zlength_replace_Znth.
    exact Hkey_current_len.
  }
  assert (Hdata_swapped_len : Zlength data_swapped = size + 1).
  {
    subst data_swapped.
    repeat rewrite Zlength_replace_Znth.
    exact Hdata_current_len.
  }
  assert
    (Hwritten_swapped :
      Permutation
        (pair_list key_written data_written)
        (pair_list key_swapped data_swapped)).
  {
    eapply Permutation_trans.
    - exact Hwritten_current.
    - subst key_swapped data_swapped.
      apply pair_list_swap_Znth.
      + lia.
      + exact Hparent_range_key.
      + exact Hchild_range_key.
  }
  assert
    (Hnew_except :
      HeapOrderExceptUp key_swapped (size + 1) parent).
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
    assert (Hnode_range : 0 <= node < Zlength key_current) by lia.
    destruct (Z.eq_dec node child) as [Hnode_child | Hnode_ne_child].
    - subst node.
      rewrite <- Hparent.
      rewrite Hkey_swap_parent, Hkey_swap_child.
      lia.
    - assert
        (Hnode_same :
          Znth node key_swapped 0 = Znth node key_current 0).
      {
        apply Hkey_swap_other; try assumption.
      }
      assert
        (Hold :
          Znth (heap_parent node) key_current 0 <=
          Znth node key_current 0).
      {
        apply Hexcept.
        repeat split; assumption.
      }
      destruct
        (Z.eq_dec (heap_parent node) parent)
        as [Hnode_parent_eq | Hnode_parent_ne].
      + rewrite Hnode_parent_eq, Hkey_swap_parent, Hnode_same.
        rewrite Hnode_parent_eq in Hold.
        lia.
      + destruct
          (Z.eq_dec (heap_parent node) child)
          as [Hnode_parent_child | Hnode_parent_ne_child].
        * rewrite Hnode_parent_child, Hkey_swap_child, Hnode_same.
          assert
            (Hpreserved :
              Znth (heap_parent child) key_current 0 <=
              Znth node key_current 0).
          {
            apply Hchildren.
            repeat split; assumption.
          }
          rewrite <- Hparent in Hpreserved.
          exact Hpreserved.
        * assert
            (Hnode_parent_same :
              Znth (heap_parent node) key_swapped 0 =
              Znth (heap_parent node) key_current 0).
          {
            apply Hkey_swap_other; try assumption.
            lia.
          }
          rewrite Hnode_parent_same, Hnode_same.
          exact Hold.
  }
  assert
    (Hnew_children :
      PushHoleChildrenPreserved key_swapped (size + 1) parent).
  {
    unfold PushHoleChildrenPreserved.
    intros node [Hnode_pos [Hnode_lt Hnode_parent]].
    pose proof
      (heap_parent_positive_bounds__push_sift_up
        node size Hnode_pos ltac:(lia))
      as [Hnode_parent_nonneg
        [Hnode_parent_lt Hnode_parent_bound]].
    assert (Hnode_range : 0 <= node < Zlength key_current) by lia.
    destruct (Z.eq_dec parent 0) as [Hparent_zero | Hparent_nonzero].
    - rewrite Hparent_zero in Hkey_swap_parent, Hkey_swap_child, Hstrict.
      rewrite Hparent_zero.
      destruct (Z.eq_dec node child) as [Hnode_child | Hnode_ne_child].
      + rewrite Hnode_child.
        change (Znth 0 key_swapped 0 <= Znth child key_swapped 0).
        rewrite Hkey_swap_parent, Hkey_swap_child.
        lia.
      + assert (Hnode_ne_parent : node <> parent) by lia.
        assert
          (Hnode_same :
            Znth node key_swapped 0 = Znth node key_current 0).
        {
          apply Hkey_swap_other; try assumption.
        }
        assert
          (Hold :
            Znth (heap_parent node) key_current 0 <=
            Znth node key_current 0).
        {
          apply Hexcept.
          repeat split; assumption.
        }
        rewrite Hnode_parent, Hparent_zero in Hold.
        change (Znth 0 key_swapped 0 <= Znth node key_swapped 0).
        rewrite Hkey_swap_parent, Hnode_same.
        lia.
    - assert (Hparent_pos : 0 < parent) by lia.
      pose proof
        (heap_parent_positive_bounds__push_sift_up
          parent size Hparent_pos Hparent_bound)
        as [Hgrand_nonneg [Hgrand_lt Hgrand_bound]].
      assert
        (Hgrand_same :
          Znth (heap_parent parent) key_swapped 0 =
          Znth (heap_parent parent) key_current 0).
      {
        apply Hkey_swap_other.
        - lia.
        - lia.
        - lia.
      }
      assert
        (Hparent_order :
          Znth (heap_parent parent) key_current 0 <=
          Znth parent key_current 0).
      {
        apply Hexcept.
        repeat split; try lia.
      }
      destruct (Z.eq_dec node child) as [Hnode_child | Hnode_ne_child].
      + subst node.
        rewrite Hgrand_same, Hkey_swap_child.
        exact Hparent_order.
      + assert (Hnode_ne_parent : node <> parent) by lia.
        assert
          (Hnode_same :
            Znth node key_swapped 0 = Znth node key_current 0).
        {
          apply Hkey_swap_other; try assumption.
        }
        assert
          (Hnode_order :
            Znth (heap_parent node) key_current 0 <=
            Znth node key_current 0).
        {
          apply Hexcept.
          repeat split; assumption.
        }
        rewrite Hnode_parent in Hnode_order.
        rewrite Hgrand_same, Hnode_same.
        lia.
  }
  split.
  - exact Hkey_swap_child.
  - split.
    + exact Hdata_swap_child.
    + unfold PushLoopState.
    split; [exact Hsize |].
    split; [exact Hkey_written_len |].
    split; [exact Hdata_written_len |].
    split; [exact Hkey_swapped_len |].
    split; [exact Hdata_swapped_len |].
    split; [exact Hparent_nonneg |].
    split; [exact Hparent_bound |].
    split.
    * rewrite Hkey_swap_parent.
      exact Hchild_key.
    * split.
      -- rewrite Hdata_swap_parent.
        exact Hchild_data.
      -- split; [exact Hwritten_swapped |].
        split; [exact Hnew_except | exact Hnew_children].
Qed.

Lemma push_zero_exit_result__push_finalization :
  forall before key_written data_written key_current data_current
    size data_x key_x,
    PushSource key_written data_written before size data_x key_x ->
    PushLoopState
      key_written data_written key_current data_current
      size 0 data_x key_x ->
    PushResult before key_current data_current size data_x key_x.
Proof.
  intros before key_written data_written key_current data_current
    size data_x key_x Hsource Hloop.
  destruct Hsource as
    (Hkey_written_len & Hdata_written_len & Hsource_perm & _).
  destruct Hloop as
    (Hsize & _ & _ & Hkey_current_len & Hdata_current_len &
     _ & _ & _ & _ & Hwritten_current & Hexcept & _).
  unfold PushResult.
  repeat split.
  - exact Hsize.
  - exact Hkey_current_len.
  - exact Hdata_current_len.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hwritten_current.
    + exact Hsource_perm.
  - unfold HeapOrderExceptUp in Hexcept.
    destruct Hexcept as [_ [_ Hordered]].
    unfold heap_ordered.
    intros child [Hchild_positive Hchild_bound].
    apply Hordered.
    repeat split; lia.
Qed.

Lemma push_result_representation__push_finalization :
  forall before key_result data_result size data_x key_x,
    size < heap_capacity ->
    PushResult before key_result data_result size data_x key_x ->
    heap_representation
      (multiset_insert before (heap_item key_x data_x))
      key_result data_result (size + 1).
Proof.
  intros before key_result data_result size data_x key_x Hcapacity Hresult.
  destruct Hresult as
    [Hsize [Hkey_length [Hdata_length [Hperm Hordered]]]].
  unfold heap_representation.
  repeat split.
  - lia.
  - lia.
  - unfold multiset_size, multiset_insert. simpl.
    rewrite <- Hkey_length.
    unfold pair_list in Hperm.
    pose proof (Permutation_length Hperm) as Hlen.
    rewrite !Zlength_correct.
    assert
      (Hcombine_key_len :
        length (combine key_result data_result) = length key_result).
    {
      rewrite length_combine.
      apply Nat.min_l.
      apply Nat2Z.inj_le.
      rewrite <- !Zlength_correct.
      lia.
    }
    assert
      (Hnat :
        length (heap_item key_x data_x :: mlist before) =
        length key_result).
    {
      rewrite <- Hcombine_key_len.
      symmetry.
      exact Hlen.
    }
    now rewrite Hnat.
  - exact Hkey_length.
  - exact Hdata_length.
  - unfold heap_relation. simpl.
    apply Permutation_sym. exact Hperm.
  - exact Hordered.
Qed.

Lemma build_initial_prefix__build_progress :
  forall (key_input data_input : list Z) n,
    Zlength key_input = n ->
    Zlength data_input = n ->
    1 <= n ->
    BuildPrefixState
      (list_to_multiset
        [heap_item (Znth 0 key_input 0) (Znth 0 data_input 0)])
      key_input data_input 1 /\
    heap_representation
      (list_to_multiset
        [heap_item (Znth 0 key_input 0) (Znth 0 data_input 0)])
      (sublist 0 1 key_input)
      (sublist 0 1 data_input)
      1.
Proof.
  intros key_input data_input n Hkey_len Hdata_len Hpositive.
  assert (Hkey_single :
    sublist 0 1 key_input = [Znth 0 key_input 0]).
  {
    apply (sublist_single 0 0 key_input).
    lia.
  }
  assert (Hdata_single :
    sublist 0 1 data_input = [Znth 0 data_input 0]).
  {
    apply (sublist_single 0 0 data_input).
    lia.
  }
  split.
  - unfold BuildPrefixState, multiset_equiv.
    repeat split; try lia.
    simpl.
    rewrite Hkey_single, Hdata_single.
    apply Permutation_refl.
  - unfold heap_representation.
    repeat split.
    + lia.
    + unfold heap_capacity; lia.
    + rewrite Hkey_single.
      reflexivity.
    + rewrite Hdata_single.
      reflexivity.
    + unfold heap_relation.
      simpl.
      rewrite Hkey_single, Hdata_single.
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
  2:{
    rewrite Zsublist_Zsublist by lia.
    f_equal; lia.
  }
  entailer!.
Qed.

Lemma build_append_next_cell__build_progress :
  forall heap i n (prefix input : list Z),
    0 <= i < n ->
    Zlength prefix = i ->
    n <= Zlength input ->
    IntArray.full heap i prefix **
    IntArray.seg heap i n (sublist i n input)
    |--
      IntArray.full heap (i + 1)
        (prefix ++ [Znth i input 0]) **
      IntArray.seg heap (i + 1) n (sublist (i + 1) n input).
Proof.
  intros heap i n prefix input Hirange Hprefix_len Hinput_len.
  sep_apply (IntArray.full_to_seg heap i prefix).
  sep_apply
    (IntArray.seg_split_to_seg
      heap i (i + 1) n (sublist i n input));
    try lia.
  replace
    (sublist 0 (i + 1 - i) (sublist i n input))
    with [Znth i input 0].
  2:{
    replace (i + 1 - i) with 1 by lia.
    rewrite Zsublist_Zsublist by lia.
    replace (0 + i) with i by lia.
    replace (1 + i) with (i + 1) by lia.
    symmetry.
    apply sublist_single.
    lia.
  }
  replace
    (sublist (i + 1 - i) (n - i) (sublist i n input))
    with (sublist (i + 1) n input).
  2:{
    rewrite Zsublist_Zsublist by lia.
    f_equal; lia.
  }
  sep_apply
    (IntArray.seg_merge_to_seg
      heap 0 i (i + 1) prefix [Znth i input 0]);
    try lia.
  sep_apply
    (IntArray.seg_to_full
      heap 0 (i + 1) (prefix ++ [Znth i input 0])).
  replace (heap + 0 * sizeof(INT)) with heap by lia.
  replace (i + 1 - 0) with (i + 1) by lia.
  entailer!.
  all:
    try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
    try (rewrite Zlength_sublist by lia; lia);
    try cancel.
Qed.

Lemma build_prefix_extend__build_progress :
  forall (prefix : multiset (Z * Z))
    (key_input data_input : list Z) i data_x key_x,
    1 <= i ->
    i < Zlength key_input ->
    Zlength key_input = Zlength data_input ->
    data_x = Znth i data_input 0 ->
    key_x = Znth i key_input 0 ->
    BuildPrefixState prefix key_input data_input i ->
    BuildPrefixState
      (multiset_insert prefix (heap_item key_x data_x))
      key_input data_input (i + 1).
Proof.
  intros prefix key_input data_input i data_x key_x
    Hi Hbound Hlen Hdata Hkey Hprefix.
  unfold BuildPrefixState in *.
  destruct Hprefix as [Hone [Hprocessed_key [Hprocessed_data Hperm]]].
  repeat split; try lia.
  unfold multiset_equiv, multiset_insert in *.
  simpl in *.
  rewrite pair_list_sublist_snoc by lia.
  subst data_x key_x.
  eapply Permutation_trans.
  - apply perm_skip.
    exact Hperm.
  - apply Permutation_cons_append.
Qed.

Lemma store_heap_equiv_transport__build_finalization :
  forall S1 S2 key_values data_values size,
    multiset_equiv S1 S2 ->
    heap_representation S1 key_values data_values size ->
    heap_representation S2 key_values data_values size.
Proof.
  intros S1 S2 key_values data_values size Hequiv Hrep.
  unfold heap_representation in *.
  destruct Hrep as
    [Hnonneg [Hcapacity [Hsize
      [Hkey_length [Hdata_length [Hrelation Hordered]]]]]].
  repeat split; try assumption.
  - pose proof
      (multiset_equiv_size (Z * Z) S1 S2 Hequiv)
      as Hsize_equiv.
    lia.
  - unfold multiset_equiv in Hequiv.
    unfold heap_relation in *.
    eapply Permutation_trans.
    + apply Permutation_sym. exact Hequiv.
    + exact Hrelation.
Qed.

Lemma build_prefix_complete__build_finalization :
  forall prefix key_input data_input processed,
    BuildPrefixState prefix key_input data_input processed ->
    processed = Zlength key_input ->
    Zlength key_input = Zlength data_input ->
    multiset_equiv
      prefix
      (list_to_multiset (pair_list key_input data_input)).
Proof.
  intros prefix key_input data_input processed
    Hprefix Hcomplete Hlen.
  subst processed.
  unfold BuildPrefixState in Hprefix.
  destruct Hprefix as [_ [_ [_ Hprefix]]].
  rewrite (pair_list_sublist_self
    key_input data_input (Zlength key_input)) in Hprefix by lia.
  exact Hprefix.
Qed.

Lemma In_Znth_Zlength :
  forall {A : Type} (l : list A) (x d : A),
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  destruct (In_nth l x d Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.

Lemma heap_ordered_root_lower_bound__pop_initialization :
  forall key_values size index,
    heap_ordered key_values size ->
    0 <= index < size ->
    Znth 0 key_values 0 <= Znth index key_values 0.
Proof.
  intros key_values size index Hordered Hindex.
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
    eapply Z.le_trans.
    + exact IH.
    + exact Hedge.
Qed.

Lemma heap_root_is_multiset_minimum__pop_initialization :
  forall S key_values data_values size,
    1 <= size ->
    heap_representation S key_values data_values size ->
    let item :=
      heap_item (Znth 0 key_values 0) (Znth 0 data_values 0) in
    PrefixMinimum key_values data_values size item /\
    multiset_minimum S item.
Proof.
  intros S key_values data_values size Hsize Hrepresentation.
  destruct Hrepresentation as
    [Hsize_nonneg
      [Hcapacity
        [Hmultiset_size
          [Hkey_length [Hdata_length [Hrelation Hordered]]]]]].
  set (item :=
    heap_item (Znth 0 key_values 0) (Znth 0 data_values 0)).
  assert (Hroot_bound :
    forall index,
      0 <= index < size ->
      item_key item <= Znth index key_values 0).
  {
    subst item.
    simpl.
    intros index Hindex.
    eapply heap_ordered_root_lower_bound__pop_initialization;
      eauto.
  }
  assert (Hpair_split :
    pair_list key_values data_values =
      item ::
      pair_list
        (sublist 1 size key_values)
        (sublist 1 size data_values)).
  {
    subst item.
    apply pair_list_cons_split; lia.
  }
  assert (Hroot_in_multiset : In item (mlist S)).
  {
    eapply Permutation_in.
    - apply Permutation_sym. exact Hrelation.
    - rewrite Hpair_split. now left.
  }
  split.
  - unfold PrefixMinimum.
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split.
    + subst item. reflexivity.
    + intros i Hi. now apply Hroot_bound.
  - unfold multiset_minimum.
    split.
    + exact Hroot_in_multiset.
    + intros x Hx.
      assert (Hx_pair : In x (pair_list key_values data_values)).
      {
        eapply Permutation_in.
        - exact Hrelation.
        - exact Hx.
      }
      destruct
        (In_Znth_Zlength
          (pair_list key_values data_values) x (heap_item 0 0)
          Hx_pair) as [i [Hi Hxi]].
      unfold pair_list in Hi.
      rewrite Zlength_combine_eq in Hi by lia.
      rewrite <- Hxi.
      unfold pair_list, item_key, heap_item.
      rewrite (@Znth_combine_eq Z Z i key_values data_values 0 0)
        by lia.
      simpl.
      apply Hroot_bound.
      lia.
Qed.

Lemma pop_root_replacement_remaining_permutation__pop_initialization :
  forall {A : Type} (before : list A) size (d : A),
    1 < size ->
    Zlength before = size ->
    Permutation
      (sublist 0 (size - 1)
        (replace_Znth 0 (Znth (size - 1) before d) before))
      (sublist 1 size before).
Proof.
  intros A before size d Hsize Hlength.
  destruct before as [|head tail].
  - rewrite Zlength_nil in Hlength. lia.
  - rewrite Zlength_cons in Hlength.
    change
      (Permutation
        (sublist 0 (size - 1)
          (Znth (size - 1) (head :: tail) d :: tail))
        (sublist 1 size (head :: tail))).
    rewrite Znth_cons by lia.
    rewrite sublist_cons1 by lia.
    rewrite sublist_cons2 by (rewrite ?Zlength_cons; lia).
    replace (1 - 1) with 0 by lia.
    replace (size - 1 - 1) with (size - 2) by lia.
    rewrite (sublist_split 0 (size - 1) (size - 2) tail) by lia.
    replace (size - 1) with (size - 2 + 1) by lia.
    rewrite (@sublist_single A d (size - 2) tail) by lia.
    change
      (Permutation
        ((Znth (size - 2) tail d :: nil) ++
          sublist 0 (size - 2) tail)
        (sublist 0 (size - 2) tail ++
          (Znth (size - 2) tail d :: nil))).
    apply Permutation_app_comm.
Qed.

Lemma pop_root_replacement_pair_remaining_permutation__pop_initialization :
  forall before_key before_data size,
    1 < size ->
    Zlength before_key = size ->
    Zlength before_data = size ->
    Permutation
      (pair_list
        (sublist 0 (size - 1)
          (replace_Znth 0 (Znth (size - 1) before_key 0) before_key))
        (sublist 0 (size - 1)
          (replace_Znth 0 (Znth (size - 1) before_data 0) before_data)))
      (pair_list
        (sublist 1 size before_key)
        (sublist 1 size before_data)).
Proof.
  intros before_key before_data size Hsize Hkey Hdata.
  rewrite pair_list_sublist.
  2:{ rewrite !Zlength_replace_Znth. lia. }
  2:{ lia. }
  2:{ rewrite Zlength_replace_Znth. lia. }
  rewrite pair_list_sublist by lia.
  rewrite combine_replace_Znth_both by lia.
  replace (heap_item
    (Znth (size - 1) before_key 0)
    (Znth (size - 1) before_data 0))
    with
      (Znth (size - 1) (pair_list before_key before_data)
        (heap_item 0 0)).
  2:{
    unfold pair_list, heap_item.
    rewrite Znth_combine_eq by lia.
    reflexivity.
  }
  apply pop_root_replacement_remaining_permutation__pop_initialization.
  - exact Hsize.
  - unfold pair_list.
    rewrite Zlength_combine_eq by lia.
    exact Hkey.
Qed.

Lemma pop_root_replacement_loop_state__pop_initialization :
  forall before_key before_data size,
    1 < size ->
    Zlength before_key = size ->
    Zlength before_data = size ->
    heap_ordered before_key size ->
    PopLoopState before_key before_data
      (replace_Znth 0 (Znth (size - 1) before_key 0) before_key)
      (replace_Znth 0 (Znth (size - 1) before_data 0) before_data)
      size 0.
Proof.
  intros before_key before_data size Hsize Hkey Hdata Hordered.
  unfold PopLoopState.
  repeat split; try lia; try assumption;
    try (rewrite Zlength_replace_Znth; lia).
  - rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - unfold PopRemainingElements.
    repeat split; try lia;
      try (rewrite Zlength_replace_Znth; lia).
    now apply
      pop_root_replacement_pair_remaining_permutation__pop_initialization.
  - unfold HeapOrderExceptDown.
    repeat split; try lia.
    intros child [Hchild_pos [Hchild_bound Hparent_not_root]].
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
    pose proof (Hordered child ltac:(lia)) as Hedge.
    rewrite Znth_replace_Znth_Diff by
      (rewrite ?Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by
      (rewrite ?Zlength_replace_Znth; lia).
    exact Hedge.
  - unfold PopHoleParentDominatesChildren.
    left. reflexivity.
Qed.

Lemma remove_minimum_singleton_empty__pop_singleton :
  forall (S : multiset (Z * Z)) item,
    multiset_size S = 1 ->
    multiset_minimum S item ->
    mlist (multiset_remove S item) = [].
Proof.
  intros S item Hsize Hminimum.
  destruct Hminimum as [Hin _].
  destruct (proj1 (multiset_remove_spec S item) Hin)
    as [Hremove_size _].
  unfold multiset_size in Hsize, Hremove_size.
  apply Zlength_nil_inv.
  lia.
Qed.

Lemma singleton_full_split_spare__pop_singleton :
  forall (p : Z) (before : list Z),
    Zlength before = 1 ->
    IntArray.full p 1 before |--
      IntArray.full p 0 [] ** IntArray.undef_seg p 0 1.
Proof.
  intros p before Hlength.
  destruct before as [|a before].
  - rewrite Zlength_nil in Hlength. lia.
  - destruct before as [|b before].
    + unfold heap_spare.
      rewrite IntArray.full_empty.
      sep_apply IntArray.full_to_seg.
      sep_apply IntArray.seg_to_undef_seg.
      entailer!.
    + rewrite !Zlength_cons in Hlength.
      pose proof (Zlength_nonneg before).
      lia.
Qed.

Lemma singleton_store_heap_after_remove__pop_singleton :
  forall key data S before_key before_data item,
    heap_representation S before_key before_data 1 ->
    multiset_minimum S item ->
    IntArray.full key 1 before_key **
    IntArray.undef_seg key 1 heap_capacity **
    IntArray.full data 1 before_data **
    IntArray.undef_seg data 1 heap_capacity |--
      store_heap key data (multiset_remove S item) 0.
Proof.
  intros key data S before_key before_data item Hrep Hminimum.
  destruct Hrep as
    [Hnonneg [Hcapacity [Hsize
      [Hkey_length [Hdata_length [Hrelation Hordered]]]]]].
  assert (Hremoved_nil :
    mlist (multiset_remove S item) = []).
  {
    eapply remove_minimum_singleton_empty__pop_singleton;
      eauto.
  }
  assert (Hremoved_rep :
    heap_representation (multiset_remove S item) [] [] 0).
  {
    unfold heap_representation, heap_relation, multiset_size.
    repeat split; try lia.
    - rewrite Hremoved_nil. reflexivity.
    - rewrite Hremoved_nil. simpl. apply Permutation_refl.
    - unfold heap_ordered. intros child Hchild. lia.
  }
  unfold store_heap.
  Exists (@nil Z).
  Exists (@nil Z).
  unfold heap_tail.
  destruct (Z_lt_dec 0 heap_capacity) as [_ | Hnot].
  2:{ unfold heap_capacity in Hnot. lia. }
  sep_apply_l_atomic
    (singleton_full_split_spare__pop_singleton
      key before_key Hkey_length).
  sep_apply_l_atomic
    (singleton_full_split_spare__pop_singleton
      data before_data Hdata_length).
  unfold heap_spare.
  replace (0 + 1) with 1 by lia.
  entailer!.
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
     Znth (heap_left_child index) current 0 <=
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
    destruct (Z_lt_dec (heap_right_child index) size)
      as [Hright | Hright].
    + destruct Hselect as [Houtside | Hvalues]; [lia |].
      destruct
        (Z.leb
          (Znth (heap_left_child index) current 0)
          (Znth (heap_right_child index) current 0)) eqn:Hcmp.
      * reflexivity.
      * apply Z.leb_gt in Hcmp. lia.
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
    Znth (heap_right_child index) current 0 <
      Znth (heap_left_child index) current 0 ->
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
      (Z.leb
        (Znth (heap_left_child index) current 0)
        (Znth (heap_right_child index) current 0)) eqn:Hcmp.
    + apply Z.leb_le in Hcmp. lia.
    + reflexivity.
  - intros child [Hchild_pos [Hchild_bound Hparent]].
    pose proof
      (heap_children_characterization__pop_child_selection
        index child Hindex Hchild_pos Hparent)
      as [-> | ->];
      lia.
Qed.

Lemma pop_comparison_ready__pop_ready_exit :
  forall before_key before_data current_key current_data
    size item index selected,
    PrefixMinimum before_key before_data size item ->
    PopLoopState before_key before_data current_key current_data
      size index ->
    PopSelectedChild current_key (size - 1) index selected ->
    Znth index current_key 0 <= Znth selected current_key 0 ->
    PopReadyState before_key before_data current_key current_data
      size item.
Proof.
  intros before_key before_data current_key current_data
    size item index selected
    Hminimum Hloop Hselected Hdominates.
  unfold PopLoopState in Hloop.
  destruct Hloop as
    (Hsize & Hbefore_key_length & Hbefore_data_length &
     Hcurrent_key_length & Hcurrent_data_length &
     Hindex_nonnegative & Hindex_bound & Hbefore_ordered &
     Hhole_key & Hhole_data & Hremaining &
     Hexcept & Hparent_dominates).
  assert (Hcurrent_ordered : heap_ordered current_key (size - 1)).
  {
    unfold heap_ordered.
    intros child Hchild.
    unfold HeapOrderExceptDown in Hexcept.
    destruct Hexcept as (_ & _ & Hordered).
    destruct (Z.eq_dec (heap_parent child) index)
      as [Hparent | Hparent].
    + unfold PopSelectedChild in Hselected.
      destruct Hselected as
        (_ & _ & _ & _ & _ & _ & _ & Hselected_dominates).
      specialize (Hselected_dominates child ltac:(tauto)).
      rewrite Hparent.
      eapply Z.le_trans.
      * exact Hdominates.
      * exact Hselected_dominates.
    + apply Hordered.
      tauto.
  }
  unfold PopReadyState.
  split; [exact Hsize |].
  split; [exact Hbefore_key_length |].
  split; [exact Hbefore_data_length |].
  split; [exact Hcurrent_key_length |].
  split; [exact Hcurrent_data_length |].
  split; [exact Hbefore_ordered |].
  split; [exact Hminimum |].
  split; [exact Hremaining | exact Hcurrent_ordered].
Qed.

Lemma pop_leaf_ready__pop_ready_exit :
  forall before_key before_data current_key current_data
    size item index,
    PrefixMinimum before_key before_data size item ->
    PopLoopState before_key before_data current_key current_data
      size index ->
    heap_left_child index >= size - 1 ->
    PopReadyState before_key before_data current_key current_data
      size item.
Proof.
  intros before_key before_data current_key current_data
    size item index Hminimum Hloop Hleft_outside.
  unfold PopLoopState in Hloop.
  destruct Hloop as
    (Hsize & Hbefore_key_length & Hbefore_data_length &
     Hcurrent_key_length & Hcurrent_data_length &
     Hindex_nonnegative & Hindex_bound & Hbefore_ordered &
     Hhole_key & Hhole_data & Hremaining &
     Hexcept & Hparent_dominates).
  assert (Hcurrent_ordered : heap_ordered current_key (size - 1)).
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
  split; [exact Hsize |].
  split; [exact Hbefore_key_length |].
  split; [exact Hbefore_data_length |].
  split; [exact Hcurrent_key_length |].
  split; [exact Hcurrent_data_length |].
  split; [exact Hbefore_ordered |].
  split; [exact Hminimum |].
  split; [exact Hremaining | exact Hcurrent_ordered].
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
  destruct (Z_lt_dec (index * 2 + 2) size)
    as [Hright | Hright].
  - destruct
      (Z.leb
        (Znth (index * 2 + 1) current 0)
        (Znth (index * 2 + 2) current 0));
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
  forall before_key before_data current_key current_data
    size index selected,
    PopLoopState before_key before_data current_key current_data
      size index ->
    PopSelectedChild current_key (size - 1) index selected ->
    Znth index current_key 0 > Znth selected current_key 0 ->
    let key_swapped :=
      replace_Znth selected (Znth index current_key 0)
        (replace_Znth index (Znth selected current_key 0)
          current_key) in
    let data_swapped :=
      replace_Znth selected (Znth index current_data 0)
        (replace_Znth index (Znth selected current_data 0)
          current_data) in
    Znth index current_key 0 = Znth selected key_swapped 0 /\
    Znth index current_data 0 = Znth selected data_swapped 0 /\
    PopLoopState before_key before_data key_swapped data_swapped
      size selected.
Proof.
  intros before_key before_data current_key current_data
    size index selected Hloop Hselected Hgt.
  unfold PopLoopState in Hloop.
  destruct Hloop as
    (Hsize & Hbefore_key_len & Hbefore_data_len &
     Hcurrent_key_len & Hcurrent_data_len &
     Hindex_nonneg & Hindex_bound & Hbefore_ordered &
     Hindex_key & Hindex_data & Hremaining &
     Hexcept & Hparent_hole).
  unfold PopSelectedChild in Hselected.
  destruct Hselected as
    (Hselected_index_nonneg & Hselected_index_bound &
     Hindex_selected & Hselected_nonneg & Hselected_bound &
     Hselected_parent & Hselected_choice & Hselected_dominates).
  set
    (key_swapped :=
      replace_Znth selected (Znth index current_key 0)
        (replace_Znth index (Znth selected current_key 0)
          current_key)).
  set
    (data_swapped :=
      replace_Znth selected (Znth index current_data 0)
        (replace_Znth index (Znth selected current_data 0)
          current_data)).
  assert (Hindex_current_key : 0 <= index < Zlength current_key)
    by (rewrite Hcurrent_key_len; lia).
  assert (Hselected_current_key : 0 <= selected < Zlength current_key)
    by (rewrite Hcurrent_key_len; lia).
  assert (Hindex_current_data : 0 <= index < Zlength current_data)
    by (rewrite Hcurrent_data_len; lia).
  assert (Hselected_current_data : 0 <= selected < Zlength current_data)
    by (rewrite Hcurrent_data_len; lia).
  assert (Hindex_ne_selected : index <> selected) by lia.
  pose proof
    (Znth_swap_Znth
      current_key index selected 0
      Hindex_current_key Hselected_current_key Hindex_ne_selected)
    as Hkey_swap.
  fold key_swapped in Hkey_swap.
  destruct Hkey_swap as
    [Hkey_swap_index [Hkey_swap_selected Hkey_swap_other]].
  pose proof
    (Znth_swap_Znth
      current_data index selected 0
      Hindex_current_data Hselected_current_data Hindex_ne_selected)
    as Hdata_swap.
  fold data_swapped in Hdata_swap.
  destruct Hdata_swap as
    [Hdata_swap_index [Hdata_swap_selected Hdata_swap_other]].
  assert (Hkey_swapped_len : Zlength key_swapped = size).
  {
    subst key_swapped.
    repeat rewrite Zlength_replace_Znth.
    exact Hcurrent_key_len.
  }
  assert (Hdata_swapped_len : Zlength data_swapped = size).
  {
    subst data_swapped.
    repeat rewrite Zlength_replace_Znth.
    exact Hcurrent_data_len.
  }
  split.
  - symmetry. exact Hkey_swap_selected.
  - split.
    + symmetry. exact Hdata_swap_selected.
    + unfold PopLoopState.
      split; [exact Hsize |].
      split; [exact Hbefore_key_len |].
      split; [exact Hbefore_data_len |].
      split; [exact Hkey_swapped_len |].
      split; [exact Hdata_swapped_len |].
      split; [exact Hselected_nonneg |].
      split; [exact Hselected_bound |].
      split; [exact Hbefore_ordered |].
      split.
      * rewrite Hkey_swap_selected.
        exact Hindex_key.
      * split.
        -- rewrite Hdata_swap_selected.
           exact Hindex_data.
        -- split.
           ++ unfold PopRemainingElements in Hremaining |- *.
              destruct Hremaining as
                (Hremaining_size & Hremaining_before_key &
                 Hremaining_before_data & Hremaining_current_key &
                 Hremaining_current_data & Hremaining_perm).
              repeat split; try lia;
                try (rewrite Hkey_swapped_len; lia);
                try (rewrite Hdata_swapped_len; lia).
              assert (Hprefix_key :
                sublist 0 (size - 1) key_swapped =
                replace_Znth selected (Znth index current_key 0)
                  (replace_Znth index (Znth selected current_key 0)
                    (sublist 0 (size - 1) current_key))).
              {
                unfold key_swapped.
                rewrite
                  sublist0_replace_Znth_inside__pop_swap_transition
                  by (rewrite ?Zlength_replace_Znth,
                        ?Hcurrent_key_len; lia).
                rewrite
                  sublist0_replace_Znth_inside__pop_swap_transition
                  by (rewrite ?Hcurrent_key_len; lia).
                reflexivity.
              }
              assert (Hprefix_data :
                sublist 0 (size - 1) data_swapped =
                replace_Znth selected (Znth index current_data 0)
                  (replace_Znth index (Znth selected current_data 0)
                    (sublist 0 (size - 1) current_data))).
              {
                unfold data_swapped.
                rewrite
                  sublist0_replace_Znth_inside__pop_swap_transition
                  by (rewrite ?Zlength_replace_Znth,
                        ?Hcurrent_data_len; lia).
                rewrite
                  sublist0_replace_Znth_inside__pop_swap_transition
                  by (rewrite ?Hcurrent_data_len; lia).
                reflexivity.
              }
              rewrite Hprefix_key, Hprefix_data.
              eapply Permutation_trans.
              ** apply Permutation_sym.
                 replace (Znth index current_key 0)
                   with
                   (Znth index
                     (sublist 0 (size - 1) current_key) 0).
                 2:{
                   rewrite Znth_sublist0 by lia.
                   reflexivity.
                 }
                 replace (Znth selected current_key 0)
                   with
                   (Znth selected
                     (sublist 0 (size - 1) current_key) 0).
                 2:{
                   rewrite Znth_sublist0 by lia.
                   reflexivity.
                 }
                 replace (Znth index current_data 0)
                   with
                   (Znth index
                     (sublist 0 (size - 1) current_data) 0).
                 2:{
                   rewrite Znth_sublist0 by lia.
                   reflexivity.
                 }
                 replace (Znth selected current_data 0)
                   with
                   (Znth selected
                     (sublist 0 (size - 1) current_data) 0).
                 2:{
                   rewrite Znth_sublist0 by lia.
                   reflexivity.
                 }
                 apply pair_list_swap_Znth.
                 --- rewrite !Zlength_sublist0 by lia.
                     lia.
                 --- rewrite Zlength_sublist0 by lia.
                     lia.
                 --- rewrite Zlength_sublist0 by lia.
                     lia.
              ** exact Hremaining_perm.
           ++ split.
              ** unfold HeapOrderExceptDown in Hexcept.
                 destruct Hexcept as
                   [Hexcept_index_nonneg
                     [Hexcept_index_bound Hexcept_edges]].
                 unfold HeapOrderExceptDown.
                 repeat split; try assumption.
                 intros child
                   [Hchild_pos [Hchild_bound Hchild_parent_not_selected]].
                 pose proof
                   (heap_parent_nonnegative_lt__pop_swap_transition
                     child Hchild_pos)
                   as Hparent_bounds.
                 destruct
                   (Z.eq_dec (heap_parent child) index)
                   as [Hparent_index | Hparent_not_index].
                 {
                   destruct (Z.eq_dec child selected)
                       as [Hchild_selected | Hchild_not_selected].
                   {
                     subst child.
                     rewrite Hparent_index.
                     rewrite Hkey_swap_index, Hkey_swap_selected.
                     lia.
                   }
                   {
                     assert (Hchild_not_index : child <> index) by lia.
                     rewrite Hparent_index.
                     rewrite Hkey_swap_index.
                     rewrite Hkey_swap_other by
                       (rewrite ?Hcurrent_key_len; lia).
                     apply Hselected_dominates.
                     repeat split; assumption.
                   }
                 }
                 {
                   destruct (Z.eq_dec child index)
                       as [Hchild_index | Hchild_not_index].
                   {
                     subst child.
                     rewrite Hkey_swap_other by
                       (rewrite ?Hcurrent_key_len; lia).
                     rewrite Hkey_swap_index.
                     destruct Hparent_hole as
                       [Hindex_zero | Hparent_dominates].
                     {
                       lia.
                     }
                     {
                       apply Hparent_dominates.
                       repeat split.
                       - lia.
                       - exact Hselected_bound.
                       - exact Hselected_parent.
                     }
                   }
                   {
                     assert (Hchild_not_selected : child <> selected).
                     {
                       intro Hchild_selected.
                       subst child.
                       contradiction.
                     }
                     rewrite Hkey_swap_other by
                       (rewrite ?Hcurrent_key_len; lia).
                     rewrite Hkey_swap_other by
                       (rewrite ?Hcurrent_key_len; lia).
                     apply Hexcept_edges.
                     repeat split; assumption.
                   }
                 }
              ** unfold PopHoleParentDominatesChildren.
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
                 rewrite Hkey_swap_index.
                 rewrite Hkey_swap_other by
                   (rewrite ?Hcurrent_key_len; lia).
                 unfold HeapOrderExceptDown in Hexcept.
                 destruct Hexcept as
                   [_ [_ Hexcept_edges]].
                 specialize
                   (Hexcept_edges child
                     ltac:(repeat split; try assumption; lia)).
                 rewrite Hchild_parent_selected in Hexcept_edges.
                 exact Hexcept_edges.
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
    apply Znth_replace_Znth_Diff;
      rewrite ?Zlength_replace_Znth; lia.
Qed.

Lemma heap_ordered_sublist0__pop_finalization :
  forall key_values size,
    heap_ordered key_values size ->
    heap_ordered (sublist 0 size key_values) size.
Proof.
  intros key_values size Hordered.
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

Lemma full_retire_last_with_tail__pop_finalization :
  forall p size values,
    0 < size ->
    size <= heap_capacity ->
    Zlength values = size ->
    IntArray.full p size values **
    IntArray.undef_seg p size heap_capacity |--
      IntArray.full p (size - 1) (sublist 0 (size - 1) values) **
      heap_tail p (size - 1).
Proof.
  intros p size values Hpositive Hcapacity Hlength.
  sep_apply_l_atomic
    (IntArray.full_split_to_seg
      p (size - 1) size values ltac:(lia)).
  sep_apply_l_atomic
    (IntArray.seg_to_full
      p 0 (size - 1)
      (sublist 0 (size - 1) values)).
  sep_apply_l_atomic
    (IntArray.seg_to_undef_seg
      p (size - 1) size
      (sublist (size - 1) size values)).
  unfold heap_tail.
  destruct (Z_lt_dec (size - 1) heap_capacity) as [_ | Hnot].
  2:{ lia. }
  unfold heap_spare.
  replace (size - 1 + 1) with size by lia.
  replace (p + 0 * sizeof(INT)) with p by lia.
  entailer!.
  replace (size - 1 - 0) with (size - 1) by lia.
  cancel.
Qed.

Lemma pop_ready_write_result__pop_finalization :
  forall S before_key before_data current_key current_data size item,
    heap_representation S before_key before_data size ->
    multiset_minimum S item ->
    PopReadyState before_key before_data current_key current_data
      size item ->
    PopResult S before_key before_data current_key current_data
      size item.
Proof.
  intros S before_key before_data current_key current_data
    size item Hrepresentation Hminimum Hready.
  destruct Hrepresentation as
    [Hsize0 [Hcapacity [Hmultiset_size
      [Hbefore_key_length
        [Hbefore_data_length [Hrelation Hbefore_ordered]]]]]].
  unfold PopReadyState in Hready.
  destruct Hready as
    (Hsize & Hbefore_key_length' & Hbefore_data_length' &
     Hcurrent_key_length & Hcurrent_data_length &
     Hbefore_ordered' & Hprefix & Hremaining &
     Hcurrent_ordered).
  unfold PrefixMinimum in Hprefix.
  destruct Hprefix as
    (Hpositive & Hprefix_key_bound & Hprefix_data_bound &
     Hroot & Hlower).
  unfold PopRemainingElements in Hremaining.
  destruct Hremaining as
    (Hremaining_size & Hremaining_before_key &
     Hremaining_before_data & Hremaining_current_key &
     Hremaining_current_data & Hremaining_perm).
  assert (Hbefore_pair_split :
    pair_list before_key before_data =
      item ::
      pair_list
        (sublist 1 size before_key)
        (sublist 1 size before_data)).
  {
    rewrite (pair_list_cons_split
      before_key before_data size) by lia.
    rewrite <- Hroot.
    reflexivity.
  }
  destruct Hminimum as [Hmember Hminimum_bound].
  destruct (proj1 (multiset_remove_spec S item) Hmember)
    as [Hremove_size Hremove_perm].
  assert (Hremoved_tail :
    Permutation
      (pair_list
        (sublist 1 size before_key)
        (sublist 1 size before_data))
      (mlist (multiset_remove S item))).
  {
    apply Permutation_cons_inv with (a := item).
    eapply Permutation_trans.
    - rewrite <- Hbefore_pair_split.
      apply Permutation_sym. exact Hrelation.
    - exact Hremove_perm.
  }
  unfold PopResult.
  repeat split; try lia; try assumption.
  - apply heap_ordered_sublist0__pop_finalization.
    exact Hcurrent_ordered.
  - eapply Permutation_trans.
    + exact Hremaining_perm.
    + exact Hremoved_tail.
Qed.

Lemma pop_result_store_retired_pair__pop_finalization :
  forall key data S before_key before_data
    result_key result_data size item,
    size <= heap_capacity ->
    PopResult S before_key before_data
      result_key result_data size item ->
    IntArray.full key size result_key **
    IntArray.undef_seg key size heap_capacity **
    IntArray.full data size result_data **
    IntArray.undef_seg data size heap_capacity |--
      store_heap key data (multiset_remove S item) (size - 1).
Proof.
  intros key data S before_key before_data
    result_key result_data size item Hcapacity Hresult.
  unfold PopResult in Hresult.
  destruct Hresult as
    (Hsize & Hbefore_key_length & Hbefore_data_length &
     Hresult_key_length & Hresult_data_length &
     Hordered & Hpermutation).
  assert (Hprefix_key_length :
    Zlength (sublist 0 (size - 1) result_key) = size - 1).
  {
    rewrite Zlength_sublist0; lia.
  }
  assert (Hprefix_data_length :
    Zlength (sublist 0 (size - 1) result_data) = size - 1).
  {
    rewrite Zlength_sublist0; lia.
  }
  assert (Hrepresentation :
    heap_representation
      (multiset_remove S item)
      (sublist 0 (size - 1) result_key)
      (sublist 0 (size - 1) result_data)
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
      rewrite <- Zlength_correct.
      unfold pair_list.
      rewrite Zlength_combine_eq.
      + exact Hprefix_key_length.
      + lia.
    - exact Hprefix_key_length.
    - exact Hprefix_data_length.
    - apply Permutation_sym. exact Hpermutation.
    - exact Hordered.
  }
  unfold store_heap.
  Exists (sublist 0 (size - 1) result_key).
  Exists (sublist 0 (size - 1) result_data).
  sep_apply_l_atomic
    (full_retire_last_with_tail__pop_finalization
      key size result_key ltac:(lia) Hcapacity Hresult_key_length).
  sep_apply_l_atomic
    (full_retire_last_with_tail__pop_finalization
      data size result_data ltac:(lia) Hcapacity Hresult_data_length).
  entailer!.
Qed.
