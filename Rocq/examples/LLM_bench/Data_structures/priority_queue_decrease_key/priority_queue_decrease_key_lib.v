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

Definition heap_capacity : Z := 100000.
Definition absent : Z := -1.

Definition heap_item (key data : Z) : Z * Z := (key, data).
Definition item_key (item : Z * Z) : Z := fst item.
Definition item_data (item : Z * Z) : Z := snd item.

Definition pair_list (key_values data_values : list Z) : list (Z * Z) :=
  combine key_values data_values.

Definition partial_map : Type := Z -> option Z.

Definition partial_map_get (M : partial_map) (data_x : Z) : option Z :=
  M data_x.

Definition partial_map_add
    (M : partial_map) (data_x key_x : Z) : partial_map :=
  fun query =>
    if Z.eq_dec query data_x then Some key_x else M query.

Definition partial_map_update
    (M : partial_map) (data_x key_x : Z) : partial_map :=
  partial_map_add M data_x key_x.

Definition partial_map_update_or_add
    (M : partial_map) (data_x key_x : Z) : partial_map :=
  partial_map_update M data_x key_x.

Definition partial_map_remove
    (M : partial_map) (data_x : Z) : partial_map :=
  fun query =>
    if Z.eq_dec query data_x then None else M query.

Definition partial_map_absent (M : partial_map) (data_x : Z) : Prop :=
  partial_map_get M data_x = None.

Definition partial_map_present
    (M : partial_map) (data_x key_x : Z) : Prop :=
  partial_map_get M data_x = Some key_x.

Definition partial_map_contains
    (M : partial_map) (data_x : Z) : Prop :=
  exists key_x, partial_map_present M data_x key_x.

Definition partial_map_item (M : partial_map) (item : Z * Z) : Prop :=
  partial_map_present M (item_data item) (item_key item).

Definition partial_map_minimum (M : partial_map) (item : Z * Z) : Prop :=
  partial_map_item M item /\
  forall data_x key_x,
    partial_map_present M data_x key_x ->
    item_key item <= key_x.

Definition heap_data_at
    (data_values : list Z) (index data_x : Z) : Prop :=
  0 <= index < Zlength data_values /\
  Znth index data_values 0 = data_x.

Definition heap_contains_data
    (M : partial_map) (data_x : Z) : Prop :=
  partial_map_contains M data_x.

Definition heap_data_absent
    (M : partial_map) (data_x : Z) : Prop :=
  partial_map_absent M data_x.

Definition heap_data_present
    (M : partial_map) (data_x : Z) : Prop :=
  heap_contains_data M data_x.

Definition heap_key_of
    (M : partial_map) (data_x key_x : Z) : Prop :=
  partial_map_present M data_x key_x.

Definition heap_data_valid
    (data_values : list Z) (data_bound size : Z) : Prop :=
  forall index,
    0 <= index < size ->
    0 <= Znth index data_values 0 < data_bound.

Definition heap_data_unique
    (data_values : list Z) (size : Z) : Prop :=
  forall i j,
    0 <= i < size ->
    0 <= j < size ->
    Znth i data_values 0 = Znth j data_values 0 ->
    i = j.

Definition heap_map_relation
    (M : partial_map)
    (key_values data_values : list Z) (size : Z) : Prop :=
  Zlength key_values = size /\
  Zlength data_values = size /\
  heap_data_unique data_values size /\
  (forall index,
    0 <= index < size ->
    partial_map_present
      M
      (Znth index data_values 0)
      (Znth index key_values 0)) /\
  (forall data_x key_x,
    partial_map_present M data_x key_x ->
    exists index,
      0 <= index < size /\
      Znth index data_values 0 = data_x /\
      Znth index key_values 0 = key_x).

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

Definition heap_ordered (key_values : list Z) (size : Z) : Prop :=
  forall child,
    0 < child /\ child < size ->
    Znth (heap_parent child) key_values 0 <= Znth child key_values 0.

Definition heap_pos_backlinks
    (data_values pos_values : list Z) (size : Z) : Prop :=
  forall index,
    0 <= index < size ->
    Znth (Znth index data_values 0) pos_values absent = index.

Definition heap_pos_forward_links
    (data_values pos_values : list Z) (data_bound size : Z) : Prop :=
  forall data_x,
    0 <= data_x < data_bound ->
    Znth data_x pos_values absent = absent \/
    exists index,
      0 <= index < size /\
      Znth index data_values 0 = data_x /\
      Znth data_x pos_values absent = index.

Definition heap_pos_consistent
    (data_values pos_values : list Z) (data_bound size : Z) : Prop :=
  0 <= data_bound /\
  Zlength pos_values = data_bound /\
  heap_data_valid data_values data_bound size /\
  heap_pos_backlinks data_values pos_values size /\
  heap_pos_forward_links data_values pos_values data_bound size.

Definition heap_representation
    (M : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size : Z) : Prop :=
  0 <= size /\
  size <= heap_capacity /\
  heap_map_relation M key_values data_values size /\
  heap_ordered key_values size /\
  heap_pos_consistent data_values pos_values data_bound size.

Definition store_heap
    (key data pos : addr) (data_bound capacity : Z)
    (M : partial_map) (size : Z) : Assertion :=
  EX key_values : list Z,
  EX data_values : list Z,
  EX pos_values : list Z,
    “ heap_representation
        M key_values data_values pos_values data_bound size ” &&
    IntArray.full key size key_values **
    IntArray.undef_seg key size capacity **
    IntArray.full data size data_values **
    IntArray.undef_seg data size capacity **
    IntArray.full pos data_bound pos_values.

Definition heap_index_of
    (M : partial_map)
    (data_values pos_values : list Z) (data_x index : Z) : Prop :=
  heap_data_present M data_x /\
  0 <= index < Zlength data_values /\
  Znth index data_values 0 = data_x /\
  Znth data_x pos_values absent = index.

Definition decrease_key_pre
    (M : partial_map) (data_x key_x : Z) : Prop :=
  exists old_key,
    heap_key_of M data_x old_key /\
    key_x <= old_key.

Definition partial_map_decrease_key_pre :=
  decrease_key_pre.

Definition update_or_push_pre
    (M : partial_map) (data_x key_x : Z) : Prop :=
  heap_data_absent M data_x \/
  decrease_key_pre M data_x key_x.

Definition partial_map_update_or_add_pre :=
  update_or_push_pre.

Definition partial_map_update_or_add_size
    (before : partial_map)
    (size_before size_after data_x key_x : Z) : Prop :=
  (partial_map_absent before data_x /\
   size_after = size_before + 1) \/
  (partial_map_decrease_key_pre before data_x key_x /\
   size_after = size_before).

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

Definition SelectedChild
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

Definition HeapArrayState
    (M : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size : Z) : Prop :=
  0 <= size /\
  size <= heap_capacity /\
  heap_map_relation M key_values data_values size /\
  heap_pos_consistent data_values pos_values data_bound size.

Definition SiftUpState
    (M : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size child : Z) : Prop :=
  HeapArrayState M key_values data_values pos_values data_bound size /\
  0 <= child < size /\
  HeapOrderExceptUp key_values size child /\
  PushHoleChildrenPreserved key_values size child.

Definition SiftDownState
    (M : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size index : Z) : Prop :=
  HeapArrayState M key_values data_values pos_values data_bound size /\
  0 <= index < size /\
  HeapOrderExceptDown key_values size index /\
  PopHoleParentDominatesChildren key_values size index.

Definition store_sift_up
    (key data pos : addr) (data_bound capacity : Z)
    (M : partial_map) (size index : Z) : Assertion :=
  EX key_values : list Z,
  EX data_values : list Z,
  EX pos_values : list Z,
    “ SiftUpState
        M key_values data_values pos_values data_bound size index ” &&
    IntArray.full key size key_values **
    IntArray.undef_seg key size capacity **
    IntArray.full data size data_values **
    IntArray.undef_seg data size capacity **
    IntArray.full pos data_bound pos_values.

Definition store_sift_down
    (key data pos : addr) (data_bound capacity : Z)
    (M : partial_map) (size index : Z) : Assertion :=
  EX key_values : list Z,
  EX data_values : list Z,
  EX pos_values : list Z,
    “ SiftDownState
        M key_values data_values pos_values data_bound size index ” &&
    IntArray.full key size key_values **
    IntArray.undef_seg key size capacity **
    IntArray.full data size data_values **
    IntArray.undef_seg data size capacity **
    IntArray.full pos data_bound pos_values.

Definition PushWriteState
    (before : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size data_x key_x : Z) : Prop :=
  partial_map_absent before data_x /\
  SiftUpState (partial_map_add before data_x key_x)
    key_values data_values pos_values
    data_bound (size + 1) size /\
  Znth size key_values 0 = key_x /\
  Znth size data_values 0 = data_x /\
  Znth data_x pos_values absent = size.

Definition DecreaseKeyWriteState
    (before : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size data_x key_x index : Z) : Prop :=
  0 <= index < size /\
  Znth index data_values 0 = data_x /\
  partial_map_decrease_key_pre before data_x key_x /\
  SiftUpState (partial_map_update before data_x key_x)
    key_values data_values pos_values
    data_bound size index /\
  Znth index key_values 0 = key_x.

Definition PopRootState
    (before : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size : Z) (popped : Z * Z) : Prop :=
  1 <= size /\
  partial_map_minimum before popped /\
  heap_representation
    (partial_map_remove before (item_data popped))
    key_values data_values pos_values data_bound (size - 1).

Definition heap_pos_backlinks_except
    (data_values pos_values : list Z) (size skipped_index : Z) : Prop :=
  forall index,
    0 <= index < size ->
    index <> skipped_index ->
    Znth (Znth index data_values 0) pos_values absent = index.

Definition PopMarkedState
    (before : partial_map)
    (key_values data_values pos_values : list Z)
    (data_bound size : Z) (popped : Z * Z) : Prop :=
  1 <= size /\
  partial_map_minimum before popped /\
  0 <= size /\
  size <= heap_capacity /\
  heap_map_relation before key_values data_values size /\
  heap_ordered key_values size /\
  0 <= data_bound /\
  Zlength pos_values = data_bound /\
  heap_data_valid data_values data_bound size /\
  heap_pos_backlinks_except data_values pos_values size 0 /\
  heap_pos_forward_links data_values pos_values data_bound size /\
  Znth 0 key_values 0 = item_key popped /\
  Znth 0 data_values 0 = item_data popped /\
  Znth (item_data popped) pos_values absent = absent /\
  0 <= item_data popped < data_bound.

Lemma heap_parent_positive_bounds :
  forall child size,
    0 < child ->
    child < size ->
    0 <= heap_parent child /\
    heap_parent child < child /\
    heap_parent child < size.
Proof.
  intros child size Hchild Hbound.
  unfold heap_parent.
  split.
  - apply Z.quot_pos; lia.
  - split.
    + apply Z.quot_lt_upper_bound; lia.
    + assert (Z.quot (child - 1) 2 < child) by
        (apply Z.quot_lt_upper_bound; lia).
      lia.
Qed.

Lemma heap_parent_left_child :
  forall index,
    0 <= index ->
    heap_parent (heap_left_child index) = index.
Proof.
  intros index Hindex.
  unfold heap_parent, heap_left_child.
  replace (index * 2 + 1 - 1) with (index * 2) by ring.
  rewrite Z.quot_mul by lia.
  reflexivity.
Qed.

Lemma heap_parent_right_child :
  forall index,
    0 <= index ->
    heap_parent (heap_right_child index) = index.
Proof.
  intros index Hindex.
  unfold heap_parent, heap_right_child.
  replace (index * 2 + 2 - 1) with (index * 2 + 1) by ring.
  pose proof
    (Z.rem_bound_pos_pos (index * 2 + 1) 2 ltac:(lia) ltac:(lia))
    as Hrem.
  pose proof (Z.quot_rem (index * 2 + 1) 2 ltac:(lia)) as Hquot.
  assert (Z.rem (index * 2 + 1) 2 = 1) by lia.
  lia.
Qed.

Lemma heap_children_characterization :
  forall index child,
    0 <= index ->
    0 < child ->
    heap_parent child = index ->
    child = heap_left_child index \/ child = heap_right_child index.
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

Lemma heap_ordered_root_lower_bound :
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
    eapply Z.le_trans; eauto.
Qed.

Lemma heap_root_is_partial_map_minimum :
  forall M key_values data_values pos_values data_bound size,
    1 <= size ->
    heap_representation
      M key_values data_values pos_values data_bound size ->
    partial_map_minimum
      M (heap_item (Znth 0 key_values 0) (Znth 0 data_values 0)).
Proof.
  intros M key_values data_values pos_values data_bound size Hsize Hrep.
  destruct Hrep as [_ [_ [Hmap [Hordered _]]]].
  destruct Hmap as
    [Hkey_len [Hdata_len [_ [Hindex_present Hpresent_index]]]].
  unfold partial_map_minimum, partial_map_item.
  split.
  - unfold item_data, item_key, heap_item.
    apply Hindex_present. lia.
  - intros data_x key_x Hpresent.
    specialize (Hpresent_index data_x key_x Hpresent)
      as [index [Hindex [_ Hkey]]].
    unfold item_key, heap_item.
    rewrite <- Hkey.
    eapply heap_ordered_root_lower_bound; eauto.
Qed.

Lemma pop_marked_state_from_heap_representation :
  forall M key_values data_values pos_values data_bound size,
    1 <= size ->
    heap_representation
      M key_values data_values pos_values data_bound size ->
    PopMarkedState
      M key_values data_values
      (replace_Znth (Znth 0 data_values 0) absent pos_values)
      data_bound size
      (heap_item (Znth 0 key_values 0) (Znth 0 data_values 0)).
Proof.
  intros M key_values data_values pos_values data_bound size Hsize Hrep.
  pose proof Hrep as Hrep_copy.
  destruct Hrep as [Hsize_nonneg [Hcapacity [Hmap [Hordered Hpos]]]].
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  destruct Hpos as [Hbound [Hpos_len [Hvalid [Hback Hforward]]]].
  assert (Hroot_valid : 0 <= Znth 0 data_values 0 < data_bound)
    by (apply Hvalid; lia).
  unfold PopMarkedState.
  split; [exact Hsize |].
  split.
  - apply heap_root_is_partial_map_minimum with
      (key_values := key_values) (data_values := data_values)
      (pos_values := pos_values) (data_bound := data_bound)
      (size := size);
      assumption.
  - split; [exact Hsize_nonneg |].
    split; [exact Hcapacity |].
    split.
    + exact
      (conj Hkey_len
        (conj Hdata_len
          (conj Hunique
            (conj Hindex_present Hpresent_index)))).
    + split; [exact Hordered |].
      split; [exact Hbound |].
      split.
      * rewrite Zlength_replace_Znth
          by (rewrite Hpos_len; exact Hroot_valid).
        exact Hpos_len.
      * split; [exact Hvalid |].
        split.
        -- unfold heap_pos_backlinks_except.
           intros index Hindex Hnot_root.
           assert (Hdata_index_valid :
             0 <= Znth index data_values 0 < data_bound)
             by (apply Hvalid; exact Hindex).
           rewrite (Znth_replace_Znth_Diff
             absent pos_values (Znth 0 data_values 0)
             (Znth index data_values 0) absent).
           ++ apply Hback. exact Hindex.
           ++ rewrite Hpos_len. exact Hroot_valid.
           ++ rewrite Hpos_len. exact Hdata_index_valid.
           ++ intro Heq.
              assert (index = 0) by (eapply Hunique; eauto; lia).
              contradiction.
        -- split.
           ++ unfold heap_pos_forward_links.
              intros data_x Hdata_x.
              destruct (Z.eq_dec data_x (Znth 0 data_values 0))
                as [Hroot | Hnot_root].
              ** left.
                 subst data_x.
                 rewrite Znth_replace_Znth_Same
                   by (rewrite Hpos_len; exact Hroot_valid).
                 reflexivity.
              ** destruct (Hforward data_x Hdata_x)
                   as [Habs | [index [Hindex [Hdata Hpos_index]]]].
                 --- left.
                     rewrite (Znth_replace_Znth_Diff
                       absent pos_values (Znth 0 data_values 0)
                       data_x absent).
                     +++ exact Habs.
                     +++ rewrite Hpos_len. exact Hroot_valid.
                     +++ rewrite Hpos_len. exact Hdata_x.
                     +++ intro Heq. apply Hnot_root. symmetry. exact Heq.
                 --- right. exists index.
                     split; [exact Hindex |].
                     split; [exact Hdata |].
                     rewrite (Znth_replace_Znth_Diff
                       absent pos_values (Znth 0 data_values 0)
                       data_x absent).
                     +++ exact Hpos_index.
                     +++ rewrite Hpos_len. exact Hroot_valid.
                     +++ rewrite Hpos_len. exact Hdata_x.
                     +++ intro Heq. apply Hnot_root. symmetry. exact Heq.
           ++ split.
              ** unfold item_key, heap_item. reflexivity.
              ** split.
                 --- unfold item_data, heap_item. reflexivity.
                 --- split.
                     +++ unfold item_data, heap_item.
                         rewrite Znth_replace_Znth_Same
                           by (rewrite Hpos_len; exact Hroot_valid).
                         reflexivity.
                     +++ unfold item_data, heap_item. exact Hroot_valid.
Qed.

Lemma heap_representation_remove_singleton :
  forall M key_values data_values pos_values data_bound,
    heap_representation M key_values data_values pos_values data_bound 1 ->
    heap_representation
      (partial_map_remove M (Znth 0 data_values 0))
      [] []
      (replace_Znth (Znth 0 data_values 0) absent pos_values)
      data_bound 0.
Proof.
  intros M key_values data_values pos_values data_bound Hrep.
  destruct Hrep as [Hsize [Hcapacity [Hmap [Hordered Hpos]]]].
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  destruct Hpos as [Hbound [Hpos_len [Hvalid [Hback Hforward]]]].
  assert (Hroot_valid : 0 <= Znth 0 data_values 0 < data_bound)
    by (apply Hvalid; lia).
  unfold heap_representation.
  split; [lia |].
  split; [unfold heap_capacity; lia |].
  split.
  - unfold heap_map_relation.
    split; [rewrite Zlength_nil; reflexivity |].
    split; [rewrite Zlength_nil; reflexivity |].
    split.
    + unfold heap_data_unique. intros; lia.
    + split.
      * intros index Hindex. lia.
      * intros data_x key_x Hpresent.
      unfold partial_map_present, partial_map_get,
        partial_map_remove in Hpresent.
      destruct (Z.eq_dec data_x (Znth 0 data_values 0))
        as [Hroot | Hnot_root]; [congruence |].
      specialize (Hpresent_index data_x key_x Hpresent)
        as [index [Hindex [Hdata _]]].
      assert (index = 0) by lia.
      subst index.
      exfalso. apply Hnot_root. symmetry. exact Hdata.
  - split.
    + unfold heap_ordered. intros child [Hchild_pos Hchild_bound].
      exfalso; lia.
    + unfold heap_pos_consistent.
      split; [exact Hbound |].
      split.
      * rewrite Zlength_replace_Znth
          by (rewrite Hpos_len; exact Hroot_valid).
        exact Hpos_len.
      * split.
        -- unfold heap_data_valid. intros index Hindex. lia.
        -- split.
           ++ unfold heap_pos_backlinks. intros index Hindex. lia.
           ++ unfold heap_pos_forward_links.
              intros data_x Hdata_x.
              destruct (Z.eq_dec data_x (Znth 0 data_values 0))
                as [Hroot | Hnot_root].
              ** left.
                 subst data_x.
                 rewrite Znth_replace_Znth_Same
                   by (rewrite Hpos_len; exact Hroot_valid).
                 reflexivity.
              ** destruct (Hforward data_x Hdata_x)
                   as [Habs | [index [Hindex [Hdata Hpos_index]]]].
                 --- left.
                     rewrite (Znth_replace_Znth_Diff
                       absent pos_values (Znth 0 data_values 0)
                       data_x absent).
                     +++ exact Habs.
                     +++ rewrite Hpos_len. exact Hroot_valid.
                     +++ rewrite Hpos_len. exact Hdata_x.
                     +++ intro Heq. apply Hnot_root. symmetry. exact Heq.
                 --- assert (index = 0) by lia.
                     subst index.
                     rewrite H in Hdata.
                     exfalso. apply Hnot_root. symmetry. exact Hdata.
Qed.

Lemma singleton_full_to_empty_undef :
  forall p capacity values,
    1 <= capacity ->
    Zlength values = 1 ->
    IntArray.full p 1 values **
    IntArray.undef_seg p 1 capacity |--
      IntArray.full p 0 [] **
      IntArray.undef_seg p 0 capacity.
Proof.
  intros p capacity values Hcapacity Hlength.
  destruct values as [|a values].
  - rewrite Zlength_nil in Hlength. lia.
  - destruct values as [|b values].
    + rewrite IntArray.full_empty.
      sep_apply IntArray.full_to_seg.
      sep_apply IntArray.seg_to_undef_seg.
      sep_apply (IntArray.undef_seg_merge_to_undef_seg p 0 1 capacity
        ltac:(lia)).
      entailer!.
    + rewrite !Zlength_cons in Hlength.
      pose proof (Zlength_nonneg values).
      lia.
Qed.

Lemma full_retire_last_to_undef :
  forall p size capacity values,
    0 < size ->
    size <= capacity ->
    Zlength values = size ->
    IntArray.full p size values **
    IntArray.undef_seg p size capacity |--
      IntArray.full p (size - 1) (sublist 0 (size - 1) values) **
      IntArray.undef_seg p (size - 1) capacity.
Proof.
  intros p size capacity values Hpositive Hcapacity Hlength.
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
  sep_apply_l_atomic
    (IntArray.undef_seg_merge_to_undef_seg
      p (size - 1) size capacity ltac:(lia)).
  replace (p + 0 * sizeof(INT)) with p by lia.
  entailer!.
  replace (size - 1 - 0) with (size - 1) by lia.
  cancel.
Qed.

Definition pop_replaced_values (size : Z) (values : list Z) : list Z :=
  sublist 0 (size - 1)
    (replace_Znth 0 (Znth (size - 1) values 0) values).

Definition pop_replacement_source (size index : Z) : Z :=
  if Z.eq_dec index 0 then size - 1 else index.

Lemma Zlength_pop_replaced_values :
  forall size values,
    1 < size ->
    Zlength values = size ->
    Zlength (pop_replaced_values size values) = size - 1.
Proof.
  intros size values Hsize Hlength.
  unfold pop_replaced_values.
  rewrite Zlength_sublist by (rewrite Zlength_replace_Znth; lia).
  lia.
Qed.

Lemma Znth_pop_replaced_values :
  forall size values index,
    1 < size ->
    Zlength values = size ->
    0 <= index < size - 1 ->
    Znth index (pop_replaced_values size values) 0 =
    Znth (pop_replacement_source size index) values 0.
Proof.
  intros size values index Hsize Hlength Hindex.
  unfold pop_replaced_values, pop_replacement_source.
  rewrite Znth_sublist0 by lia.
  destruct (Z.eq_dec index 0) as [Hidx | Hidx].
  - subst index.
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
Qed.

Lemma pop_replacement_source_range :
  forall size index,
    1 < size ->
    0 <= index < size - 1 ->
    0 < pop_replacement_source size index < size.
Proof.
  intros size index Hsize Hindex.
  unfold pop_replacement_source.
  destruct (Z.eq_dec index 0); lia.
Qed.

Lemma pop_replacement_source_injective :
  forall size i j,
    1 < size ->
    0 <= i < size - 1 ->
    0 <= j < size - 1 ->
    pop_replacement_source size i =
    pop_replacement_source size j ->
    i = j.
Proof.
  intros size i j Hsize Hi Hj Heq.
  unfold pop_replacement_source in Heq.
  destruct (Z.eq_dec i 0), (Z.eq_dec j 0); lia.
Qed.

Lemma heap_map_relation_remove_root_replacement :
  forall M key_values data_values size,
    1 < size ->
    heap_map_relation M key_values data_values size ->
    heap_map_relation
      (partial_map_remove M (Znth 0 data_values 0))
      (pop_replaced_values size key_values)
      (pop_replaced_values size data_values)
      (size - 1).
Proof.
  intros M key_values data_values size Hsize Hmap.
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  unfold heap_map_relation.
  split.
  - apply Zlength_pop_replaced_values; assumption.
  - split.
    + apply Zlength_pop_replaced_values; assumption.
    + split.
      * unfold heap_data_unique.
        intros i j Hi Hj Heq.
        rewrite !Znth_pop_replaced_values in Heq by assumption.
        apply pop_replacement_source_injective with (size := size);
          try assumption.
        assert (Hsource_i :
          0 < pop_replacement_source size i < size)
          by (apply pop_replacement_source_range; assumption).
        assert (Hsource_j :
          0 < pop_replacement_source size j < size)
          by (apply pop_replacement_source_range; assumption).
        apply Hunique.
        -- lia.
        -- lia.
        -- exact Heq.
      * split.
        -- intros index Hindex.
           rewrite !Znth_pop_replaced_values by assumption.
           set (source := pop_replacement_source size index).
           assert (Hsource_range : 0 < source < size).
           {
             subst source.
             apply pop_replacement_source_range; assumption.
           }
           unfold partial_map_present, partial_map_get,
             partial_map_remove.
           destruct
             (Z.eq_dec (Znth source data_values 0)
               (Znth 0 data_values 0)) as [Hroot | Hnot_root].
           ++ exfalso.
              assert (source = 0) by (eapply Hunique; eauto; lia).
              lia.
           ++ apply Hindex_present. lia.
        -- intros data_x key_x Hpresent.
           unfold partial_map_present, partial_map_get,
             partial_map_remove in Hpresent.
           destruct (Z.eq_dec data_x (Znth 0 data_values 0))
             as [Hroot | Hnot_root]; [congruence |].
           specialize (Hpresent_index data_x key_x Hpresent)
             as [old_index [Hold_index [Hdata Hkey]]].
           assert (Hold_not_root : old_index <> 0).
           {
             intro Hold_root.
             subst old_index.
             apply Hnot_root. symmetry. exact Hdata.
           }
           destruct (Z.eq_dec old_index (size - 1))
             as [Hold_last | Hold_not_last].
           ++ exists 0.
              repeat split; try lia.
              ** rewrite Znth_pop_replaced_values by
                   (try assumption; lia).
                 unfold pop_replacement_source.
                 destruct (Z.eq_dec 0 0); [| contradiction].
                 rewrite <- Hold_last. exact Hdata.
              ** rewrite Znth_pop_replaced_values by
                   (try assumption; lia).
                 unfold pop_replacement_source.
                 destruct (Z.eq_dec 0 0); [| contradiction].
                 rewrite <- Hold_last. exact Hkey.
           ++ exists old_index.
              assert (Hnew_index : 0 <= old_index < size - 1) by lia.
              repeat split; try lia.
              ** rewrite Znth_pop_replaced_values by
                   (try assumption; lia).
                 unfold pop_replacement_source.
                 destruct (Z.eq_dec old_index 0); [contradiction |].
                 exact Hdata.
              ** rewrite Znth_pop_replaced_values by
                   (try assumption; lia).
                 unfold pop_replacement_source.
                 destruct (Z.eq_dec old_index 0); [contradiction |].
                 exact Hkey.
Qed.

Lemma pop_root_replacement_sift_down_state :
  forall M key_values data_values pos_values data_bound size popped,
    1 < size ->
    PopMarkedState
      M key_values data_values pos_values data_bound size popped ->
    SiftDownState
      (partial_map_remove M (item_data popped))
      (pop_replaced_values size key_values)
      (pop_replaced_values size data_values)
      (replace_Znth (Znth (size - 1) data_values 0) 0 pos_values)
      data_bound (size - 1) 0.
Proof.
  intros M key_values data_values pos_values data_bound size popped
    Hsize Hmarked.
  unfold PopMarkedState in Hmarked.
  destruct Hmarked as
    (Hnonempty & Hminimum & Hsize_nonneg & Hcapacity &
     Hmap & Hordered & Hbound & Hpos_len & Hvalid &
     Hback_except & Hforward & Hroot_key & Hroot_data &
     Hroot_absent & Hroot_valid).
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  assert (Hmap_full :
    heap_map_relation M key_values data_values size).
  {
    repeat split; assumption.
  }
  assert (Hlast_valid : 0 <= Znth (size - 1) data_values 0 < data_bound)
    by (apply Hvalid; lia).
  assert (Hlast_not_root :
    Znth (size - 1) data_values 0 <> Znth 0 data_values 0).
  {
    intro Heq.
    assert (size - 1 = 0) by (eapply Hunique; eauto; lia).
    lia.
  }
  unfold SiftDownState.
  split.
  - unfold HeapArrayState.
    split; [lia |].
    split; [lia |].
    split.
    + rewrite <- Hroot_data.
      apply heap_map_relation_remove_root_replacement; assumption.
    + unfold heap_pos_consistent.
      split; [exact Hbound |].
      split.
      * rewrite Zlength_replace_Znth by
          (rewrite Hpos_len; exact Hlast_valid).
        exact Hpos_len.
      * split.
        -- unfold heap_data_valid.
           intros index Hindex.
           rewrite Znth_pop_replaced_values by assumption.
           apply Hvalid.
           pose proof
             (pop_replacement_source_range size index Hsize Hindex).
           lia.
        -- split.
           ++ unfold heap_pos_backlinks.
              intros index Hindex.
              destruct (Z.eq_dec index 0) as [Hidx_root | Hidx_not_root].
              ** subst index.
                 rewrite Znth_pop_replaced_values by assumption.
                 unfold pop_replacement_source.
                 destruct (Z.eq_dec 0 0); [| contradiction].
                 rewrite Znth_replace_Znth_Same by
                   (rewrite Hpos_len; exact Hlast_valid).
                 reflexivity.
              ** rewrite Znth_pop_replaced_values by assumption.
                 unfold pop_replacement_source.
                 destruct (Z.eq_dec index 0); [contradiction |].
                 assert (Hdata_index_valid :
                   0 <= Znth index data_values 0 < data_bound)
                   by (apply Hvalid; lia).
                 rewrite (Znth_replace_Znth_Diff
                   absent pos_values (Znth (size - 1) data_values 0)
                   (Znth index data_values 0) 0).
                 --- apply Hback_except; lia.
                 --- rewrite Hpos_len. exact Hlast_valid.
                 --- rewrite Hpos_len. exact Hdata_index_valid.
                 --- intro Heq.
                     assert (index = size - 1)
                       by (eapply Hunique; eauto; lia).
                     lia.
           ++ unfold heap_pos_forward_links.
              intros data_x Hdata_x.
              destruct (Z.eq_dec data_x (Znth 0 data_values 0))
                as [Hquery_root | Hquery_not_root].
              ** left.
                 subst data_x.
                 rewrite (Znth_replace_Znth_Diff
                   absent pos_values (Znth (size - 1) data_values 0)
                   (Znth 0 data_values 0) 0).
                 --- rewrite Hroot_data. exact Hroot_absent.
                 --- rewrite Hpos_len. exact Hlast_valid.
                 --- rewrite Hpos_len. exact Hdata_x.
                 --- intro Heq. apply Hlast_not_root. exact Heq.
              ** destruct (Z.eq_dec data_x (Znth (size - 1) data_values 0))
                   as [Hquery_last | Hquery_not_last].
                 --- right. exists 0.
                     subst data_x.
                     repeat split; try lia.
                     +++ rewrite Znth_pop_replaced_values by
                           (try assumption; lia).
                         unfold pop_replacement_source.
                         destruct (Z.eq_dec 0 0); [reflexivity | contradiction].
                     +++ rewrite Znth_replace_Znth_Same by
                           (rewrite Hpos_len; exact Hlast_valid).
                         reflexivity.
                 --- destruct (Hforward data_x Hdata_x)
                       as [Habs | [old_index [Hold_index [Hdata Hpos]]]].
                     +++ left.
                         rewrite (Znth_replace_Znth_Diff
                           absent pos_values (Znth (size - 1) data_values 0)
                           data_x 0).
                         *** exact Habs.
                         *** rewrite Hpos_len. exact Hlast_valid.
                         *** rewrite Hpos_len. exact Hdata_x.
                         *** intro Heq. apply Hquery_not_last. symmetry. exact Heq.
                     +++ assert (Hold_not_root : old_index <> 0).
                         {
                           intro Hold_root.
                           subst old_index.
                           rewrite Hold_root in Hdata.
                           apply Hquery_not_root. symmetry. exact Hdata.
                         }
                         assert (Hold_not_last : old_index <> size - 1).
                         {
                           intro Hold_last.
                           subst old_index.
                           rewrite Hold_last in Hdata.
                           apply Hquery_not_last. symmetry. exact Hdata.
                         }
                         right. exists old_index.
                         assert (Hnew_index : 0 <= old_index < size - 1) by lia.
                         repeat split; try lia.
                         *** rewrite Znth_pop_replaced_values by
                               (try assumption; lia).
                             unfold pop_replacement_source.
                             destruct (Z.eq_dec old_index 0);
                               [contradiction | exact Hdata].
                         *** rewrite (Znth_replace_Znth_Diff
                               absent pos_values
                               (Znth (size - 1) data_values 0)
                               data_x 0).
                             ---- exact Hpos.
                             ---- rewrite Hpos_len. exact Hlast_valid.
                             ---- rewrite Hpos_len. exact Hdata_x.
                             ---- intro Heq.
                                  apply Hquery_not_last.
                                  symmetry. exact Heq.
  - split; [lia |].
    split.
    + unfold HeapOrderExceptDown.
      split; [lia |].
      split; [lia |].
      intros child [Hchild_pos [Hchild_bound Hparent_not_root]].
      pose proof
        (heap_parent_positive_bounds child (size - 1)
          Hchild_pos Hchild_bound) as
        [Hparent_nonnegative [Hparent_lt_child Hparent_bound]].
      rewrite !Znth_pop_replaced_values by
        (try assumption; lia).
      unfold pop_replacement_source.
      destruct (Z.eq_dec (heap_parent child) 0);
        [contradiction |].
      destruct (Z.eq_dec child 0); [lia |].
      apply Hordered. lia.
    + unfold PopHoleParentDominatesChildren.
      left. reflexivity.
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

Definition heap_swap_values (i j : Z) (values : list Z) : list Z :=
  replace_Znth j (Znth i values 0)
    (replace_Znth i (Znth j values 0) values).

Definition heap_swap_pos
    (data_values pos_values : list Z) (i j : Z) : list Z :=
  replace_Znth (Znth j data_values 0) i
    (replace_Znth (Znth i data_values 0) j pos_values).

Definition swap_source (i j k : Z) : Z :=
  if Z.eq_dec k i then j else if Z.eq_dec k j then i else k.

Lemma swap_source_range :
  forall i j k size,
    0 <= i < size ->
    0 <= j < size ->
    0 <= k < size ->
    0 <= swap_source i j k < size.
Proof.
  intros i j k size Hi Hj Hk.
  unfold swap_source.
  destruct (Z.eq_dec k i), (Z.eq_dec k j); lia.
Qed.

Lemma swap_source_involutive :
  forall i j k,
    i <> j ->
    swap_source i j (swap_source i j k) = k.
Proof.
  intros i j k Hneq.
  unfold swap_source.
  destruct (Z.eq_dec k i), (Z.eq_dec k j); subst; try lia;
    repeat (destruct Z.eq_dec; try lia).
Qed.

Lemma swap_source_injective :
  forall i j k1 k2,
    i <> j ->
    swap_source i j k1 = swap_source i j k2 ->
    k1 = k2.
Proof.
  intros i j k1 k2 Hneq Heq.
  pose proof (f_equal (swap_source i j) Heq) as Hswap.
  rewrite !swap_source_involutive in Hswap by exact Hneq.
  exact Hswap.
Qed.

Lemma Zlength_heap_swap_values :
  forall i j values,
    Zlength (heap_swap_values i j values) = Zlength values.
Proof.
  intros. unfold heap_swap_values.
  repeat rewrite Zlength_replace_Znth.
  reflexivity.
Qed.

Lemma Znth_heap_swap_values :
  forall values i j k,
    0 <= i < Zlength values ->
    0 <= j < Zlength values ->
    i <> j ->
    0 <= k < Zlength values ->
    Znth k (heap_swap_values i j values) 0 =
    Znth (swap_source i j k) values 0.
Proof.
  intros values i j k Hi Hj Hneq Hk.
  unfold heap_swap_values.
  pose proof (Znth_swap_Znth values i j 0 Hi Hj Hneq)
    as [Hi_val [Hj_val Hother]].
  unfold swap_source.
  destruct (Z.eq_dec k i) as [Hki | Hki].
  - subst k. exact Hi_val.
  - destruct (Z.eq_dec k j) as [Hkj | Hkj].
    + subst k. exact Hj_val.
    + apply Hother; assumption.
Qed.

Lemma heap_data_unique_swap_values :
  forall data_values size i j,
    heap_data_unique data_values size ->
    0 <= i < size ->
    0 <= j < size ->
    i <> j ->
    Zlength data_values = size ->
    heap_data_unique (heap_swap_values i j data_values) size.
Proof.
  intros data_values size i j Hunique Hi Hj Hneq Hlen.
  unfold heap_data_unique.
  intros k1 k2 Hk1 Hk2 Heq.
  rewrite !Znth_heap_swap_values in Heq by lia.
  apply swap_source_injective with (i := i) (j := j); [assumption |].
  apply Hunique; try (apply swap_source_range; assumption).
  exact Heq.
Qed.

Lemma heap_map_relation_swap_values :
  forall M key_values data_values size i j,
    heap_map_relation M key_values data_values size ->
    0 <= i < size ->
    0 <= j < size ->
    i <> j ->
    heap_map_relation M
      (heap_swap_values i j key_values)
      (heap_swap_values i j data_values)
      size.
Proof.
  intros M key_values data_values size i j Hmap Hi Hj Hneq.
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  unfold heap_map_relation.
  split.
  - rewrite Zlength_heap_swap_values. exact Hkey_len.
  - split.
    + rewrite Zlength_heap_swap_values. exact Hdata_len.
    + split.
      * apply heap_data_unique_swap_values; assumption.
      * split.
        -- intros index Hindex.
           rewrite !Znth_heap_swap_values by lia.
           apply Hindex_present.
           apply swap_source_range; assumption.
        -- intros data_x key_x Hpresent.
           specialize (Hpresent_index data_x key_x Hpresent)
             as [old_index [Hold_index [Hdata Hkey]]].
           exists (swap_source i j old_index).
           assert (Hnew_index :
             0 <= swap_source i j old_index < size)
             by (apply swap_source_range; assumption).
           split; [exact Hnew_index |].
           split.
           ++ rewrite Znth_heap_swap_values by lia.
              rewrite swap_source_involutive by assumption.
              exact Hdata.
           ++ rewrite Znth_heap_swap_values by lia.
              rewrite swap_source_involutive by assumption.
              exact Hkey.
Qed.

Lemma heap_pos_consistent_swap_values :
  forall data_values pos_values data_bound size i j,
    heap_data_unique data_values size ->
    heap_pos_consistent data_values pos_values data_bound size ->
    0 <= i < size ->
    0 <= j < size ->
    i <> j ->
    Zlength data_values = size ->
    heap_pos_consistent
      (heap_swap_values i j data_values)
      (heap_swap_pos data_values pos_values i j)
      data_bound size.
Proof.
  intros data_values pos_values data_bound size i j
    Hunique Hpos Hi Hj Hneq Hdata_len.
  destruct Hpos as [Hbound [Hpos_len [Hvalid [Hback Hforward]]]].
  assert (Hdata_i_valid : 0 <= Znth i data_values 0 < data_bound)
    by (apply Hvalid; assumption).
  assert (Hdata_j_valid : 0 <= Znth j data_values 0 < data_bound)
    by (apply Hvalid; assumption).
  assert (Hdata_i_ne_j :
    Znth i data_values 0 <> Znth j data_values 0).
  {
    intro Heq.
    assert (i = j) by (eapply Hunique; eauto).
    contradiction.
  }
  unfold heap_pos_consistent.
  split; [exact Hbound |].
  split.
  - unfold heap_swap_pos.
    rewrite !Zlength_replace_Znth by
      (try assumption; lia).
    exact Hpos_len.
  - split.
    + unfold heap_data_valid.
      intros index Hindex.
      rewrite Znth_heap_swap_values by lia.
      apply Hvalid.
      apply swap_source_range; assumption.
    + split.
      * unfold heap_pos_backlinks.
        intros index Hindex.
        destruct (Z.eq_dec index i) as [Hidx_i | Hidx_not_i].
        -- subst index.
           rewrite Znth_heap_swap_values by lia.
           unfold swap_source.
           destruct (Z.eq_dec i i); [| contradiction].
           unfold heap_swap_pos.
           rewrite Znth_replace_Znth_Same by
             (rewrite Zlength_replace_Znth; try assumption; lia).
           reflexivity.
        -- destruct (Z.eq_dec index j) as [Hidx_j | Hidx_not_j].
           ++ subst index.
              rewrite Znth_heap_swap_values by lia.
              unfold swap_source.
              destruct (Z.eq_dec j i); [contradiction |].
              destruct (Z.eq_dec j j); [| contradiction].
              unfold heap_swap_pos.
              rewrite Znth_replace_Znth_Diff by
                (rewrite ?Zlength_replace_Znth, ?Hpos_len; try assumption;
                 intro Heq; apply Hdata_i_ne_j; symmetry; exact Heq).
              rewrite Znth_replace_Znth_Same by
                (try assumption; lia).
              reflexivity.
           ++ rewrite Znth_heap_swap_values by lia.
              unfold swap_source.
              destruct (Z.eq_dec index i); [contradiction |].
              destruct (Z.eq_dec index j); [contradiction |].
              assert (Hdata_index_valid :
                0 <= Znth index data_values 0 < data_bound)
                by (apply Hvalid; assumption).
              assert (Hdata_index_ne_i :
                Znth index data_values 0 <> Znth i data_values 0).
              {
                intro Heq.
                assert (index = i) by (eapply Hunique; eauto).
                contradiction.
              }
              assert (Hdata_index_ne_j :
                Znth index data_values 0 <> Znth j data_values 0).
              {
                intro Heq.
                assert (index = j) by (eapply Hunique; eauto).
                contradiction.
              }
              unfold heap_swap_pos.
              rewrite Znth_replace_Znth_Diff by
                (rewrite ?Zlength_replace_Znth, ?Hpos_len; try assumption;
                 intro Heq; apply Hdata_index_ne_j; symmetry; exact Heq).
              rewrite Znth_replace_Znth_Diff by
                (try assumption; lia ||
                 intro Heq; apply Hdata_index_ne_i; symmetry; exact Heq).
              apply Hback. exact Hindex.
      * unfold heap_pos_forward_links.
        intros data_x Hdata_x.
        destruct (Z.eq_dec data_x (Znth i data_values 0))
          as [Hquery_i | Hquery_not_i].
        -- right. exists j.
           subst data_x.
           split; [exact Hj |].
           split.
           ++ rewrite Znth_heap_swap_values by lia.
              unfold swap_source.
              destruct (Z.eq_dec j i); [lia |].
              destruct (Z.eq_dec j j); [reflexivity | lia].
           ++ unfold heap_swap_pos.
              rewrite Znth_replace_Znth_Diff by
                (rewrite ?Zlength_replace_Znth, ?Hpos_len; try assumption;
                 intro Heq; apply Hdata_i_ne_j; symmetry; exact Heq).
              rewrite Znth_replace_Znth_Same by
                (try assumption; lia).
              reflexivity.
        -- destruct (Z.eq_dec data_x (Znth j data_values 0))
             as [Hquery_j | Hquery_not_j].
           ++ right. exists i.
              subst data_x.
              split; [exact Hi |].
              split.
              ** rewrite Znth_heap_swap_values by lia.
                 unfold swap_source.
                 destruct (Z.eq_dec i i); [reflexivity | contradiction].
              ** unfold heap_swap_pos.
                 rewrite Znth_replace_Znth_Same by
                   (rewrite Zlength_replace_Znth; try assumption; lia).
                 reflexivity.
           ++ destruct (Hforward data_x Hdata_x)
                as [Habs | [old_index [Hold_index [Hdata Hpos_old]]]].
              ** left.
                 unfold heap_swap_pos.
                 rewrite Znth_replace_Znth_Diff by
                   (rewrite ?Zlength_replace_Znth, ?Hpos_len; try assumption;
                    intro Heq; apply Hquery_not_j; symmetry; exact Heq).
                 rewrite Znth_replace_Znth_Diff by
                   (try assumption; lia ||
                    intro Heq; apply Hquery_not_i; symmetry; exact Heq).
                 exact Habs.
              ** assert (Hold_not_i : old_index <> i).
                 {
                   intro Hold_i. subst old_index.
                   rewrite Hold_i in Hdata.
                   apply Hquery_not_i. symmetry. exact Hdata.
                 }
                 assert (Hold_not_j : old_index <> j).
                 {
                   intro Hold_j. subst old_index.
                   rewrite Hold_j in Hdata.
                   apply Hquery_not_j. symmetry. exact Hdata.
                 }
                 right. exists old_index.
                 split; [exact Hold_index |].
                 split.
                 --- rewrite Znth_heap_swap_values by lia.
                     unfold swap_source.
                     destruct (Z.eq_dec old_index i); [contradiction |].
                     destruct (Z.eq_dec old_index j); [contradiction |].
                     exact Hdata.
                 --- unfold heap_swap_pos.
                     rewrite Znth_replace_Znth_Diff by
                       (rewrite ?Zlength_replace_Znth, ?Hpos_len; try assumption;
                        intro Heq; apply Hquery_not_j; symmetry; exact Heq).
                     rewrite Znth_replace_Znth_Diff by
                       (try assumption; lia ||
                        intro Heq; apply Hquery_not_i; symmetry; exact Heq).
                     exact Hpos_old.
Qed.

Lemma heap_array_state_swap_values :
  forall M key_values data_values pos_values data_bound size i j,
    HeapArrayState M key_values data_values pos_values data_bound size ->
    0 <= i < size ->
    0 <= j < size ->
    i <> j ->
    HeapArrayState M
      (heap_swap_values i j key_values)
      (heap_swap_values i j data_values)
      (heap_swap_pos data_values pos_values i j)
      data_bound size.
Proof.
  intros M key_values data_values pos_values data_bound size i j
    Harray Hi Hj Hneq.
  destruct Harray as [Hsize_nonneg [Hcapacity [Hmap Hpos]]].
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  unfold HeapArrayState.
  split; [exact Hsize_nonneg |].
  split; [exact Hcapacity |].
  split.
  - apply heap_map_relation_swap_values; try assumption.
    repeat split; assumption.
  - apply heap_pos_consistent_swap_values; try assumption.
Qed.

Lemma selected_child_left :
  forall key_values size index,
    0 <= index ->
    index < size ->
    heap_left_child index < size ->
    (heap_right_child index >= size \/
     Znth (heap_left_child index) key_values 0 <=
       Znth (heap_right_child index) key_values 0) ->
    SelectedChild key_values size index (heap_left_child index).
Proof.
  intros key_values size index Hindex Hindex_bound Hleft_bound Hselect.
  unfold SelectedChild.
  assert (Hleft_pos : 0 < heap_left_child index).
  { unfold heap_left_child. lia. }
  assert (Hparent_left :
      heap_parent (heap_left_child index) = index)
    by (apply heap_parent_left_child; lia).
  repeat split.
  - exact Hindex.
  - exact Hindex_bound.
  - unfold heap_left_child. lia.
  - lia.
  - exact Hleft_bound.
  - exact Hparent_left.
  - unfold heap_selected_child.
    destruct (Z_lt_dec (heap_right_child index) size)
      as [Hright | Hright].
    + destruct Hselect as [Houtside | Hvalues]; [lia |].
      destruct
        (Z.leb
          (Znth (heap_left_child index) key_values 0)
          (Znth (heap_right_child index) key_values 0)) eqn:Hcmp.
      * reflexivity.
      * apply Z.leb_gt in Hcmp. lia.
    + reflexivity.
  - intros child [Hchild_pos [Hchild_bound Hparent]].
    pose proof
      (heap_children_characterization
        index child Hindex Hchild_pos Hparent)
      as [-> | ->].
    + lia.
    + destruct Hselect as [Houtside | Hvalues].
      * lia.
      * exact Hvalues.
Qed.

Lemma selected_child_right :
  forall key_values size index,
    0 <= index ->
    index < size ->
    heap_right_child index < size ->
    Znth (heap_right_child index) key_values 0 <
      Znth (heap_left_child index) key_values 0 ->
    SelectedChild key_values size index (heap_right_child index).
Proof.
  intros key_values size index Hindex Hindex_bound Hright_bound Hvalues.
  unfold SelectedChild.
  assert (Hright_pos : 0 < heap_right_child index).
  { unfold heap_right_child. lia. }
  assert (Hparent_right :
      heap_parent (heap_right_child index) = index)
    by (apply heap_parent_right_child; lia).
  repeat split.
  - exact Hindex.
  - exact Hindex_bound.
  - unfold heap_right_child. lia.
  - lia.
  - exact Hright_bound.
  - exact Hparent_right.
  - unfold heap_selected_child.
    destruct (Z_lt_dec (heap_right_child index) size); [|lia].
    destruct
      (Z.leb
        (Znth (heap_left_child index) key_values 0)
        (Znth (heap_right_child index) key_values 0)) eqn:Hcmp.
    + apply Z.leb_le in Hcmp. lia.
    + reflexivity.
  - intros child [Hchild_pos [Hchild_bound Hparent]].
    pose proof
      (heap_children_characterization
        index child Hindex Hchild_pos Hparent)
      as [-> | ->].
    + lia.
    + lia.
Qed.

Lemma selected_child_current_lt :
  forall key_values size index selected,
    SelectedChild key_values size index selected ->
    index < selected.
Proof.
  intros key_values size index selected Hselected.
  unfold SelectedChild in Hselected.
  tauto.
Qed.

Lemma sift_up_swap_state :
  forall M key_values data_values pos_values data_bound size child parent,
    SiftUpState M key_values data_values pos_values data_bound size child ->
    0 < child ->
    parent = heap_parent child ->
    Znth parent key_values 0 > Znth child key_values 0 ->
    SiftUpState M
      (heap_swap_values parent child key_values)
      (heap_swap_values parent child data_values)
      (heap_swap_pos data_values pos_values parent child)
      data_bound size parent.
Proof.
  intros M key_values data_values pos_values data_bound size child parent
    Hstate Hchild_pos Hparent Hstrict.
  destruct Hstate as [Harray [Hchild_range [Hexcept Hchildren]]].
  destruct Harray as [Hsize_nonneg [Hcapacity [Hmap Hpos]]].
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  unfold HeapOrderExceptUp in Hexcept.
  destruct Hexcept as [_ [_ Hexcept_edges]].
  unfold PushHoleChildrenPreserved in Hchildren.
  pose proof
    (heap_parent_positive_bounds child size Hchild_pos (proj2 Hchild_range))
    as [Hparent_nonneg [Hparent_lt Hparent_bound]].
  rewrite <- Hparent in Hparent_nonneg, Hparent_lt, Hparent_bound.
  assert (Hparent_ne_child : parent <> child) by lia.
  set (key_swapped := heap_swap_values parent child key_values).
  set (data_swapped := heap_swap_values parent child data_values).
  set (pos_swapped := heap_swap_pos data_values pos_values parent child).
  assert (Hkey_swap_parent :
    Znth parent key_swapped 0 = Znth child key_values 0).
  {
    subst key_swapped.
    rewrite Znth_heap_swap_values by lia.
    unfold swap_source.
    destruct (Z.eq_dec parent parent); [reflexivity | contradiction].
  }
  assert (Hkey_swap_child :
    Znth child key_swapped 0 = Znth parent key_values 0).
  {
    subst key_swapped.
    rewrite Znth_heap_swap_values by lia.
    unfold swap_source.
    destruct (Z.eq_dec child parent); [lia |].
    destruct (Z.eq_dec child child); [reflexivity | contradiction].
  }
  assert (Hkey_swap_other :
    forall node,
      0 <= node < size ->
      node <> parent ->
      node <> child ->
      Znth node key_swapped 0 = Znth node key_values 0).
  {
    intros node Hnode Hnode_parent Hnode_child.
    subst key_swapped.
    rewrite Znth_heap_swap_values by lia.
    unfold swap_source.
    destruct (Z.eq_dec node parent); [contradiction |].
    destruct (Z.eq_dec node child); [contradiction |].
    reflexivity.
  }
  assert (Harray_swapped :
    HeapArrayState M key_swapped data_swapped pos_swapped data_bound size).
  {
    assert (Hmap_original :
      heap_map_relation M key_values data_values size)
      by (repeat split; assumption).
    assert (Harray_original :
      HeapArrayState M key_values data_values pos_values data_bound size)
      by (exact (conj Hsize_nonneg (conj Hcapacity (conj Hmap_original Hpos)))).
    subst key_swapped data_swapped pos_swapped.
    apply heap_array_state_swap_values; try exact Harray_original; lia.
  }
  unfold SiftUpState.
  split; [exact Harray_swapped |].
  split; [lia |].
  split.
  - unfold HeapOrderExceptUp.
    split; [exact Hparent_nonneg |].
    split; [exact Hparent_bound |].
    intros node [Hnode_pos [Hnode_bound Hnode_ne_parent]].
    pose proof
      (heap_parent_positive_bounds node size Hnode_pos Hnode_bound)
      as [Hnode_parent_nonneg [Hnode_parent_lt Hnode_parent_bound]].
    destruct (Z.eq_dec node child) as [Hnode_child | Hnode_ne_child].
    + subst node.
      rewrite <- Hparent.
      rewrite Hkey_swap_parent, Hkey_swap_child.
      lia.
    + assert (Hnode_same :
        Znth node key_swapped 0 = Znth node key_values 0)
        by (apply Hkey_swap_other; lia).
      assert (Hold :
        Znth (heap_parent node) key_values 0 <=
        Znth node key_values 0).
      {
        apply Hexcept_edges.
        repeat split; assumption.
      }
      destruct (Z.eq_dec (heap_parent node) parent)
        as [Hnode_parent_eq | Hnode_parent_ne].
      * rewrite Hnode_parent_eq, Hkey_swap_parent, Hnode_same.
        rewrite Hnode_parent_eq in Hold.
        lia.
      * destruct (Z.eq_dec (heap_parent node) child)
          as [Hnode_parent_child | Hnode_parent_ne_child].
        -- rewrite Hnode_parent_child, Hkey_swap_child, Hnode_same.
           assert (Hpreserved :
             Znth (heap_parent child) key_values 0 <=
             Znth node key_values 0).
           {
             apply Hchildren.
             repeat split; assumption.
           }
           rewrite <- Hparent in Hpreserved.
           exact Hpreserved.
        -- assert (Hnode_parent_same :
             Znth (heap_parent node) key_swapped 0 =
             Znth (heap_parent node) key_values 0)
             by (apply Hkey_swap_other; lia).
           rewrite Hnode_parent_same, Hnode_same.
           exact Hold.
  - unfold PushHoleChildrenPreserved.
    intros node [Hnode_pos [Hnode_bound Hnode_parent]].
    pose proof
      (heap_parent_positive_bounds node size Hnode_pos Hnode_bound)
      as [Hnode_parent_nonneg [Hnode_parent_lt Hnode_parent_bound]].
    destruct (Z.eq_dec parent 0) as [Hparent_zero | Hparent_nonzero].
    + rewrite Hparent_zero in Hkey_swap_parent, Hkey_swap_child, Hstrict.
      rewrite Hparent_zero.
      destruct (Z.eq_dec node child) as [Hnode_child | Hnode_ne_child].
      * rewrite Hnode_child.
        change (Znth 0 key_swapped 0 <= Znth child key_swapped 0).
        rewrite Hkey_swap_parent, Hkey_swap_child.
        lia.
      * assert (Hnode_ne_parent : node <> parent) by lia.
        assert (Hnode_same :
          Znth node key_swapped 0 = Znth node key_values 0)
          by (apply Hkey_swap_other; lia).
        assert (Hold :
          Znth (heap_parent node) key_values 0 <=
          Znth node key_values 0).
        {
          apply Hexcept_edges.
          repeat split; assumption.
        }
        rewrite Hnode_parent, Hparent_zero in Hold.
        change (Znth 0 key_swapped 0 <= Znth node key_swapped 0).
        rewrite Hkey_swap_parent, Hnode_same.
        lia.
    + assert (Hparent_pos : 0 < parent) by lia.
      pose proof
        (heap_parent_positive_bounds parent size Hparent_pos Hparent_bound)
        as [Hgrand_nonneg [Hgrand_lt Hgrand_bound]].
      assert (Hgrand_same :
        Znth (heap_parent parent) key_swapped 0 =
        Znth (heap_parent parent) key_values 0)
        by (apply Hkey_swap_other; lia).
      assert (Hparent_order :
        Znth (heap_parent parent) key_values 0 <=
        Znth parent key_values 0).
      {
        apply Hexcept_edges.
        repeat split; try lia.
      }
      destruct (Z.eq_dec node child) as [Hnode_child | Hnode_ne_child].
      * subst node.
        rewrite Hgrand_same, Hkey_swap_child.
        exact Hparent_order.
      * assert (Hnode_ne_parent : node <> parent) by lia.
        assert (Hnode_same :
          Znth node key_swapped 0 = Znth node key_values 0)
          by (apply Hkey_swap_other; lia).
        assert (Hold :
          Znth parent key_values 0 <= Znth node key_values 0).
        {
          pose proof
            (Hexcept_edges node
              ltac:(repeat split; try assumption; lia)) as Hold0.
          rewrite Hnode_parent in Hold0.
          exact Hold0.
        }
        rewrite Hgrand_same, Hnode_same.
        eapply Z.le_trans; eauto.
Qed.

Lemma sift_down_swap_state :
  forall M key_values data_values pos_values data_bound size current selected,
    SiftDownState M key_values data_values pos_values data_bound size current ->
    SelectedChild key_values size current selected ->
    Znth current key_values 0 > Znth selected key_values 0 ->
    SiftDownState M
      (heap_swap_values current selected key_values)
      (heap_swap_values current selected data_values)
      (heap_swap_pos data_values pos_values current selected)
      data_bound size selected.
Proof.
  intros M key_values data_values pos_values data_bound size current selected
    Hstate Hselected Hstrict.
  destruct Hstate as [Harray [Hcurrent_range [Hexcept Hparent_hole]]].
  destruct Harray as [Hsize_nonneg [Hcapacity [Hmap Hpos]]].
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  unfold SelectedChild in Hselected.
  destruct Hselected as
    (Hselected_current_nonneg & Hselected_current_bound &
     Hcurrent_lt_selected & Hselected_nonneg & Hselected_bound &
     Hselected_parent & Hselected_choice & Hselected_dominates).
  unfold HeapOrderExceptDown in Hexcept.
  destruct Hexcept as [_ [_ Hexcept_edges]].
  set (key_swapped := heap_swap_values current selected key_values).
  set (data_swapped := heap_swap_values current selected data_values).
  set (pos_swapped := heap_swap_pos data_values pos_values current selected).
  assert (Hcurrent_ne_selected : current <> selected) by lia.
  assert (Hkey_swap_current :
    Znth current key_swapped 0 = Znth selected key_values 0).
  {
    subst key_swapped.
    rewrite Znth_heap_swap_values by lia.
    unfold swap_source.
    destruct (Z.eq_dec current current); [reflexivity | contradiction].
  }
  assert (Hkey_swap_selected :
    Znth selected key_swapped 0 = Znth current key_values 0).
  {
    subst key_swapped.
    rewrite Znth_heap_swap_values by lia.
    unfold swap_source.
    destruct (Z.eq_dec selected current); [lia |].
    destruct (Z.eq_dec selected selected); [reflexivity | contradiction].
  }
  assert (Hkey_swap_other :
    forall node,
      0 <= node < size ->
      node <> current ->
      node <> selected ->
      Znth node key_swapped 0 = Znth node key_values 0).
  {
    intros node Hnode Hnode_current Hnode_selected.
    subst key_swapped.
    rewrite Znth_heap_swap_values by lia.
    unfold swap_source.
    destruct (Z.eq_dec node current); [contradiction |].
    destruct (Z.eq_dec node selected); [contradiction |].
    reflexivity.
  }
  assert (Harray_swapped :
    HeapArrayState M key_swapped data_swapped pos_swapped data_bound size).
  {
    assert (Hmap_original :
      heap_map_relation M key_values data_values size)
      by (repeat split; assumption).
    assert (Harray_original :
      HeapArrayState M key_values data_values pos_values data_bound size)
      by (exact (conj Hsize_nonneg (conj Hcapacity (conj Hmap_original Hpos)))).
    subst key_swapped data_swapped pos_swapped.
    apply heap_array_state_swap_values; try exact Harray_original; lia.
  }
  unfold SiftDownState.
  split; [exact Harray_swapped |].
  split; [lia |].
  split.
  - unfold HeapOrderExceptDown.
    split; [exact Hselected_nonneg |].
    split; [exact Hselected_bound |].
    intros child [Hchild_pos [Hchild_bound Hchild_parent_not_selected]].
    pose proof
      (heap_parent_positive_bounds child size Hchild_pos Hchild_bound)
      as [Hparent_nonneg [Hparent_lt Hparent_bound]].
    destruct (Z.eq_dec (heap_parent child) current)
      as [Hparent_current | Hparent_not_current].
    + destruct (Z.eq_dec child selected)
        as [Hchild_selected | Hchild_not_selected].
      * subst child.
        rewrite Hparent_current.
        rewrite Hkey_swap_current, Hkey_swap_selected.
        lia.
      * assert (Hchild_not_current : child <> current) by lia.
        rewrite Hparent_current.
        rewrite Hkey_swap_current.
        rewrite Hkey_swap_other by lia.
        apply Hselected_dominates.
        repeat split; assumption.
    + destruct (Z.eq_dec child current)
        as [Hchild_current | Hchild_not_current].
      * subst child.
        rewrite Hkey_swap_other by lia.
        rewrite Hkey_swap_current.
        destruct Hparent_hole as [Hcurrent_zero | Hparent_dominates].
        -- lia.
        -- apply Hparent_dominates.
           repeat split.
           ++ lia.
           ++ exact Hselected_bound.
           ++ exact Hselected_parent.
      * assert (Hchild_not_selected : child <> selected).
        {
          intro Hchild_selected.
          subst child.
          contradiction.
        }
        rewrite Hkey_swap_other by lia.
        rewrite Hkey_swap_other by lia.
        apply Hexcept_edges.
        repeat split; assumption.
  - unfold PopHoleParentDominatesChildren.
    right.
    intros child [Hchild_pos [Hchild_bound Hchild_parent_selected]].
    pose proof
      (heap_parent_positive_bounds child size Hchild_pos Hchild_bound)
      as [Hparent_nonneg [Hparent_lt Hparent_bound]].
    assert (Hchild_not_selected : child <> selected) by lia.
    assert (Hchild_not_current : child <> current) by lia.
    rewrite Hselected_parent.
    rewrite Hkey_swap_current.
    rewrite Hkey_swap_other by lia.
    specialize
      (Hexcept_edges child
        ltac:(repeat split; try assumption; lia)).
    rewrite Hchild_parent_selected in Hexcept_edges.
    exact Hexcept_edges.
Qed.

Lemma sift_up_state_heap_representation_at_root :
  forall M key_values data_values pos_values data_bound size child,
    child <= 0 ->
    SiftUpState M key_values data_values pos_values data_bound size child ->
    heap_representation M key_values data_values pos_values data_bound size.
Proof.
  intros M key_values data_values pos_values data_bound size child
    Hroot Hstate.
  destruct Hstate as [Harray [Hchild_range [Hexcept _]]].
  destruct Harray as [Hsize_nonnegative [Hcapacity [Hmap Hpos]]].
  unfold HeapOrderExceptUp in Hexcept.
  destruct Hexcept as [_ [_ Hexcept_order]].
  unfold heap_representation.
  split; [assumption |].
  split; [assumption |].
  split; [assumption |].
  split.
  - unfold heap_ordered.
    intros node [Hnode_positive Hnode_bound].
    destruct (Z.eq_dec node child) as [-> | Hnot_child].
    + lia.
    + apply Hexcept_order. repeat split; assumption.
  - assumption.
Qed.

Lemma sift_up_state_heap_representation_at_break :
  forall M key_values data_values pos_values data_bound size child parent,
    0 < child ->
    parent = heap_parent child ->
    Znth parent key_values 0 <= Znth child key_values 0 ->
    SiftUpState M key_values data_values pos_values data_bound size child ->
    heap_representation M key_values data_values pos_values data_bound size.
Proof.
  intros M key_values data_values pos_values data_bound size child parent
    Hchild Hparent Hdominates Hstate.
  destruct Hstate as [Harray [Hchild_range [Hexcept _]]].
  destruct Harray as [Hsize_nonnegative [Hcapacity [Hmap Hpos]]].
  unfold HeapOrderExceptUp in Hexcept.
  destruct Hexcept as [_ [_ Hexcept_order]].
  unfold heap_representation.
  split; [assumption |].
  split; [assumption |].
  split; [assumption |].
  split.
  - unfold heap_ordered.
    intros node [Hnode_positive Hnode_bound].
    destruct (Z.eq_dec node child) as [-> | Hnot_child].
    + rewrite <- Hparent. exact Hdominates.
    + apply Hexcept_order. repeat split; assumption.
  - assumption.
Qed.

Lemma sift_down_state_heap_representation_at_leaf :
  forall M key_values data_values pos_values data_bound size index,
    heap_left_child index >= size ->
    SiftDownState M key_values data_values pos_values data_bound size index ->
    heap_representation M key_values data_values pos_values data_bound size.
Proof.
  intros M key_values data_values pos_values data_bound size index
    Hleaf Hstate.
  destruct Hstate as [Harray [Hindex_range [Hexcept _]]].
  destruct Harray as [Hsize_nonnegative [Hcapacity [Hmap Hpos]]].
  unfold HeapOrderExceptDown in Hexcept.
  destruct Hexcept as [Hindex_nonnegative [_ Hexcept_order]].
  unfold heap_representation.
  split; [assumption |].
  split; [assumption |].
  split; [assumption |].
  split.
  - unfold heap_ordered.
    intros child [Hchild_positive Hchild_bound].
    destruct (Z.eq_dec (heap_parent child) index) as [Hparent | Hnot_parent].
    + pose proof
        (heap_children_characterization
          index child Hindex_nonnegative Hchild_positive Hparent)
        as [Hleft | Hright].
      * unfold heap_left_child in Hleaf.
        rewrite Hleft in Hchild_bound.
        unfold heap_left_child in Hchild_bound.
        lia.
      * unfold heap_left_child, heap_right_child in *.
        rewrite Hright in Hchild_bound.
        lia.
    + apply Hexcept_order. repeat split; assumption.
  - assumption.
Qed.

Lemma sift_down_state_heap_representation_at_break :
  forall M key_values data_values pos_values data_bound size index selected,
    Znth index key_values 0 <= Znth selected key_values 0 ->
    SelectedChild key_values size index selected ->
    SiftDownState M key_values data_values pos_values data_bound size index ->
    heap_representation M key_values data_values pos_values data_bound size.
Proof.
  intros M key_values data_values pos_values data_bound size index selected
    Hdominates Hselected Hstate.
  destruct Hstate as [Harray [Hindex_range [Hexcept _]]].
  destruct Harray as [Hsize_nonnegative [Hcapacity [Hmap Hpos]]].
  unfold HeapOrderExceptDown in Hexcept.
  destruct Hexcept as [_ [_ Hexcept_order]].
  unfold SelectedChild in Hselected.
  destruct Hselected as
    (_ & _ & _ & _ & _ & _ & _ & Hselected_min).
  unfold heap_representation.
  split; [assumption |].
  split; [assumption |].
  split; [assumption |].
  split.
  - unfold heap_ordered.
    intros child [Hchild_positive Hchild_bound].
    destruct (Z.eq_dec (heap_parent child) index) as [Hparent | Hnot_parent].
    + rewrite Hparent.
      eapply Z.le_trans.
      * exact Hdominates.
      * apply Hselected_min. repeat split; assumption.
    + apply Hexcept_order. repeat split; assumption.
  - assumption.
Qed.

Lemma heap_map_relation_absent_not_in_data :
  forall M key_values data_values size data_x,
    heap_map_relation M key_values data_values size ->
    partial_map_absent M data_x ->
    forall index,
      0 <= index < size ->
      Znth index data_values 0 <> data_x.
Proof.
  intros M key_values data_values size data_x Hmap Habs index Hindex Heq.
  destruct Hmap as [_ [_ [_ [Hindex_present _]]]].
  specialize (Hindex_present index Hindex).
  unfold partial_map_absent, partial_map_get in Habs.
  unfold partial_map_present, partial_map_get in Hindex_present.
  rewrite Heq in Hindex_present.
  congruence.
Qed.

Lemma heap_data_unique_snoc :
  forall data_values size data_x,
    Zlength data_values = size ->
    heap_data_unique data_values size ->
    (forall index, 0 <= index < size -> Znth index data_values 0 <> data_x) ->
    heap_data_unique (data_values ++ [data_x]) (size + 1).
Proof.
  intros data_values size data_x Hdata_len Hunique Hnotin i j Hi Hj Heq.
  destruct (Z.eq_dec i size) as [Hi_size | Hi_not_size];
  destruct (Z.eq_dec j size) as [Hj_size | Hj_not_size].
  - lia.
  - subst i.
    assert (Hj_old : 0 <= j < size) by lia.
    rewrite app_Znth2 in Heq by (rewrite Hdata_len; lia).
    rewrite Hdata_len in Heq.
    replace (size - size) with 0 in Heq by lia.
    simpl in Heq.
    rewrite app_Znth1 in Heq by (rewrite Hdata_len; lia).
    symmetry in Heq.
    exfalso. eapply Hnotin; eauto.
  - subst j.
    assert (Hi_old : 0 <= i < size) by lia.
    rewrite app_Znth1 in Heq by (rewrite Hdata_len; lia).
    rewrite app_Znth2 in Heq by (rewrite Hdata_len; lia).
    rewrite Hdata_len in Heq.
    replace (size - size) with 0 in Heq by lia.
    simpl in Heq.
    exfalso. eapply Hnotin; eauto.
  - assert (Hi_old : 0 <= i < size) by lia.
    assert (Hj_old : 0 <= j < size) by lia.
    rewrite app_Znth1 in Heq by (rewrite Hdata_len; lia).
    rewrite app_Znth1 in Heq by (rewrite Hdata_len; lia).
    eapply Hunique; eauto.
Qed.

Lemma heap_map_relation_add_snoc :
  forall M key_values data_values size data_x key_x,
    heap_map_relation M key_values data_values size ->
    partial_map_absent M data_x ->
    heap_map_relation
      (partial_map_add M data_x key_x)
      (key_values ++ [key_x])
      (data_values ++ [data_x])
      (size + 1).
Proof.
  intros M key_values data_values size data_x key_x Hmap Habs.
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  pose proof
    (heap_map_relation_absent_not_in_data
      M key_values data_values size data_x
      (conj Hkey_len (conj Hdata_len
        (conj Hunique (conj Hindex_present Hpresent_index))))
      Habs) as Hnotin.
  unfold heap_map_relation.
  repeat split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - apply heap_data_unique_snoc; assumption.
  - intros index Hindex.
    destruct (Z.eq_dec index size) as [Hidx_last | Hidx_old].
    + subst index.
      rewrite app_Znth2 by lia.
      rewrite app_Znth2 by lia.
      rewrite Hkey_len, Hdata_len.
      replace (size - size) with 0 by lia.
      rewrite !Znth0_cons.
      unfold partial_map_present, partial_map_get, partial_map_add.
      destruct (Z.eq_dec data_x data_x); congruence.
    + assert (Hidx_range : 0 <= index < size) by lia.
      rewrite app_Znth1 by lia.
      rewrite app_Znth1 by lia.
      unfold partial_map_present, partial_map_get, partial_map_add.
      destruct
        (Z.eq_dec (Znth index data_values 0) data_x)
        as [Heq | Hneq].
      * exfalso. now apply (Hnotin index Hidx_range).
      * apply Hindex_present. exact Hidx_range.
  - intros query key Hpresent.
    unfold partial_map_present, partial_map_get, partial_map_add in Hpresent.
    destruct (Z.eq_dec query data_x) as [Hquery | Hquery].
    + subst query.
      injection Hpresent as Hkey_eq.
      subst key.
      assert (Hsize_nonnegative : 0 <= size) by
        (rewrite <- Hdata_len; apply Zlength_nonneg).
      exists size.
      repeat split; try lia.
      * rewrite app_Znth2 by lia.
        rewrite Hdata_len.
        replace (size - size) with 0 by lia.
        rewrite Znth0_cons.
        reflexivity.
      * rewrite app_Znth2 by lia.
        rewrite Hkey_len.
        replace (size - size) with 0 by lia.
        rewrite Znth0_cons.
        reflexivity.
    + specialize (Hpresent_index query key Hpresent)
        as [index [Hidx [Hdata Hkey]]].
      exists index.
      repeat split; try lia.
      * rewrite app_Znth1 by lia. exact Hdata.
      * rewrite app_Znth1 by lia. exact Hkey.
Qed.

Lemma heap_pos_consistent_add_snoc :
  forall data_values pos_values data_bound size data_x,
    Zlength data_values = size ->
    heap_pos_consistent data_values pos_values data_bound size ->
    heap_data_unique data_values size ->
    (forall index, 0 <= index < size -> Znth index data_values 0 <> data_x) ->
    0 <= data_x < data_bound ->
    heap_pos_consistent
      (data_values ++ [data_x])
      (replace_Znth data_x size pos_values)
      data_bound
      (size + 1).
Proof.
	  intros data_values pos_values data_bound size data_x
	    Hdata_len Hpos Hunique Hnotin Hdata_x.
	  destruct Hpos as
	    [Hdata_bound [Hpos_len [Hvalid [Hback Hforward]]]].
	  assert (Hsize_nonnegative : 0 <= size) by
	    (rewrite <- Hdata_len; apply Zlength_nonneg).
	  unfold heap_pos_consistent.
	  split; [exact Hdata_bound |].
	  split; [rewrite Zlength_replace_Znth by (rewrite Hpos_len; lia);
	          exact Hpos_len |].
	  split.
	  - unfold heap_data_valid.
	    intros idx Hidx.
	    destruct (Z.eq_dec idx size) as [Hlast | Hold].
	    + subst idx.
	      rewrite app_Znth2 by (rewrite Hdata_len; lia).
      rewrite Hdata_len.
      replace (size - size) with 0 by lia.
      exact Hdata_x.
	    + assert (Hidx_old : 0 <= idx < size) by lia.
	      rewrite app_Znth1 by (rewrite Hdata_len; lia).
	      apply Hvalid. exact Hidx_old.
	  - split.
	  + unfold heap_pos_backlinks.
	    intros idx Hidx.
	    destruct (Z.eq_dec idx size) as [Hlast | Hold].
	    * subst idx.
	      rewrite app_Znth2 by (rewrite Hdata_len; lia).
	      rewrite Hdata_len.
	      replace (size - size) with 0 by lia.
	      rewrite Znth_replace_Znth_Same by (rewrite Hpos_len; exact Hdata_x).
	      reflexivity.
	    * assert (Hidx_old : 0 <= idx < size) by lia.
	      assert (Hdata_valid : 0 <= Znth idx data_values 0 < data_bound)
	        by (apply Hvalid; exact Hidx_old).
      rewrite app_Znth1 by (rewrite Hdata_len; lia).
	      rewrite (Znth_replace_Znth_Diff
	        absent pos_values data_x (Znth idx data_values 0) size).
	      apply Hback. exact Hidx_old.
	      -- rewrite Hpos_len. exact Hdata_x.
	      -- rewrite Hpos_len. exact Hdata_valid.
	      -- intro Heq. apply (Hnotin idx Hidx_old). symmetry. exact Heq.
	  + unfold heap_pos_forward_links.
	    intros query Hquery.
	    destruct (Z.eq_dec query data_x) as [Hquery_data | Hquery_data].
	    * subst query.
	      right. exists size.
	      split; [lia |].
	      split.
	      -- rewrite app_Znth2 by (rewrite Hdata_len; lia).
	         rewrite Hdata_len.
	         replace (size - size) with 0 by lia.
	         rewrite Znth0_cons.
	         reflexivity.
	      -- rewrite Znth_replace_Znth_Same by (rewrite Hpos_len; exact Hdata_x).
	         reflexivity.
	    * destruct (Hforward query Hquery)
	        as [Habs | [old_index [Hidx [Hdata Hposq]]]].
	      -- left.
	         rewrite (Znth_replace_Znth_Diff
	           absent pos_values data_x query size).
	         exact Habs.
	         ++ rewrite Hpos_len. exact Hdata_x.
	         ++ rewrite Hpos_len. exact Hquery.
	         ++ intro Heq. apply Hquery_data. symmetry. exact Heq.
	      -- right. exists old_index.
	         split; [lia |].
	         split.
	         ++ rewrite app_Znth1 by (rewrite Hdata_len; lia). exact Hdata.
	         ++ rewrite (Znth_replace_Znth_Diff
	              absent pos_values data_x query size).
	            exact Hposq.
	            ** rewrite Hpos_len. exact Hdata_x.
	            ** rewrite Hpos_len. exact Hquery.
	            ** intro Heq. apply Hquery_data. symmetry. exact Heq.
Qed.

Lemma push_write_state_from_heap_representation :
  forall M key_values data_values pos_values data_bound size data_x key_x,
    heap_representation M key_values data_values pos_values data_bound size ->
    partial_map_absent M data_x ->
    0 <= data_x < data_bound ->
    size + 1 <= heap_capacity ->
    PushWriteState M
      (key_values ++ [key_x])
      (data_values ++ [data_x])
      (replace_Znth data_x size pos_values)
      data_bound size data_x key_x.
Proof.
  intros M key_values data_values pos_values data_bound size data_x key_x
    Hrep Habs Hdata_x Hcapacity_next.
  destruct Hrep as [Hsize [Hcapacity [Hmap [Hordered Hpos]]]].
  pose proof Hmap as Hmap_copy.
  destruct Hmap_copy as
    [Hkey_len [Hdata_len [Hunique _]]].
  pose proof
    (heap_map_relation_absent_not_in_data
      M key_values data_values size data_x Hmap Habs) as Hnotin.
  unfold PushWriteState.
  split; [exact Habs |].
  split.
	- unfold SiftUpState.
	  split.
	  + unfold HeapArrayState.
	    split; [lia |].
	    split; [exact Hcapacity_next |].
	    split.
	    * apply heap_map_relation_add_snoc; assumption.
	    * apply heap_pos_consistent_add_snoc; assumption.
    + split.
      * lia.
      * split.
        -- unfold HeapOrderExceptUp.
           repeat split; try lia.
           intros node [Hnode_positive [Hnode_bound Hnode_not_child]].
           assert (Hnode_old : 0 <= node < size) by lia.
           pose proof
             (heap_parent_positive_bounds node size
               Hnode_positive ltac:(lia)) as
             [Hparent_nonnegative [Hparent_lt_node Hparent_lt_size]].
           rewrite app_Znth1 by lia.
           rewrite app_Znth1 by lia.
           apply Hordered. lia.
        -- unfold PushHoleChildrenPreserved.
           intros node [Hnode_positive [Hnode_bound Hparent]].
           pose proof
             (heap_parent_positive_bounds node (size + 1)
               Hnode_positive Hnode_bound) as
             [_ [Hparent_lt_node _]].
           rewrite Hparent in Hparent_lt_node.
           lia.
  - split.
    + rewrite app_Znth2 by lia.
      rewrite Hkey_len.
      replace (size - size) with 0 by lia.
      reflexivity.
    + split.
      * rewrite app_Znth2 by lia.
        rewrite Hdata_len.
        replace (size - size) with 0 by lia.
        reflexivity.
      * destruct Hpos as [_ [Hpos_len _]].
	        rewrite Znth_replace_Znth_Same by (rewrite Hpos_len; exact Hdata_x).
	        reflexivity.
Qed.

Lemma heap_parent_zero :
  heap_parent 0 = 0.
Proof.
  reflexivity.
Qed.

Lemma heap_key_at_index_from_relation :
  forall M key_values data_values size index data_x key_x,
    heap_map_relation M key_values data_values size ->
    0 <= index < size ->
    Znth index data_values 0 = data_x ->
    partial_map_present M data_x key_x ->
    Znth index key_values 0 = key_x.
Proof.
  intros M key_values data_values size index data_x key_x
    Hmap Hindex Hdata Hpresent.
  destruct Hmap as [_ [_ [_ [Hindex_present _]]]].
  specialize (Hindex_present index Hindex).
  unfold partial_map_present, partial_map_get in *.
  rewrite Hdata in Hindex_present.
  congruence.
Qed.

Lemma decrease_key_new_le_old_index :
  forall M key_values data_values size index data_x key_x,
    heap_map_relation M key_values data_values size ->
    0 <= index < size ->
    Znth index data_values 0 = data_x ->
    partial_map_decrease_key_pre M data_x key_x ->
    key_x <= Znth index key_values 0.
Proof.
  intros M key_values data_values size index data_x key_x
    Hmap Hindex Hdata Hpre.
  unfold partial_map_decrease_key_pre, decrease_key_pre in Hpre.
  destruct Hpre as [old_key [Hpresent Hle]].
  pose proof
    (heap_key_at_index_from_relation
      M key_values data_values size index data_x old_key
      Hmap Hindex Hdata Hpresent) as Hold.
  lia.
Qed.

Lemma heap_index_of_from_heap_representation :
  forall M key_values data_values pos_values data_bound size data_x key_x,
    heap_representation M key_values data_values pos_values data_bound size ->
    0 <= data_x < data_bound ->
    partial_map_decrease_key_pre M data_x key_x ->
    heap_index_of
      M data_values pos_values data_x (Znth data_x pos_values 0) /\
    0 <= Znth data_x pos_values 0 < size.
Proof.
  intros M key_values data_values pos_values data_bound size data_x key_x
    Hrep Hdata_x Hpre.
  destruct Hrep as [Hsize [Hcapacity [Hmap [Hordered Hpos]]]].
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  destruct Hpos as [Hbound [Hpos_len [Hvalid [Hback Hforward]]]].
  unfold partial_map_decrease_key_pre, decrease_key_pre in Hpre.
  destruct Hpre as [old_key [Hpresent Hle]].
  specialize (Hpresent_index data_x old_key Hpresent)
    as [index [Hindex [Hdata Hkey]]].
  assert (Hpos_absent_default :
    Znth data_x pos_values 0 = Znth data_x pos_values absent).
  {
    apply Znth_indep.
    rewrite Hpos_len. exact Hdata_x.
  }
  assert (Hpos_index : Znth data_x pos_values 0 = index).
  {
    rewrite Hpos_absent_default.
    rewrite <- Hdata.
    apply Hback. exact Hindex.
  }
  rewrite Hpos_index.
  split.
  - unfold heap_index_of, heap_data_present, heap_contains_data.
    split.
    + exists old_key. exact Hpresent.
    + split.
      * rewrite Hdata_len. exact Hindex.
      * split; [exact Hdata |].
        rewrite <- Hdata.
        apply Hback. exact Hindex.
  - exact Hindex.
Qed.

Lemma heap_map_relation_update_key :
  forall M key_values data_values size index data_x key_x,
    heap_map_relation M key_values data_values size ->
    0 <= index < size ->
    Znth index data_values 0 = data_x ->
    heap_map_relation
      (partial_map_update M data_x key_x)
      (replace_Znth index key_x key_values)
      data_values
      size.
Proof.
  intros M key_values data_values size index data_x key_x
    Hmap Hindex Hdata_at_index.
	  destruct Hmap as
	    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
	  unfold heap_map_relation.
	  split; [rewrite Zlength_replace_Znth by (rewrite Hkey_len; exact Hindex);
	          exact Hkey_len |].
	  split; [exact Hdata_len |].
	  split; [exact Hunique |].
	  split.
  - intros idx Hidx.
    unfold partial_map_present, partial_map_get,
      partial_map_update, partial_map_add.
    destruct (Z.eq_dec (Znth idx data_values 0) data_x)
      as [Hsame_data | Hdiff_data].
    + assert (idx = index) as ->.
      {
        apply Hunique; try assumption.
        rewrite Hsame_data, Hdata_at_index. reflexivity.
      }
      rewrite Znth_replace_Znth_Same by (rewrite Hkey_len; exact Hindex).
      destruct (Z.eq_dec data_x data_x); congruence.
    + assert (idx <> index) as Hidx_ne_index.
      {
        intro Heq. subst idx.
        apply Hdiff_data. exact Hdata_at_index.
      }
      rewrite (Znth_replace_Znth_Diff
        0 key_values index idx key_x).
      * destruct (Z.eq_dec (Znth idx data_values 0) data_x);
          [contradiction |].
        apply Hindex_present. exact Hidx.
      * rewrite Hkey_len. exact Hindex.
      * rewrite Hkey_len. exact Hidx.
      * intro Heq. apply Hidx_ne_index. symmetry. exact Heq.
  - intros query key Hpresent.
    unfold partial_map_present, partial_map_get,
      partial_map_update, partial_map_add in Hpresent.
    destruct (Z.eq_dec query data_x) as [Hquery_data | Hquery_data].
    + subst query.
      injection Hpresent as Hkey_eq.
      subst key.
      exists index.
      split; [exact Hindex |].
      split; [exact Hdata_at_index |].
      rewrite Znth_replace_Znth_Same by (rewrite Hkey_len; exact Hindex).
      reflexivity.
    + specialize (Hpresent_index query key Hpresent)
        as [idx [Hidx [Hdata Hkey]]].
      assert (index <> idx) as Hindex_ne_idx.
      {
        intro Heq. subst idx.
        apply Hquery_data.
        rewrite <- Hdata.
        exact Hdata_at_index.
      }
      exists idx.
      split; [exact Hidx |].
      split; [exact Hdata |].
      rewrite (Znth_replace_Znth_Diff
        0 key_values index idx key_x).
      * exact Hkey.
      * rewrite Hkey_len. exact Hindex.
      * rewrite Hkey_len. exact Hidx.
      * exact Hindex_ne_idx.
Qed.

Lemma heap_order_except_up_after_decrease :
  forall M key_values data_values size index data_x key_x,
    heap_map_relation M key_values data_values size ->
    heap_ordered key_values size ->
    partial_map_decrease_key_pre M data_x key_x ->
    0 <= index < size ->
    Znth index data_values 0 = data_x ->
    HeapOrderExceptUp
      (replace_Znth index key_x key_values)
      size
      index.
Proof.
  intros M key_values data_values size index data_x key_x
    Hmap Hordered Hpre Hindex Hdata.
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  unfold heap_ordered in Hordered.
  assert (Hmap_full :
    heap_map_relation M key_values data_values size).
  {
    repeat split; assumption.
  }
  pose proof
    (decrease_key_new_le_old_index
      M key_values data_values size index data_x key_x
      Hmap_full Hindex Hdata Hpre) as Hnew_le_old.
  unfold HeapOrderExceptUp.
  split; [lia |].
  split; [lia |].
  intros node [Hnode_positive [Hnode_bound Hnode_not_index]].
  pose proof
    (heap_parent_positive_bounds node size Hnode_positive Hnode_bound)
    as [Hparent_nonnegative [Hparent_lt_node Hparent_lt_size]].
  destruct (Z.eq_dec (heap_parent node) index) as [Hparent_index | Hparent_not_index].
  - rewrite Hparent_index.
    rewrite Znth_replace_Znth_Same by (rewrite Hkey_len; exact Hindex).
    rewrite (Znth_replace_Znth_Diff 0 key_values index node key_x).
	    + eapply Z.le_trans.
	      * exact Hnew_le_old.
	      * rewrite <- Hparent_index.
	        apply Hordered. lia.
    + rewrite Hkey_len. exact Hindex.
    + rewrite Hkey_len. lia.
    + intro Heq. apply Hnode_not_index. symmetry. exact Heq.
  - rewrite (Znth_replace_Znth_Diff
      0 key_values index (heap_parent node) key_x).
    + rewrite (Znth_replace_Znth_Diff 0 key_values index node key_x).
      * apply Hordered. lia.
      * rewrite Hkey_len. exact Hindex.
      * rewrite Hkey_len. lia.
      * intro Heq. apply Hnode_not_index. symmetry. exact Heq.
    + rewrite Hkey_len. exact Hindex.
    + rewrite Hkey_len. lia.
    + intro Heq. apply Hparent_not_index. symmetry. exact Heq.
Qed.

Lemma push_hole_children_preserved_after_decrease :
  forall M key_values data_values size index data_x key_x,
    heap_map_relation M key_values data_values size ->
    heap_ordered key_values size ->
    partial_map_decrease_key_pre M data_x key_x ->
    0 <= index < size ->
    Znth index data_values 0 = data_x ->
    PushHoleChildrenPreserved
      (replace_Znth index key_x key_values)
      size
      index.
Proof.
  intros M key_values data_values size index data_x key_x
    Hmap Hordered Hpre Hindex Hdata.
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  unfold heap_ordered in Hordered.
  assert (Hmap_full :
    heap_map_relation M key_values data_values size).
  {
    repeat split; assumption.
  }
  pose proof
    (decrease_key_new_le_old_index
      M key_values data_values size index data_x key_x
      Hmap_full Hindex Hdata Hpre) as Hnew_le_old.
  unfold PushHoleChildrenPreserved.
  intros node [Hnode_positive [Hnode_bound Hparent_node]].
  pose proof
    (heap_parent_positive_bounds node size Hnode_positive Hnode_bound)
    as [_ [Hparent_lt_node _]].
  assert (Hnode_not_index : node <> index) by lia.
  rewrite Hparent_node in Hparent_lt_node.
  destruct (Z.eq_dec (heap_parent index) index)
    as [Hparent_index_self | Hparent_index_not_self].
  - rewrite Hparent_index_self.
    rewrite Znth_replace_Znth_Same by (rewrite Hkey_len; exact Hindex).
    rewrite (Znth_replace_Znth_Diff 0 key_values index node key_x).
	    + eapply Z.le_trans.
	      * exact Hnew_le_old.
	      * rewrite <- Hparent_node.
	        apply Hordered. lia.
    + rewrite Hkey_len. exact Hindex.
    + rewrite Hkey_len. lia.
    + intro Heq. apply Hnode_not_index. symmetry. exact Heq.
  - assert (Hindex_positive : 0 < index).
	    {
	      destruct (Z.eq_dec index 0) as [Hidx_zero | Hidx_not_zero].
	      - subst index. exfalso.
	        apply Hparent_index_not_self.
	        rewrite Hidx_zero. apply heap_parent_zero.
	      - lia.
	    }
    pose proof
      (heap_parent_positive_bounds index size Hindex_positive ltac:(lia))
      as [Hparent_index_nonnegative [_ Hparent_index_lt_size]].
    rewrite (Znth_replace_Znth_Diff
      0 key_values index (heap_parent index) key_x).
    + rewrite (Znth_replace_Znth_Diff 0 key_values index node key_x).
	      * eapply Z.le_trans.
	        -- apply Hordered. lia.
	        -- rewrite <- Hparent_node.
	           apply Hordered. lia.
      * rewrite Hkey_len. exact Hindex.
      * rewrite Hkey_len. lia.
      * intro Heq. apply Hnode_not_index. symmetry. exact Heq.
    + rewrite Hkey_len. exact Hindex.
    + rewrite Hkey_len. lia.
    + intro Heq. apply Hparent_index_not_self. symmetry. exact Heq.
Qed.

Lemma decrease_key_write_state_from_heap_representation :
  forall M key_values data_values pos_values data_bound size data_x key_x index,
    heap_representation M key_values data_values pos_values data_bound size ->
    partial_map_decrease_key_pre M data_x key_x ->
    heap_index_of M data_values pos_values data_x index ->
    0 <= index < size ->
    DecreaseKeyWriteState M
      (replace_Znth index key_x key_values)
      data_values
      pos_values
      data_bound size data_x key_x index.
Proof.
  intros M key_values data_values pos_values data_bound size data_x key_x index
    Hrep Hpre Hindex_of Hindex.
  destruct Hrep as [Hsize [Hcapacity [Hmap [Hordered Hpos]]]].
  destruct Hindex_of as [_ [_ [Hdata_at_index _]]].
  unfold DecreaseKeyWriteState.
  split; [exact Hindex |].
  split; [exact Hdata_at_index |].
  split; [exact Hpre |].
  split.
  - unfold SiftUpState.
    split.
    + unfold HeapArrayState.
      split; [exact Hsize |].
      split; [exact Hcapacity |].
      split.
      * apply heap_map_relation_update_key; assumption.
      * exact Hpos.
    + split; [exact Hindex |].
      split.
      * apply heap_order_except_up_after_decrease with
          (M := M) (data_values := data_values) (data_x := data_x);
          assumption.
      * apply push_hole_children_preserved_after_decrease with
          (M := M) (data_values := data_values) (data_x := data_x);
          assumption.
  - destruct Hmap as [Hkey_len _].
    rewrite Znth_replace_Znth_Same by (rewrite Hkey_len; exact Hindex).
    reflexivity.
Qed.

Lemma partial_map_absent_from_negative_pos :
  forall M key_values data_values pos_values data_bound size data_x,
    heap_representation M key_values data_values pos_values data_bound size ->
    0 <= data_x < data_bound ->
    Znth data_x pos_values 0 < 0 ->
    partial_map_absent M data_x.
Proof.
  intros M key_values data_values pos_values data_bound size data_x
    Hrep Hdata_x Hpos_negative.
  destruct Hrep as [Hsize [Hcapacity [Hmap [Hordered Hpos]]]].
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  destruct Hpos as [Hbound [Hpos_len [Hvalid [Hback Hforward]]]].
  unfold partial_map_absent, partial_map_get.
  destruct (M data_x) as [old_key |] eqn:HM; [| reflexivity].
  exfalso.
  assert (Hpresent : partial_map_present M data_x old_key) by exact HM.
  specialize (Hpresent_index data_x old_key Hpresent)
    as [index [Hindex [Hdata Hkey]]].
  assert (Hpos_default :
    Znth data_x pos_values 0 = Znth data_x pos_values absent).
  {
    apply Znth_indep.
    rewrite Hpos_len. exact Hdata_x.
  }
  rewrite Hpos_default in Hpos_negative.
  assert (Hpos_index : Znth data_x pos_values absent = index).
  {
    rewrite <- Hdata.
    apply Hback. exact Hindex.
  }
  lia.
Qed.

Lemma partial_map_decrease_key_pre_from_nonnegative_pos :
  forall M key_values data_values pos_values data_bound size data_x key_x,
    heap_representation M key_values data_values pos_values data_bound size ->
    0 <= data_x < data_bound ->
    0 <= Znth data_x pos_values 0 ->
    partial_map_update_or_add_pre M data_x key_x ->
    partial_map_decrease_key_pre M data_x key_x.
Proof.
  intros M key_values data_values pos_values data_bound size data_x key_x
    Hrep Hdata_x Hpos_nonnegative Hpre.
  unfold partial_map_update_or_add_pre, update_or_push_pre in Hpre.
  destruct Hpre as [Habs | Hdec]; [| exact Hdec].
  exfalso.
  destruct Hrep as [Hsize [Hcapacity [Hmap [Hordered Hpos]]]].
  destruct Hmap as
    [Hkey_len [Hdata_len [Hunique [Hindex_present Hpresent_index]]]].
  destruct Hpos as [Hbound [Hpos_len [Hvalid [Hback Hforward]]]].
  assert (Hpos_default :
    Znth data_x pos_values 0 = Znth data_x pos_values absent).
  {
    apply Znth_indep.
    rewrite Hpos_len. exact Hdata_x.
  }
  specialize (Hforward data_x Hdata_x) as [Hpos_abs | [index [Hindex [Hdata Hpos_index]]]].
  - rewrite Hpos_default, Hpos_abs in Hpos_nonnegative.
    unfold absent in Hpos_nonnegative. lia.
  - specialize (Hindex_present index Hindex) as Hpresent.
    rewrite Hdata in Hpresent.
    unfold heap_data_absent, partial_map_absent, partial_map_get in Habs.
    unfold partial_map_present, partial_map_get in Hpresent.
    congruence.
Qed.
