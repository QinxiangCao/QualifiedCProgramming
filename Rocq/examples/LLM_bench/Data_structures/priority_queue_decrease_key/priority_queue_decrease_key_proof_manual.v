Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key Require Import priority_queue_decrease_key_goal.
From SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key Require Import priority_queue_decrease_key_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib.
Local Open Scope sac.

Local Ltac finish_entail :=
  split_pure_spatial;
  [ repeat cancel
  | split_pures;
    dump_pre_spatial;
    try lia;
    try int_auto;
    try assumption;
    try reflexivity ].

Lemma proof_of_pqdk_sift_up_entail_wit_1 : pqdk_sift_up_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_sift_up.
  Intros key_values data_values pos_values.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_up_entail_wit_2 : pqdk_sift_up_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hparent_nonnegative : 0 <= heap_parent child).
  { unfold heap_parent. apply Z.quot_pos; lia. }
  assert (Hparent_lt_child : heap_parent child < child).
  { unfold heap_parent. apply Z.quot_lt_upper_bound; lia. }
  Exists key_values_2 data_values_2 pos_values_2.
  finish_entail;
    unfold heap_parent in *;
    try lia;
    try reflexivity.
Qed.

Lemma proof_of_pqdk_sift_up_entail_wit_3 : pqdk_sift_up_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH10 as Hstate.
  destruct Hstate as [Harray _].
  destruct Harray as [_ [_ [_ Hpos]]].
  destruct Hpos as [_ [_ [Hvalid _]]].
  pose proof (Hvalid child ltac:(lia)) as Hchild_valid.
  pose proof (Hvalid parent ltac:(lia)) as Hparent_valid.
  Exists pos_values_2 data_values key_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_up_entail_wit_4 : pqdk_sift_up_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst tmp_key tmp_data.
  pose proof (sift_up_swap_state M0 key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child parent PreH16 PreH3 PreH8 PreH9) as Hswap.
  unfold heap_swap_values, heap_swap_pos in Hswap.
  Exists (replace_Znth child (Znth parent key_values_2 0)
    (replace_Znth parent (Znth child key_values_2 0) key_values_2))
    (replace_Znth child (Znth parent data_values_2 0)
    (replace_Znth parent (Znth child data_values_2 0) data_values_2))
    (replace_Znth (Znth child data_values_2 0) parent
    (replace_Znth (Znth parent data_values_2 0) child pos_values_2)).
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_up_return_wit_1 : pqdk_sift_up_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (sift_up_state_heap_representation_at_root
      M0 key_values data_values pos_values data_bound_pre n_pre child
      PreH1 PreH6) as Hrep.
  unfold store_heap.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_up_return_wit_2 : pqdk_sift_up_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (sift_up_state_heap_representation_at_break
      M0 key_values data_values pos_values data_bound_pre n_pre
      child parent PreH4 PreH9 PreH1 PreH10) as Hrep.
  unfold store_heap.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_down_safety_wit_1 : pqdk_sift_down_safety_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  entailer!.
  all: unfold heap_capacity in *; nia.
Qed.

Lemma proof_of_pqdk_sift_down_safety_wit_2 : pqdk_sift_down_safety_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  entailer!.
  all: unfold heap_capacity in *; nia.
Qed.

Lemma proof_of_pqdk_sift_down_entail_wit_1 : pqdk_sift_down_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_sift_down.
  Intros key_values data_values pos_values.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_down_entail_wit_3_1 : pqdk_sift_down_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hselected :
    SelectedChild key_values_2 n_pre current right).
  {
    subst left right smallest.
    replace (current * 2 + 1 + 1) with (heap_right_child current)
      by (unfold heap_right_child; lia).
    apply selected_child_right.
    - lia.
    - lia.
    - unfold heap_right_child. lia.
    - unfold heap_left_child, heap_right_child.
      replace (current * 2 + 2) with (current * 2 + 1 + 1)
        by lia.
      exact PreH1.
  }
  Exists data_values_2 pos_values_2 key_values_2.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_down_entail_wit_3_2 : pqdk_sift_down_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hselected :
    SelectedChild key_values_2 n_pre current smallest).
  {
    subst left right smallest.
    replace (current * 2 + 1) with (heap_left_child current)
      by (unfold heap_left_child; lia).
    apply selected_child_left.
    - lia.
    - lia.
    - unfold heap_left_child. lia.
    - left. unfold heap_right_child. lia.
  }
  Exists data_values_2 pos_values_2 key_values_2.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_down_entail_wit_3_3 : pqdk_sift_down_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hselected :
    SelectedChild key_values_2 n_pre current smallest).
  {
    subst left right smallest.
    replace (current * 2 + 1) with (heap_left_child current)
      by (unfold heap_left_child; lia).
    apply selected_child_left.
    - lia.
    - lia.
    - unfold heap_left_child. lia.
    - right.
      unfold heap_left_child, heap_right_child.
      replace (current * 2 + 2) with (current * 2 + 1 + 1)
        by lia.
      lia.
  }
  Exists data_values_2 pos_values_2 key_values_2.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_down_entail_wit_4 : pqdk_sift_down_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH11 as Hstate.
  destruct Hstate as [Harray _].
  destruct Harray as [_ [_ [_ Hpos]]].
  destruct Hpos as [_ [_ [Hvalid _]]].
  pose proof (Hvalid current ltac:(lia)) as Hcurrent_valid.
  pose proof (Hvalid smallest ltac:(lia)) as Hsmallest_valid.
  pose proof PreH10 as Hselected.
  unfold SelectedChild in Hselected.
  destruct Hselected as
    (Hcurrent_nonnegative & _ & Hcurrent_lt_smallest &
     _ & Hsmallest_bound & Hsmallest_parent & _ & _).
  assert (Hleft_bound : left < n_pre).
  {
    subst left.
    pose proof
      (heap_children_characterization
        current smallest Hcurrent_nonnegative ltac:(lia)
        Hsmallest_parent) as [Hleft | Hright].
    - unfold heap_left_child in Hleft. lia.
    - unfold heap_left_child, heap_right_child in *. lia.
  }
  Exists pos_values_2 data_values key_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_down_entail_wit_5 : pqdk_sift_down_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst tmp_key tmp_data.
  pose proof (sift_down_swap_state M0 key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current smallest PreH21 PreH20 PreH13) as Hswap.
  unfold heap_swap_values, heap_swap_pos in Hswap.
  Exists (replace_Znth smallest (Znth current key_values_2 0)
    (replace_Znth current (Znth smallest key_values_2 0) key_values_2))
    (replace_Znth smallest (Znth current data_values_2 0)
    (replace_Znth current (Znth smallest data_values_2 0) data_values_2))
    (replace_Znth (Znth smallest data_values_2 0) current
    (replace_Znth (Znth current data_values_2 0) smallest pos_values_2)).
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_down_return_wit_1 : pqdk_sift_down_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hleaf : heap_left_child current >= n_pre).
  { unfold heap_left_child. lia. }
  pose proof
    (sift_down_state_heap_representation_at_leaf
      M0 key_values data_values pos_values data_bound_pre n_pre current
      Hleaf PreH6) as Hrep.
  unfold store_heap.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_sift_down_return_wit_2 : pqdk_sift_down_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (sift_down_state_heap_representation_at_break
      M0 key_values data_values pos_values data_bound_pre n_pre
      current smallest PreH1 PreH10 PreH11) as Hrep.
  unfold store_heap.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_push_safety_wit_1 : pqdk_push_safety_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  entailer!.
  all: unfold heap_capacity in *; lia.
Qed.

Lemma proof_of_pqdk_push_entail_wit_1 : pqdk_push_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_heap.
  Intros key_values data_values pos_values.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_push_entail_wit_2 : pqdk_push_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (push_write_state_from_heap_representation
      M_before key_values data_values pos_values
      data_bound_pre n data_x_pre key_x_pre
      PreH7 PreH6 ltac:(lia) ltac:(lia)) as Hpush.
  unfold PushWriteState in Hpush.
  destruct Hpush as [_ [Hsift _]].
  unfold store_sift_up.
  Exists (app key_values (cons key_x_pre nil))
         (app data_values (cons data_x_pre nil))
         (replace_Znth data_x_pre n pos_values).
  finish_entail.
Qed.

Lemma proof_of_pqdk_decrease_key_entail_wit_1 : pqdk_decrease_key_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_heap.
  Intros key_values data_values pos_values.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_decrease_key_entail_wit_2 : pqdk_decrease_key_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (heap_index_of_from_heap_representation
      M_before key_values_2 data_values_2 pos_values
      data_bound_pre n data_x_pre key_x_pre
      PreH7 ltac:(lia) PreH6) as [Hindex_of Hindex_range].
  Exists key_values_2 data_values_2 pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_decrease_key_entail_wit_3 : pqdk_decrease_key_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (decrease_key_write_state_from_heap_representation
      M_before key_values data_values pos_values
      data_bound_pre n data_x_pre key_x_pre idx
      PreH8 PreH6 PreH7 ltac:(lia)) as Hwrite.
  unfold DecreaseKeyWriteState in Hwrite.
  destruct Hwrite as [_ [_ [_ [Hsift _]]]].
  unfold store_sift_up.
  Exists (replace_Znth idx key_x_pre key_values)
         data_values
         pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_update_or_push_entail_wit_1 : pqdk_update_or_push_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_heap.
  Intros key_values data_values pos_values.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_update_or_push_entail_wit_2 : pqdk_update_or_push_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (partial_map_absent_from_negative_pos
      M_before key_values data_values pos_values
      data_bound_pre n data_x_pre
      PreH8 ltac:(lia) PreH1) as Habs.
  unfold store_heap.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_update_or_push_entail_wit_3 : pqdk_update_or_push_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (partial_map_decrease_key_pre_from_nonnegative_pos
      M_before key_values data_values pos_values
      data_bound_pre n data_x_pre key_x_pre
      PreH8 ltac:(lia) ltac:(lia) PreH7) as Hdec.
  unfold store_heap.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_update_or_push_entail_wit_4_1 : pqdk_update_or_push_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsize :
    partial_map_update_or_add_size M_before n (n + 1)
      data_x_pre key_x_pre).
  {
    unfold partial_map_update_or_add_size.
    left. split; [exact PreH6 | lia].
  }
  Exists (n + 1).
  finish_entail.
  unfold partial_map_update_or_add, partial_map_update.
  repeat cancel.
Qed.

Lemma proof_of_pqdk_update_or_push_entail_wit_4_2 : pqdk_update_or_push_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsize :
    partial_map_update_or_add_size M_before n n
      data_x_pre key_x_pre).
  {
    unfold partial_map_update_or_add_size.
    right. split; [exact PreH6 | lia].
  }
  Exists n.
  finish_entail.
  unfold partial_map_update_or_add, partial_map_update.
  repeat cancel.
Qed.

Lemma proof_of_pqdk_pop_entail_wit_1 : pqdk_pop_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_heap.
  Intros key_values data_values pos_values.
  Exists key_values data_values pos_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_pop_entail_wit_2 : pqdk_pop_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH4 as Hrep.
  destruct Hrep as [_ [_ [_ [_ Hpos]]]].
  destruct Hpos as [_ [_ [Hvalid _]]].
  pose proof (Hvalid 0 ltac:(lia)) as Hroot_valid.
  Exists pos_values_2 data_values key_values.
  finish_entail.
Qed.

Lemma proof_of_pqdk_pop_entail_wit_3 : pqdk_pop_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst result_key result_data.
  pose proof
    (pop_marked_state_from_heap_representation
      M_before key_values_2 data_values_2 pos_values_2
      data_bound_pre n ltac:(lia) PreH9) as Hmarked.
  pose proof PreH9 as Hrep.
  destruct Hrep as [_ [_ [_ [_ Hpos]]]].
  destruct Hpos as [_ [_ [Hvalid _]]].
  pose proof (Hvalid (n - 1) ltac:(lia)) as Hlast_valid.
  unfold absent in *.
  Exists key_values_2
         (replace_Znth (Znth 0 data_values_2 0) (-1) pos_values_2)
         data_values_2
         (heap_item (Znth 0 key_values_2 0) (Znth 0 data_values_2 0)).
  finish_entail.
Qed.

Lemma proof_of_pqdk_pop_entail_wit_4 : pqdk_pop_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH11 as Hmarked.
  unfold PopMarkedState in Hmarked.
  destruct Hmarked as
    (_ & Hminimum & _ & _ & Hmap & _ & _ & _ & _).
  destruct Hmap as [Hkey_len [Hdata_len _]].
  pose proof
    (pop_root_replacement_sift_down_state
      M_before key_values data_values pos_values
      data_bound_pre n popped_2 PreH1 PreH11) as Hsift.
  pose proof Hsift as Hsift_copy.
  destruct Hsift_copy as [Harray [Hindex_range _]].
  destruct Harray as [_ [_ [_ Hpos]]].
  destruct Hpos as [_ [_ [Hvalid_new _]]].
  pose proof (Hvalid_new 0 ltac:(lia)) as Hnew_root_valid.
  sep_apply (full_retire_last_to_undef
    key_pre n capacity
    (replace_Znth 0 (Znth (n - 1) key_values 0) key_values)
    ltac:(lia) ltac:(lia)
    ltac:(rewrite Zlength_replace_Znth; exact Hkey_len)).
  sep_apply (full_retire_last_to_undef
    data_pre n capacity
    (replace_Znth 0 (Znth (n - 1) data_values 0) data_values)
    ltac:(lia) ltac:(lia)
    ltac:(rewrite Zlength_replace_Znth; exact Hdata_len)).
  unfold pop_replaced_values in Hsift, Hnew_root_valid.
  unfold store_sift_down.
  Exists popped_2
    (sublist 0 (n - 1) (replace_Znth 0 (Znth (n - 1) key_values 0) key_values))
    (sublist 0 (n - 1) (replace_Znth 0 (Znth (n - 1) data_values 0) data_values))
    (replace_Znth (Znth (n - 1) data_values 0) 0 pos_values).
  finish_entail.
Qed.

Lemma proof_of_pqdk_pop_return_wit_1 : pqdk_pop_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst n result_key result_data.
  pose proof
    (heap_root_is_partial_map_minimum
      M_before key_values data_values pos_values
      data_bound_pre 1 ltac:(lia) PreH9) as Hminimum.
  pose proof
    (heap_representation_remove_singleton
      M_before key_values data_values pos_values
      data_bound_pre PreH9) as Hremoved.
  pose proof PreH9 as Hrep.
  destruct Hrep as [_ [_ [Hmap _]]].
  destruct Hmap as [Hkey_len [Hdata_len _]].
  sep_apply (singleton_full_to_empty_undef
    key_pre capacity key_values ltac:(lia) Hkey_len).
  sep_apply (singleton_full_to_empty_undef
    data_pre capacity data_values ltac:(lia) Hdata_len).
  unfold store_heap.
  unfold absent in *.
  Exists (Znth 0 data_values 0) (heap_item (Znth 0 key_values 0) (Znth 0 data_values 0)) (Znth 0 key_values 0).
  Exists (@nil Z) (@nil Z)
         (replace_Znth (Znth 0 data_values 0) (-1) pos_values).
  finish_entail.
  replace (1 - 1) with 0 by lia.
  repeat cancel.
Qed.
