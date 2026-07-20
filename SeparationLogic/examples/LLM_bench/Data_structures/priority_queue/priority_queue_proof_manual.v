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
From SimpleC.EE.LLM_bench.Data_structures.priority_queue Require Import priority_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.
Local Open Scope sac.

Lemma proof_of_push_entail_wit_1 : push_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  - rewrite <- PreH4.
    rewrite replace_Znth_Znth.
    sep_apply IntArray.full_to_seg.
    cancel (IntArray.seg heap_pre 0 (n_pre + 1) l).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + apply push_loop_init_at_tail; assumption.
Qed. 

Lemma proof_of_push_entail_wit_2_split_goal_1 : push_entail_wit_2_split_goal_1.
Proof.
  pre_process.
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_push_entail_wit_2 : push_entail_wit_2.
Proof.
  pre_process.
  Exists l_cur_2.
  split_pure_spatial.
  - cancel (IntArray.seg heap_pre 0 (n_pre + 1) l_cur_2).
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_push_entail_wit_3 : push_entail_wit_3.
Proof.
  pre_process.
  Exists l_cur_2.
  split_pure_spatial.
  - cancel (IntArray.seg heap_pre 0 (n_pre + 1) l_cur_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + destruct (heap_parent_bounds_pos child ltac:(lia)) as [Hparent_nonneg _].
      exact Hparent_nonneg.
    + destruct (heap_parent_bounds_pos child ltac:(lia)) as [_ Hparent_lt].
      exact Hparent_lt.
    + pose proof (heap_parent_bounds_pos child ltac:(lia))
        as [Hparent_nonneg Hparent_lt].
      unfold HeapParent in Hparent_nonneg, Hparent_lt |- *.
      lia.
    + unfold HeapParent.
      reflexivity.
Qed. 

Lemma proof_of_push_entail_wit_4 : push_entail_wit_4.
Proof.
  pre_process.
  replace (parent - 0) with parent in PreH1 by lia.
  replace (child - 0) with child in PreH1 by lia.
  pose proof
    (push_loop_stop_to_result l l_cur_2 n_pre child parent x_pre PreH12 PreH4 PreH9 PreH1)
    as Hpush.
  Exists l_cur_2.
  split_pure_spatial.
  - cancel (IntArray.seg heap_pre 0 (n_pre + 1) l_cur_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    all: try exact Hpush.
    all: try (
      destruct Hpush as [_ [_ [_ [_ [_ [HPQ _]]]]]];
      exact HPQ
    ).
Qed. 

Lemma proof_of_push_entail_wit_5 : push_entail_wit_5.
Proof.
  pre_process.
  replace (parent - 0) with parent in PreH1 by lia.
  replace (child - 0) with child in PreH1 by lia.
  destruct PreH12 as
    [Hn0 [Hlen_before [Hlen_cur [Hchild0 [Hchildn [Hx_before [Hx_child [Hheap_before [Hperm [Hexcept Hchildren]]]]]]]]]].
  destruct Hexcept as [Hexcept0 [Hexcept_bound Hexcept_ord]].
  set (l_cur_2 :=
    replace_Znth child (Znth parent l_cur 0)
      (replace_Znth parent (Znth child l_cur 0) l_cur)).
  assert (Hparent_range : 0 <= parent < Zlength l_cur) by (rewrite Hlen_cur; lia).
  assert (Hchild_range : 0 <= child < Zlength l_cur) by (rewrite Hlen_cur; lia).
  assert (Hswap_parent :
    Znth parent l_cur_2 0 = Znth child l_cur 0).
  {
    unfold l_cur_2.
    rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  assert (Hswap_child :
    Znth child l_cur_2 0 = Znth parent l_cur 0).
  {
    unfold l_cur_2.
    rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  }
  assert (Hswap_other :
    forall k,
      0 <= k < Zlength l_cur ->
      k <> parent ->
      k <> child ->
      Znth k l_cur_2 0 = Znth k l_cur 0).
  {
    intros k Hk Hk_parent Hk_child.
    unfold l_cur_2.
    rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
  }
  Exists l_cur_2.
  split_pure_spatial.
  - sep_apply IntArray.full_to_seg.
    + unfold l_cur_2 in *.
      replace (parent - 0) with parent by lia.
      replace (child - 0) with child by lia.
      cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + replace (parent - 0) with parent by lia.
      rewrite Hswap_child.
      reflexivity.
    + unfold PushLoopState.
      split; [exact Hn0|].
      split; [exact Hlen_before|].
      split.
      * unfold l_cur_2.
        repeat rewrite Zlength_replace_Znth.
        exact Hlen_cur.
      * split; [lia|].
        split; [lia|].
        split; [exact Hx_before|].
        split.
        { rewrite Hswap_parent.
          exact Hx_child. }
        split; [exact Hheap_before|].
        split.
        { eapply Permutation_trans.
          - exact Hperm.
          - unfold l_cur_2.
            apply permutation_swap_Znth; rewrite Hlen_cur; lia.
        }
        split.
        { unfold HeapOrderExceptUp.
          split; [lia|].
          split.
          - lia.
          - intros node [Hnode_pos [Hnode_bound Hnode_neq_parent]].
            destruct (Z.eq_dec node child) as [Hnode_child | Hnode_not_child].
            + subst node.
              rewrite <- PreH9.
              rewrite Hswap_parent, Hswap_child.
              lia.
            + destruct (Z.eq_dec (HeapParent node) child) as [Hparent_child | Hparent_not_child].
              * rewrite Hparent_child.
                rewrite Hswap_child.
                rewrite Hswap_other by (try lia; exact Hnode_neq_parent; exact Hnode_not_child).
                rewrite PreH9.
                apply Hchildren.
                lia.
	              * destruct (Z.eq_dec (HeapParent node) parent) as [Hparent_parent | Hparent_other].
	                -- rewrite Hparent_parent.
	                   rewrite Hswap_parent.
	                   rewrite Hswap_other by (try lia; exact Hnode_neq_parent; exact Hnode_not_child).
	                   assert (Znth parent l_cur 0 >= Znth node l_cur 0).
	                   { rewrite <- Hparent_parent. apply Hexcept_ord. lia. }
	                   lia.
	                -- destruct (heap_parent_bounds_pos node Hnode_pos)
	                     as [Hnode_parent0 Hnode_parentlt].
	                   rewrite Hswap_other by (try lia; exact Hparent_other; exact Hparent_not_child).
	                   rewrite Hswap_other by (try lia; exact Hnode_neq_parent; exact Hnode_not_child).
	                   apply Hexcept_ord.
	                   lia.
        }
	        { unfold PushHoleChildrenPreserved.
	          intros node [Hnode_pos [Hnode_bound Hnode_parent]].
	          destruct (Z.eq_dec parent 0) as [Hparent_zero | Hparent_nonzero].
	          - rewrite Hparent_zero in *.
	            assert (Hhp0 : HeapParent 0 = 0) by (vm_compute; reflexivity).
	            rewrite Hhp0.
	            rewrite Hswap_parent.
	            destruct (Z.eq_dec node child) as [Hnode_child | Hnode_not_child].
	            + subst node.
	              rewrite Hswap_child.
	              lia.
	            + rewrite Hswap_other by (try lia; exact Hnode_not_child; lia).
	              assert (Znth 0 l_cur 0 >= Znth node l_cur 0).
	              {
	                replace (Znth 0 l_cur 0) with (Znth (HeapParent node) l_cur 0).
	                2:{ rewrite Hnode_parent. reflexivity. }
	                apply Hexcept_ord.
	                lia.
	              }
	              lia.
	          - assert (Hgp_parent :
	              Znth (HeapParent parent) l_cur 0 >= Znth parent l_cur 0).
	            { apply Hexcept_ord. lia. }
	            destruct (heap_parent_bounds_pos parent) as [Hgp0 Hgplt]; try lia.
	            rewrite Hswap_other by (try lia; exact Hparent_nonzero; intro Heq; subst; lia).
	            destruct (Z.eq_dec node child) as [Hnode_child | Hnode_not_child].
	            + subst node.
	              rewrite Hswap_child.
	              exact Hgp_parent.
	            + assert (Hnode_not_parent : node <> parent).
	              {
	                intro Heq.
	                subst node.
	                destruct (heap_parent_bounds_pos parent) as [_ Hparent_lt]; try lia.
	              }
	              rewrite Hswap_other by (try lia; exact Hnode_not_parent; exact Hnode_not_child).
	              assert (Znth parent l_cur 0 >= Znth node l_cur 0).
	              { rewrite <- Hnode_parent. apply Hexcept_ord. lia. }
	              lia.
        }
    + intros idx Hidx.
      destruct (Z.eq_dec idx parent) as [-> | Hidx_parent].
      * rewrite Hswap_parent.
        apply PreH13.
        rewrite Hlen_cur in Hchild_range.
        exact Hchild_range.
      * destruct (Z.eq_dec idx child) as [-> | Hidx_child].
	        { rewrite Hswap_child.
	          apply PreH13.
	          rewrite Hlen_cur in Hparent_range.
	          exact Hparent_range.
	        }
	        { assert (Hidx_cur : 0 <= idx < Zlength l_cur) by (rewrite Hlen_cur; exact Hidx).
	          rewrite (Hswap_other idx Hidx_cur Hidx_parent Hidx_child).
	          apply PreH13.
	          exact Hidx.
	        }
Qed. 

Lemma proof_of_push_entail_wit_6 : push_entail_wit_6.
Proof.
  pre_process.
  Exists l_cur_2.
  split_pure_spatial.
  - cancel (IntArray.seg heap_pre 0 (n_pre + 1) l_cur_2).
  - split_pures.
    all: dump_pre_spatial; unfold PushLoopState in *; intuition auto; try lia.
Qed. 

Lemma proof_of_push_entail_wit_7_1 : push_entail_wit_7_1.
Proof.
  pre_process.
  assert (child = 0) by lia.
  subst child.
  pose proof (push_loop_root_to_result l l_cur n_pre x_pre PreH8) as Hpush.
  Exists l_cur.
  split_pure_spatial.
  - cancel (IntArray.seg heap_pre 0 (n_pre + 1) l_cur).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    all: try exact Hpush.
    all: try (
      destruct Hpush as [_ [_ [_ [_ [_ [HPQ _]]]]]];
      exact HPQ
    ).
Qed. 

Lemma proof_of_push_entail_wit_7_2_split_goal_1 : push_entail_wit_7_2_split_goal_1.
Proof.
  pre_process.
  apply PreH12.
  exact H.
Qed.

Lemma proof_of_push_entail_wit_7_2 : push_entail_wit_7_2.
Proof.
  pre_process.
  Exists l_cur.
  split_pure_spatial.
  - cancel (IntArray.seg heap_pre 0 (n_pre + 1) l_cur).
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_push_return_wit_1_split_goal_1 : push_return_wit_1_split_goal_1.
Proof.
  pre_process.
  apply PreH7.
  exact H.
Qed.

Lemma proof_of_push_return_wit_1 : push_return_wit_1.
Proof.
  pre_process.
  Exists l_out_2.
  split_pure_spatial.
  - cancel (IntArray.seg heap_pre 0 (n_pre + 1) l_out_2).
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_build_entail_wit_1 : build_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre l).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + apply build_prefix_state_init_one; lia.
    + apply priority_queue_prefix_one; lia.
Qed. 

Lemma proof_of_build_entail_wit_2 : build_entail_wit_2.
Proof.
  pre_process.
  Exists heap_l.
  split_pure_spatial.
  - apply IntArray.full_split_to_seg; lia.
  - split_pures.
    all: dump_pre_spatial; unfold PriorityQueuePrefix in *; intuition auto; try lia.
Qed. 

Lemma proof_of_build_entail_wit_3 : build_entail_wit_3.
Proof.
  pre_process.
  pose proof PreH1 as Hpush_old.
  pose proof PreH10 as Hbuild_old.
  destruct PreH1 as
    [_ [Hprefix_before_len [Hprefix_out_len [_ [_ [_ _]]]]]].
  destruct PreH10 as
    [_ [_ [Hcur_len [_ [_ _]]]]].
  assert (Hbuild_new :
    BuildPrefixState l
      (l_out ++ sublist (i + 1) n_pre heap_l_2) (i + 1)).
  {
    replace (sublist (i + 1) n_pre heap_l_2)
      with (sublist (i + 1) (Zlength heap_l_2) heap_l_2).
    2:{
      rewrite Hcur_len, PreH6.
      reflexivity.
    }
    eapply build_prefix_state_extend_after_push; try exact Hbuild_old;
      try exact Hpush_old.
    lia.
  }
  assert (HPQ_new :
    PriorityQueuePrefix (l_out ++ sublist (i + 1) n_pre heap_l_2) (i + 1)).
  {
    destruct Hbuild_new as [_ [_ [_ [HPQ_new _]]]].
    exact HPQ_new.
  }
  assert (Hrange_new :
    forall idx, 0 <= idx < n_pre ->
      INT_MIN <= Znth idx (l_out ++ sublist (i + 1) n_pre heap_l_2) 0 <= INT_MAX).
  {
    intros idx Hidx.
    destruct (Z_lt_ge_dec idx (i + 1)) as [Hlt | Hge].
    - rewrite app_Znth1 by lia.
      apply PreH3.
      lia.
    - rewrite app_Znth2 by (rewrite Hprefix_out_len; lia).
      rewrite Znth_sublist by lia.
      replace (idx - (i + 1) + (i + 1)) with idx by lia.
      apply PreH13.
      lia.
  }
  Exists (l_out ++ sublist (i + 1) n_pre heap_l_2).
  split_pure_spatial.
  - sep_apply (IntArray.seg_merge_to_seg
      heap_pre 0 (i + 1) n_pre l_out (sublist (i + 1) n_pre heap_l_2));
      [|lia].
    sep_apply (IntArray.seg_to_full
      heap_pre 0 n_pre (l_out ++ sublist (i + 1) n_pre heap_l_2)).
    replace (heap_pre + 0 * sizeof ( INT )) with heap_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    entailer!.
  - split_pures.
    + dump_pre_spatial; exact PreH4.
    + dump_pre_spatial; exact PreH5.
    + dump_pre_spatial; exact PreH6.
    + dump_pre_spatial; exact PreH7.
    + dump_pre_spatial; exact PreH8.
    + rewrite PreH9.
      pose proof (PreH13 i ltac:(lia)) as Hrange_i.
      destruct Hrange_i as [Hrange_i _].
      dump_pre_spatial.
      exact Hrange_i.
    + rewrite PreH9.
      pose proof (PreH13 i ltac:(lia)) as Hrange_i.
      destruct Hrange_i as [_ Hrange_i].
      dump_pre_spatial.
      exact Hrange_i.
    + dump_pre_spatial; exact Hbuild_new.
    + dump_pre_spatial; exact HPQ_new.
    + dump_pre_spatial; exact Hrange_new.
Qed. 

Lemma proof_of_build_entail_wit_4_split_goal_1 : build_entail_wit_4_split_goal_1.
Proof.
  pre_process.
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_build_entail_wit_4 : build_entail_wit_4.
Proof.
  pre_process.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_build_return_wit_1 : build_return_wit_1.
Proof.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  Exists heap_l.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l).
  - split_pures.
    all: dump_pre_spatial; auto.
Qed. 

Lemma proof_of_build_partial_solve_wit_2_pure : build_partial_solve_wit_2_pure.
Proof.
  pre_process.
  destruct PreH7 as [_ [_ [Hheap_len [_ [_ _]]]]].
  entailer!.
  - rewrite Zlength_sublist0 by (rewrite Hheap_len, PreH3; lia).
    lia.
  - rewrite Znth_sublist0 by lia.
    symmetry.
    exact PreH6.
  - rewrite PreH6.
    pose proof (PreH10 i ltac:(lia)) as Hrange_i.
    lia.
  - rewrite PreH6.
    pose proof (PreH10 i ltac:(lia)) as Hrange_i.
    lia.
  - apply sublist_prefix_preserves_max_heap.
    + lia.
    + rewrite Hheap_len, PreH3.
      lia.
    + exact PreH9.
  - intros idx Hidx.
    rewrite Znth_sublist0 by lia.
    apply PreH10; lia.
Qed. 

Lemma proof_of_pop_entail_wit_1 : pop_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre l).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + pose proof (PreH5 0 ltac:(lia)) as [? ?]; lia.
    + pose proof (PreH5 0 ltac:(lia)) as [? ?]; lia.
    + destruct PreH4 as [_ Hroot_max].
      apply Hroot_max; lia.
Qed. 

Lemma proof_of_pop_entail_wit_2 : pop_entail_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre l).
  - split_pures.
    all: dump_pre_spatial; subst; auto; try lia.
    unfold PopResult, PriorityQueuePrefix, MaxHeapPrefix; intuition auto; try lia;
      try apply Permutation_refl.
Qed. 

Lemma proof_of_pop_entail_wit_3 : pop_entail_wit_3.
Proof.
  pre_process.
  assert (Hn : 1 < n_pre) by lia.
  Exists (replace_Znth 0 (Znth (n_pre - 1) l 0) l).
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre (replace_Znth 0 (Znth (n_pre - 1) l 0) l)).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    all: try (apply pop_loop_state_init_replace_root; try assumption).
    all: try match goal with
             | |- forall idx, _ =>
                 intros idx Hidx;
                 destruct (Z.eq_dec idx 0) as [-> | Hneq];
                 [ rewrite Znth_replace_Znth_Same by lia
                 | rewrite Znth_replace_Znth_Diff by lia ];
                  apply PreH10; lia
           end.
Qed. 

Lemma proof_of_pop_entail_wit_4_split_goal_1 : pop_entail_wit_4_split_goal_1.
Proof.
  pre_process.
  apply PreH9.
  exact H.
Qed.

Lemma proof_of_pop_entail_wit_4 : pop_entail_wit_4.
Proof.
  pre_process.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_pop_entail_wit_5_split_goal_1 : pop_entail_wit_5_split_goal_1.
Proof.
  pre_process.
  apply PreH14.
  exact H.
Qed.

Lemma proof_of_pop_entail_wit_5 : pop_entail_wit_5.
Proof.
  pre_process.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_pop_entail_wit_6_3 : pop_entail_wit_6_3.
Proof.
  pre_process.
  assert (Hleft_eq : left = 2 * idx + 1) by lia.
  subst largest.
  pose proof
    (pop_selected_child_left_ge_right heap_l_2 (n_pre - 1) idx left right
      PreH9 Hleft_eq PreH12 PreH2 PreH1)
    as Hsel.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_pop_entail_wit_6_2 : pop_entail_wit_6_2.
Proof.
  pre_process.
  assert (Hleft_eq : left = 2 * idx + 1) by lia.
  pose proof
    (pop_selected_child_left_no_right heap_l_2 (n_pre - 1) idx left right
      PreH8 Hleft_eq PreH11 PreH14 PreH1)
    as Hsel.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + subst largest; exact Hsel.
Qed. 

Lemma proof_of_pop_entail_wit_6_1 : pop_entail_wit_6_1.
Proof.
  pre_process.
  assert (Hleft_eq : left = 2 * idx + 1) by lia.
  pose proof
    (pop_selected_child_right heap_l_2 (n_pre - 1) idx left right
      PreH9 Hleft_eq PreH12 PreH2 PreH1)
    as Hsel.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_pop_entail_wit_7 : pop_entail_wit_7.
Proof.
  pre_process.
  assert (Hleft_eq : left = 2 * idx + 1) by lia.
  pose proof
    (pop_selected_child_bounds heap_l_2 (n_pre - 1) idx left right largest
      PreH8 Hleft_eq PreH11 PreH14)
    as [Hleft0 [Hleft_lt [Hright0 Hright_le]]].
  pose proof
    (pop_loop_no_swap_to_ready l heap_l_2 n_pre idx largest ret
      PreH15 PreH14 PreH1 PreH7 PreH4)
    as Hready.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_pop_entail_wit_8 : pop_entail_wit_8.
Proof.
  pre_process.
  assert (Hleft_eq : left = 2 * idx + 1) by lia.
  pose proof
    (pop_selected_child_bounds heap_l (n_pre - 1) idx left right largest
      PreH8 Hleft_eq PreH11 PreH14)
    as [Hleft0 [Hleft_lt [Hright0 Hright_le]]].
  set (heap_l_2 :=
    replace_Znth largest (Znth idx heap_l 0)
      (replace_Znth idx (Znth largest heap_l 0) heap_l)).
  pose proof
    (pop_loop_swap_down_preserve l heap_l n_pre idx largest PreH15 PreH14 PreH1)
    as [Hidx_largest Hloop].
  assert (Hidx_range : 0 <= idx < Zlength heap_l).
  {
    pose proof PreH15 as Hstate.
    destruct Hstate as [_ [_ [Hcur _]]].
    rewrite Hcur.
    lia.
  }
  assert (Hlargest_range : 0 <= largest < Zlength heap_l).
  {
    pose proof PreH15 as Hstate.
    destruct Hstate as [_ [_ [Hcur _]]].
    rewrite Hcur.
    lia.
  }
  assert (Hswap_idx :
    Znth idx heap_l_2 0 = Znth largest heap_l 0).
  {
    unfold heap_l_2.
    rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  assert (Hswap_largest :
    Znth largest heap_l_2 0 = Znth idx heap_l 0).
  {
    unfold heap_l_2.
    rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  }
  assert (Hswap_other :
    forall k,
      0 <= k < Zlength heap_l ->
      k <> idx ->
      k <> largest ->
      Znth k heap_l_2 0 = Znth k heap_l 0).
  {
    intros k Hk Hk_idx Hk_largest.
    unfold heap_l_2.
    rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
  }
  Exists heap_l_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    + intros pos Hpos.
      destruct (Z.eq_dec pos idx) as [-> | Hpos_idx].
      * rewrite Hswap_idx.
        apply PreH16.
        split; [exact PreH12|].
        lia.
      * destruct (Z.eq_dec pos largest) as [-> | Hpos_largest].
        { rewrite Hswap_largest.
          apply PreH16.
          split; [exact PreH8|].
          lia.
        }
        { assert (Hpos_cur : 0 <= pos < Zlength heap_l) by
            (pose proof PreH15 as Hstate;
             destruct Hstate as [_ [_ [Hcur _]]];
             rewrite Hcur; exact Hpos).
          rewrite (Hswap_other pos Hpos_cur Hpos_idx Hpos_largest).
          apply PreH16.
          exact Hpos.
        }
Qed. 

Lemma proof_of_pop_entail_wit_9 : pop_entail_wit_9.
Proof.
  pre_process.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures.
    all: dump_pre_spatial; unfold PopLoopState in *; intuition auto; try lia.
Qed. 

Lemma proof_of_pop_entail_wit_10_1 : pop_entail_wit_10_1.
Proof.
  pre_process.
  pose proof
    (pop_loop_no_child_to_ready l heap_l_2 n_pre idx ret
      PreH13 PreH1 PreH8 PreH5)
    as Hready.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_pop_entail_wit_10_2_split_goal_1 : pop_entail_wit_10_2_split_goal_1.
Proof.
  pre_process.
  apply PreH20.
  exact H.
Qed.

Lemma proof_of_pop_entail_wit_10_2 : pop_entail_wit_10_2.
Proof.
  pre_process.
  Exists heap_l_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre heap_l_2).
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_pop_entail_wit_11 : pop_entail_wit_11.
Proof.
  pre_process.
  pose proof
    (pop_ready_final_write_to_result_with_range l heap_l n_pre ret PreH9 PreH4 PreH5 PreH10)
    as [Hpop_result Hout_range].
  Exists (replace_Znth (n_pre - 1) ret heap_l).
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre (replace_Znth (n_pre - 1) ret heap_l)).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_pop_return_wit_1_split_goal_1 : pop_return_wit_1_split_goal_1.
Proof.
  pre_process.
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_pop_return_wit_1 : pop_return_wit_1.
Proof.
  pre_process.
  Exists l_out_2.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre l_out_2).
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_pop_return_wit_2_split_goal_1 : pop_return_wit_2_split_goal_1.
Proof.
  pre_process.
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_pop_return_wit_2 : pop_return_wit_2.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  - cancel (IntArray.full heap_pre n_pre l).
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.
