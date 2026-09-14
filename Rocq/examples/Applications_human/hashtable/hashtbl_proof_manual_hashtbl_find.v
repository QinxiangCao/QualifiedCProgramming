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
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_goal.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.hashtable.hashtbl_lib.
Local Open Scope sac.

Lemma proof_of_hashtbl_find_entail_wit_1_split_goal_1 : hashtbl_find_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (proj2 (Z.rem_bound_pos retval 211 PreH1 ltac:(lia))).
Qed.

Lemma proof_of_hashtbl_find_entail_wit_1_split_goal_2 : hashtbl_find_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.rem_nonneg; lia.
Qed.

Lemma proof_of_hashtbl_find_entail_wit_1 : hashtbl_find_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hashtbl_find_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_hashtbl_find_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_hashtbl_find_entail_wit_2 : hashtbl_find_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hidx : 0 <= retval % 211 < 211) by lia.
  prop_apply_p (PtrArray.full_Zlength bucks_ph 211 lh_2).
  Intros_p Hlen.
  assert (Hidxlen : 0 <= retval % 211 < Zlength lh_2) by lia.
  assert (Hbucket : exists l2,
             b_2 (retval % 211) =
               Some (Znth (retval % 211) lh_2 0, l2)).
  {
    apply (proj2 (PreH8 (retval % 211)
                    (Znth (retval % 211) lh_2 0))).
    split; [exact Hidxlen | reflexivity].
  }
  destruct Hbucket as [l2 Hb].
  sep_apply_l_atomic
    (PtrArray.full_split_to_missing_i
       bucks_ph (retval % 211) 211 lh_2 0 Hidx).
  sep_apply_l_atomic
    (store_map_split store_sll (retval % 211)
       (Znth (retval % 211) lh_2 0, l2) b_2 Hb).
  sep_apply_l_atomic
    (sll_Znth0__find_setup (Znth (retval % 211) lh_2 0) l2).
  Intros_p Hhead.
  Exists (Znth (retval % 211) lh_2 0) (@nil Z) l2
    b_2 lh_2 l_2 bucks_ph top_ph_2 m_node_2.
  replace (sizeof(PTR)) with ptr_size_Z by reflexivity.
  simpl sllbseg.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. rewrite PreH5. reflexivity.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. simpl. exact Hb.
    + dump_pre_spatial. simpl. exact Hhead.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. unfold not_key. intros p k1 Hin. inversion Hin.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial. apply PreH10. exact Hidx.
    + dump_pre_spatial. apply PreH10. exact Hidx.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_hashtbl_find_entail_wit_3 : hashtbl_find_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct l2_2 as [|i_v_head l_tail].
  - simpl sll.
    Intros_p Hzero.
    contradiction.
  - simpl sll.
    Intros p_next.
    assert (Hnext_nonnull :
              &(i_v_3 # "blist" ->ₛ "next") <> 0) by assumption.
    subst i_v_head.
    assert (Hin_bucket : In i_v_3 (l1_2 ++ i_v_3 :: l_tail)).
    {
      apply in_or_app.
      right; simpl; auto.
    }
    assert (Hkey : exists k_cur,
               hash_string k_cur mod NBUCK = ind /\
               m_node_2 k_cur = Some i_v_3).
    {
      apply (proj2 (PreH11 ind i_v_3)).
      exists (Znth ind lh_2 0), (l1_2 ++ i_v_3 :: l_tail).
      split; [exact PreH7 | exact Hin_bucket].
    }
    destruct Hkey as [k_cur [Hkey_hash Hkey]].
    destruct
      (map_composable_node_value_lookup__find_traversal
         m_node_2 m1 m2 k_cur i_v_3 PreH6 PreH5 Hkey)
      as [vp Hvp].
    sep_apply_l_atomic
      (store_map_split store_name k_cur i_v_3 m_node_2 Hkey).
    unfold store_name.
    Intros kp.
    sep_apply_l_atomic
      (store_map_split store_uint
         (&(i_v_3 # "blist" ->ₛ "val")) vp m2 Hvp).
    destruct l1_2 as [|h_val t_l1].
    + simpl sllbseg.
      Intros_p Hcell_nonnull.
      Intros_p Hcell_eq.
      Right.
      Exists p_next kp vp (@nil Z) b_2 lh_2 l_2 bucks_ph_2
        top_ph_2 k_cur i_v_3 l_tail (i_v_3 :: l_tail) m_node_2.
      simpl sllbseg.
      split_pure_spatial.
      * repeat cancel.
      * split_pures;
          dump_pre_spatial;
          simpl in *;
          try assumption;
          try reflexivity;
          try congruence;
          try lia.
    + simpl sllbseg.
      Intros_p Hcell_nonnull.
      Intros_p Hhval_nonnull.
      Left.
      Exists p_next kp vp h_val t_l1 (h_val :: t_l1) b_2 lh_2 l_2
        bucks_ph_2 top_ph_2 k_cur i_v_3 l_tail (i_v_3 :: l_tail)
        m_node_2.
      replace (sizeof(PTR)) with ptr_size_Z by reflexivity.
      unfold ptr_size_Z, Arch32.ptr_size_Z, Arch32.ptr_size.
      split_pure_spatial.
      * cancel (i # Ptr |-> i_v_3).
        cancel (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top_ph_2).
        cancel (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks_ph_2).
        cancel (dll top_ph_2 0 l_2).
        cancel (PtrArray.missing_i bucks_ph_2 ind 0 211 lh_2).
        cancel (store_map_missing_i store_sll b_2 ind).
        cancel ((bucks_ph_2 + ind * Z.of_nat 4) # Ptr |-> h_val).
        cancel (sllbseg &(h_val # "blist" ->ₛ "next") i t_l1).
        cancel.
      * split_pures;
          dump_pre_spatial;
          simpl in *;
          try assumption;
          try reflexivity;
          try congruence;
          try lia.
Qed.

Lemma proof_of_hashtbl_find_entail_wit_6_1 : hashtbl_find_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).

  prop_apply_p
    (PtrArray.full_Zlength bucks_ph_2 211
       (replace_Znth ind h_val lh_2)).
  Intros_p Hlen.
  rewrite Zlength_replace_Znth in Hlen.
  assert (Hrange : 0 <= ind < Zlength lh_2) by lia.
  assert (Hreplace : replace_Znth ind h_val lh_2 = lh_2).
  { apply (replace_Znth_id__find_return_found lh_2 ind 0 h_val);
      [exact Hrange | symmetry; exact PreH14]. }
  rewrite Hreplace.

  assert (Hin_bucket : In h_val (l1_2 ++ l2_2)).
  { rewrite PreH13. simpl. auto. }
  assert (Hkey_hval : exists key,
      hash_string key mod NBUCK = ind /\
      m_node_2 key = Some h_val).
  { apply (proj2 (PreH17 ind h_val)).
    exists (Znth ind lh_2 0), (l1_2 ++ l2_2).
    split; assumption. }
  destruct Hkey_hval as [key_hval [_ Hmap_hval]].
  assert (Hin_hval : In h_val l_2).
  { apply (proj1 (PreH15 h_val)).
    exists key_hval. exact Hmap_hval. }
  prop_apply_p
    (dll_member_nonnull__find_return
       top_ph_2 0 l_2 h_val Hin_hval).
  Intros_p Hhval.

  assert (Hin_current : In i_v_2 l_2).
  { apply (proj1 (PreH15 i_v_2)).
    exists k_cur. exact PreH9. }
  prop_apply_p
    (dll_member_nonnull__find_return
       top_ph_2 0 l_2 i_v_2 Hin_current).
  Intros_p Hcurrent.

  assert (Hcell : bucks_ph_2 + ind * sizeof(PTR) <> NULL).
  { apply PreH19. unfold NBUCK. lia. }
  prop_apply_p
    (sllbseg_start_nonnull
       &(h_val # "blist" ->ₛ "next") i t_l1).
  Intros_p Hhnext.

  sep_apply_l_atomic
    (PtrArray.full_split_to_missing_i
       bucks_ph_2 ind 211 lh_2 0 ltac:(lia)).
  rewrite <- PreH14.
  sep_apply_l_atomic
    (sllbseg_len1
       (bucks_ph_2 + ind * sizeof(PTR)) h_val
       Hcell Hhval Hhnext).
  sep_apply_l_atomic
    (sllbseg_snoc__findref_traversal
       &(h_val # "blist" ->ₛ "next") i i_v_2 t_l1
       Hcurrent PreH21).
  sep_apply_l_atomic
    (ptr_string_name__findref_traversal i_v_2 kp k_cur).
  sep_apply_l_atomic
    (store_map_merge store_name k_cur i_v_2 m_node_2 PreH9).
  sep_apply_l_atomic
    (store_map_merge store_uint
       &(i_v_2 # "blist" ->ₛ "val") vp m2 PreH22).
  prop_apply_p
    (not_key_snoc__find_traversal
       k l1_2 m_node_2 k_cur i_v_2 PreH18 PreH2 PreH9).
  Intros_p Hnot_next.
  rewrite PreH13 in Hnot_next.

  assert (Hb_next :
      b_2 ind = Some
        (Znth ind lh_2 0,
         ((h_val :: t_l1) ++ i_v_2 :: nil) ++ l_tail)).
  { rewrite <- app_assoc.
    change (b_2 ind = Some
      (Znth ind lh_2 0, (h_val :: t_l1) ++ i_v_2 :: l_tail)).
    rewrite <- PreH13, <- PreH8.
    exact PreH10. }
  assert (Hhead_next :
      Znth 0 (((h_val :: t_l1) ++ i_v_2 :: nil) ++ l_tail) 0 =
      Znth ind lh_2 0).
  { rewrite <- app_assoc.
    change (Znth 0 ((h_val :: t_l1) ++ i_v_2 :: l_tail) 0 =
      Znth ind lh_2 0).
    rewrite <- PreH13, <- PreH8.
    exact PreH11. }

  Exists p_next ((h_val :: nil) ++ (t_l1 ++ i_v_2 :: nil)) l_tail
    b_2 lh_2 l_2 bucks_ph_2 top_ph_2 m_node_2.
  split_pure_spatial.
  - simpl sllbseg.
    Intros_p Hcell_sp.
    Intros_p Hhval_sp.
    Intros_p Hhnext_sp.
    Intros_p Heq_sp.
    split_pure_spatial.
    + cancel (store_map store_name m_node_2).
      cancel.
      change
        (sllbseg
           &(h_val # "blist" ->ₛ "next")
           &(i_v_2 # "blist" ->ₛ "next")
           (t_l1 +:: i_v_2)%list
         |--
         sllbseg
           &(h_val # "blist" ->ₛ "next")
           &(i_v_2 # "blist" ->ₛ "next")
           (t_l1 +:: i_v_2)%list).
      cancel (sllbseg
        &(h_val # "blist" ->ₛ "next")
        &(i_v_2 # "blist" ->ₛ "next")
        (t_l1 +:: i_v_2)%list).
    + split_pures; dump_pre_spatial; auto.
  - split_pures; dump_pre_spatial; eauto.
Qed.

Lemma proof_of_hashtbl_find_entail_wit_6_2 : hashtbl_find_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst l1_2.
  subst i.

  assert (Hin_current : In i_v_2 l_2).
  { apply (proj1 (PreH14 i_v_2)).
    exists k_cur. exact PreH9. }
  prop_apply_p
    (dll_member_nonnull__find_return
       top_ph_2 0 l_2 i_v_2 Hin_current).
  Intros_p Hcurrent.

  sep_apply_l_atomic
    (ptr_string_name__findref_traversal i_v_2 kp k_cur).
  sep_apply_l_atomic
    (store_map_merge store_name k_cur i_v_2 m_node_2 PreH9).
  sep_apply_l_atomic
    (store_map_merge store_uint
       &(i_v_2 # "blist" ->ₛ "val") vp m2 PreH21).
  prop_apply_p
    (not_key_snoc__find_traversal
       k nil m_node_2 k_cur i_v_2 PreH17 PreH2 PreH9).
  Intros_p Hnot_next.

  assert (Hb_next :
      b_2 ind = Some
        (Znth ind lh_2 0, (i_v_2 :: nil) ++ l_tail)).
  { change (b_2 ind = Some
      (Znth ind lh_2 0, i_v_2 :: l_tail)).
    rewrite <- PreH8.
    exact PreH10. }
  assert (Hhead_next :
      Znth 0 ((i_v_2 :: nil) ++ l_tail) 0 =
      Znth ind lh_2 0).
  { change (Znth 0 (i_v_2 :: l_tail) 0 = Znth ind lh_2 0).
    rewrite <- PreH8.
    exact PreH11. }

  Exists p_next (i_v_2 :: nil) l_tail b_2 lh_2 l_2
    bucks_ph_2 top_ph_2 m_node_2.
  split_pure_spatial.
  - simpl sllbseg.
    Intros_p Hcell_sp.
    Intros_p Heq_sp.
    split_pure_spatial.
    + cancel (store_map store_name m_node_2).
      cancel.
      change
        ((bucks_ph_2 + ind * sizeof(PTR)) # Ptr |-> i_v_2
         |--
         (bucks_ph_2 + ind * sizeof(PTR)) # Ptr |-> i_v_2).
      cancel ((bucks_ph_2 + ind * sizeof(PTR)) # Ptr |-> i_v_2).
    + split_pures; dump_pre_spatial; auto.
  - split_pures; dump_pre_spatial; eauto.
Qed.

Lemma proof_of_hashtbl_find_return_wit_1 : hashtbl_find_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i_v.
  sep_apply_l_atomic (sll_zero_inv__findref_results l2).
  Intros_p Hl2.
  subst l2.
  rewrite app_nil_r in PreH7, PreH8.
  assert (Hm1_none : m1 k = None).
  { eapply lookup_none_after_bucket_exhaustion__find_return_empty
      with (m_node := m_node) (b := b) (ind := ind)
           (ph := Znth ind lh 0) (bucket := l1); eauto. }
  sep_apply_l_atomic
    (sllbseg_slot_null__findref_results
      (bucks_ph + ind * sizeof(PTR)) i l1).
  Intros head.
  sep_apply_l_atomic (sll_head_matches_Znth__find_return_empty head l1).
  Intros_p Hhead.
  assert (Hhead_lh : head = Znth ind lh 0).
  { transitivity (Znth 0 l1 0); assumption. }
  assert (Hind_lh : 0 <= ind < Zlength lh).
  { apply (proj1 (PreH10 ind (Znth ind lh 0))).
    exists l1. exact PreH7. }
  assert (Hb_head : b ind = Some (head, l1)).
  { rewrite Hhead_lh. exact PreH7. }
  normalize.
  rewrite sizeof_ptr.
  fold ptr_size_Z.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full bucks_ph ind 211 head lh).
  - dump_pre_spatial. lia.
  - rewrite (replace_Znth_id__find_return_found
      lh ind 0 head Hind_lh (eq_sym Hhead_lh)).
    Left.
    split_pure_spatial.
    + unfold store_hash_skeleton.
      Exists m_node l lh top_ph bucks_ph b.
      split_pure_spatial.
      * unfold NBUCK, NULL.
        repeat cancel.
        sep_apply_r_atomic
          (store_map_merge store_sll ind (head, l1) b Hb_head).
        unfold store_sll.
        repeat cancel.
      * split_pures.
        -- dump_pre_spatial. exact PreH6.
        -- dump_pre_spatial. exact PreH9.
        -- dump_pre_spatial. exact PreH10.
        -- dump_pre_spatial. exact PreH11.
        -- dump_pre_spatial. exact PreH13.
    + split_pures.
      * dump_pre_spatial. exact Hm1_none.
      * dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_hashtbl_find_return_wit_2 : hashtbl_find_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k_cur.
  subst l2.
  subst l1.
  assert (Hnode_value : m_node k = Some i_v) by exact PreH9.
  assert (Hvalue_addr : m1 k = Some &(i_v # "blist" ->ₛ "val")).
  { eapply node_value_map_lookup__findref_returns; eauto. }
  prop_apply_p
    (PtrArray.full_Zlength bucks_ph 211
      (replace_Znth ind i_v (replace_Znth ind h_val lh))).
  Intros_p Hlen_nested.
  assert (Hlen_lh : Zlength lh = 211).
  { rewrite !Zlength_replace_Znth in Hlen_nested.
    exact Hlen_nested. }
  assert (Hbounds_lh : 0 <= ind < Zlength lh) by lia.
  assert (Hin_bucket_head :
    In h_val ((h_val :: t_l1) ++ i_v :: l_tail)).
  { simpl. auto. }
  destruct (proj2 (PreH17 ind h_val))
    as [head_key [_ Hmap_head]].
  { exists (Znth ind lh 0),
      ((h_val :: t_l1) ++ i_v :: l_tail).
    split.
    - exact PreH10.
    - exact Hin_bucket_head. }
  assert (Hin_head_global : In h_val l).
  { apply (proj1 (PreH15 h_val)).
    exists head_key.
    exact Hmap_head. }
  assert (Hin_i_v_global : In i_v l).
  { apply (proj1 (PreH15 i_v)).
    exists k.
    exact Hnode_value. }
  prop_apply_p
    (dll_member_nonzero__findref_results
      top_ph 0 l h_val Hin_head_global).
  Intros_p Hhead_nonzero.
  prop_apply_p
    (dll_member_nonzero__findref_results
      top_ph 0 l i_v Hin_i_v_global).
  Intros_p Hi_v_nonzero.
  rewrite Znth_replace_Znth_Same by exact Hbounds_lh.
  rewrite replace_Znth_twice__find_return_found.
  sep_apply_l_atomic
    (sllbseg_slot_sll__findref_results
      (&(h_val # "blist" ->ₛ "next")) i p_next
      t_l1 l_tail).
  Intros suffix_head.
  rename H into Hhead_next.
  sep_apply_l_atomic
    (sll_cons_fold__findref_results
      h_val suffix_head (t_l1 ++ l_tail)
      Hhead_nonzero Hhead_next).
  sep_apply_l_atomic
    (sll_cons_fold__findref_results
      i_v h_val ((h_val :: t_l1) ++ l_tail)
      Hi_v_nonzero PreH21).
  set (new_l := (i_v :: (h_val :: t_l1) ++ l_tail)%list).
  change
    (sll i_v (i_v :: (h_val :: t_l1) ++ l_tail))
    with (sll i_v new_l).
  set (b1 := fun j => if Z.eq_dec j ind
                      then Some (i_v, new_l) else b j).
  assert (Hrepr1 : repr_all_heads (replace_Znth ind i_v lh) b1).
  { unfold b1.
    eapply repr_all_heads_update_bucket__findref_results; eauto. }
  assert (Hperm :
    Permutation ((h_val :: t_l1) ++ i_v :: l_tail) new_l).
  { unfold new_l.
    apply Permutation_sym.
    apply Permutation_middle. }
  assert (Hcontain1 : contain_all_correct_addrs m_node b1).
  { unfold b1.
    eapply contain_all_correct_addrs_update_bucket_perm__findref_results;
      eauto. }
  destruct
    (store_map_missing_i_equiv store_sll b b1 ind)
    as [Hmissing_b _].
  { intros j Hneq.
    unfold b1.
    destruct (Z.eq_dec j ind); congruence. }
  sep_apply_l_atomic Hmissing_b.
  change (sll i_v new_l) with (store_sll ind (i_v, new_l)).
  sep_apply_l_atomic
    (store_map_merge store_sll ind (i_v, new_l) b1
      ltac:(unfold b1; destruct (Z.eq_dec ind ind);
            [reflexivity | contradiction])).
  sep_apply_l_atomic
    (ptr_string_name__findref_traversal i_v kp k).
  sep_apply_l_atomic
    (store_map_merge store_name k i_v m_node Hnode_value).
  sep_apply_l_atomic
    (store_map_merge store_uint
      (&(i_v # "blist" ->ₛ "val")) vp m2 PreH22).
  Right.
  Exists vp (&(i_v # "blist" ->ₛ "val")).
  split_pure_spatial.
  - unfold store_hash_skeleton.
    Exists m_node l (replace_Znth ind i_v lh)
      top_ph bucks_ph b1.
    split_pure_spatial.
    + unfold NBUCK.
      change NULL with 0.
      normalize.
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact PreH7.
      * dump_pre_spatial.
        exact PreH15.
      * dump_pre_spatial.
        exact Hrepr1.
      * dump_pre_spatial.
        exact Hcontain1.
      * dump_pre_spatial.
        exact PreH19.
  - split_pures.
    + dump_pre_spatial.
      exact Hvalue_addr.
    + dump_pre_spatial.
      exact PreH22.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_hashtbl_find_return_wit_3 : hashtbl_find_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k_cur.
  subst l2.
  subst l1.
  simpl in PreH10, PreH11.
  change (i_v = Znth ind lh 0) in PreH11.
  assert (Hnode_value : m_node k = Some i_v) by exact PreH9.
  assert (Hvalue_addr : m1 k = Some &(i_v # "blist" ->ₛ "val")).
  { eapply node_value_map_lookup__findref_returns; eauto. }
  prop_apply_p
    (PtrArray.full_Zlength bucks_ph 211
      (replace_Znth ind i_v (replace_Znth ind p_next lh))).
  Intros_p Hlen_nested.
  assert (Hlen_lh : Zlength lh = 211).
  { rewrite !Zlength_replace_Znth in Hlen_nested.
    exact Hlen_nested. }
  assert (Hbounds_lh : 0 <= ind < Zlength lh) by lia.
  assert (Hin_i_v_global : In i_v l).
  { apply (proj1 (PreH14 i_v)).
    exists k.
    exact Hnode_value. }
  prop_apply_p
    (dll_member_nonzero__findref_results
      top_ph 0 l i_v Hin_i_v_global).
  Intros_p Hi_v_nonzero.
  assert (Harray :
    replace_Znth ind i_v (replace_Znth ind p_next lh) = lh).
  { rewrite replace_Znth_twice__find_return_found.
    eapply (replace_Znth_id__find_return_found lh ind 0 i_v).
    - exact Hbounds_lh.
    - symmetry.
      exact PreH11. }
  rewrite Harray.
  simpl sllbseg.
  Intros_p Hbucket_cell_nonzero.
  Intros_p Hslot_eq.
  sep_apply_l_atomic
    (sll_cons_fold__findref_results
      i_v p_next l_tail Hi_v_nonzero PreH20).
  assert (Hbcurrent : b ind = Some (i_v, i_v :: l_tail)).
  { rewrite PreH10.
    rewrite <- PreH11.
    reflexivity. }
  change (sll i_v (i_v :: l_tail))
    with (store_sll ind (i_v, i_v :: l_tail)).
  sep_apply_l_atomic
    (store_map_merge store_sll ind (i_v, i_v :: l_tail) b Hbcurrent).
  sep_apply_l_atomic
    (ptr_string_name__findref_traversal i_v kp k).
  sep_apply_l_atomic
    (store_map_merge store_name k i_v m_node Hnode_value).
  sep_apply_l_atomic
    (store_map_merge store_uint
      (&(i_v # "blist" ->ₛ "val")) vp m2 PreH21).
  Right.
  Exists vp (&(i_v # "blist" ->ₛ "val")).
  split_pure_spatial.
  - unfold store_hash_skeleton.
    Exists m_node l lh top_ph bucks_ph b.
    split_pure_spatial.
    + unfold NBUCK.
      change NULL with 0.
      normalize.
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact PreH7.
      * dump_pre_spatial.
        exact PreH14.
      * dump_pre_spatial.
        exact PreH15.
      * dump_pre_spatial.
        exact PreH16.
      * dump_pre_spatial.
        exact PreH18.
  - split_pures.
    + dump_pre_spatial.
      exact Hvalue_addr.
    + dump_pre_spatial.
      exact PreH21.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_hashtbl_find_which_implies_wit_1 : hashtbl_find_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_hash_skeleton.
  Intros m_node l lh top_ph bucks_ph b.
  Exists lh b l bucks_ph top_ph m_node.
  split_pure_spatial.
  - cancel (&(h # "hashtbl" ->ₛ "top") # Ptr |-> top_ph).
    cancel (&(h # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks_ph).
    cancel (dll top_ph 0 l).
    cancel (PtrArray.full bucks_ph 211 lh).
    cancel (store_map store_sll b).
    cancel (store_map store_name m_node).
  - split_pures.
    all: dump_pre_spatial; assumption.
Qed.
