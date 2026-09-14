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

Lemma proof_of_hashtbl_findref_entail_wit_1 : hashtbl_findref_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_pos retval 211 PreH1 ltac:(lia)) as Hmod.
  prop_apply_p (PtrArray.full_Zlength h_bucks 211 lh_2).
  Intros_p Hlen.
  sep_apply_l_atomic
    (PtrArray.full_split_to_missing_i
      h_bucks (retval % 211) 211 lh_2 0 ltac:(lia)).
  pose proof
    (PreH6 (retval % 211) (Znth (retval % 211) lh_2 0))
    as Hrepr.
  assert (Hbound : 0 <= retval % 211 < Zlength lh_2) by lia.
  destruct (proj2 Hrepr (conj Hbound eq_refl)) as [bucket Hb].
  assert
    (Hcell : h_bucks + (retval % 211) * sizeof(PTR) <> NULL).
  { apply PreH8.
    unfold NBUCK.
    exact Hmod. }
  sep_apply_l_atomic
    (store_map_split store_sll (retval % 211)
      (Znth (retval % 211) lh_2 0, bucket) b0_2 Hb).
  simpl store_sll.
  Exists top_2 (Znth (retval % 211) lh_2 0)
    (@nil Z) bucket bucket h_bucks lh_2 b0_2 l_2 m_node_2.
  simpl app.
  simpl sllbseg.
  split_pure_spatial.
  - change (sizeof(PTR)) with ptr_size_Z.
    normalize; repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try reflexivity.
    all: try congruence.
    all: try (unfold not_key; intros; contradiction).
    all: lia.
Qed.

Lemma proof_of_hashtbl_findref_entail_wit_5 : hashtbl_findref_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (ptr_string_name__findref_traversal
      i_v_2 i_v_key k_list_current).
  sep_apply_l_atomic
    (store_map_merge store_name k_list_current i_v_2 m_node_2 PreH5).
  prop_apply_p
    (store_name_map_injective_all__findref_traversal m_node_2).
  Intros_p Hinjective.
  sep_apply_l_atomic
    (sllbseg_snoc__findref_traversal
      (h_bucks_2 + ind * sizeof(PTR)) i i_v_2 l_prev_2
      PreH3 PreH7).
  assert
    (Hnot : not_key k (l_prev_2 ++ i_v_2 :: nil) m_node_2).
  { unfold not_key in *.
    intros p k1 Hin Hlookup.
    apply in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    - exact (PreH19 p k1 Hin Hlookup).
    - simpl in Hin.
      destruct Hin as [Hp | Hin]; [| contradiction].
      subst p.
      intro Heq.
      apply PreH2.
      assert (Hkeys : k1 = k_list_current).
      { eapply Hinjective; eauto. }
      congruence. }
  assert
    (Hl0 :
      l0_2 = (l_prev_2 ++ i_v_2 :: nil) ++ l_resres).
  { rewrite PreH18, PreH6.
    rewrite <- app_assoc.
    reflexivity. }
  Exists top_2 i_v_next (l_prev_2 ++ i_v_2 :: nil) l_resres l0_2
    h_bucks_2 lh_2 b0_2 l_2 m_node_2.
  split_pure_spatial.
  - normalize; repeat cancel.
    unfold derivable1.
    auto.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption.
Qed.

Lemma proof_of_hashtbl_findref_return_wit_1 : hashtbl_findref_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i_v.
  sep_apply_l_atomic (sll_zero_inv__findref_results l_res).
  Intros_p Hl_res.
  subst l_res.
  rewrite app_nil_r in PreH11.
  subst l0.
  assert (Hnode_none : m_node k = None).
  { eapply
      (current_bucket_exhausted_not_key__lookup_miss_results
        m_node b0 ind (Znth ind lh 0) l_prev k).
    - exact PreH10.
    - exact PreH6.
    - exact PreH12.
    - unfold NBUCK.
      rewrite <- Z.rem_mod_nonneg by
        (pose proof (hash_string_in_range k); unfold hash_string_k; lia).
      symmetry.
      exact PreH2. }
  assert (Hvalue_none : m k = None).
  { unfold node_value_map in PreH3.
    subst m.
    unfold map_fun.
    rewrite Hnode_none.
    reflexivity. }
  prop_apply_p (PtrArray.missing_i_Zlength h_bucks ind 0 211 lh).
  Intros_p Hlen.
  sep_apply_l_atomic
    (sllbseg_slot_null__findref_results
      (h_bucks + ind * sizeof(PTR)) i l_prev).
  Intros bucket_head.
  change (sizeof(PTR)) with ptr_size_Z.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full
      h_bucks ind 211 bucket_head lh ltac:(lia)).
  set (b1 := fun j => if Z.eq_dec j ind
                      then Some (bucket_head, l_prev) else b0 j).
  assert (Hbounds_lh : 0 <= ind < Zlength lh) by lia.
  assert (Hrepr1 : repr_all_heads (replace_Znth ind bucket_head lh) b1).
  { unfold b1.
    eapply repr_all_heads_update_bucket__findref_results; eauto. }
  assert (Hcontain1 : contain_all_correct_addrs m_node b1).
  { unfold b1.
    eapply contain_all_correct_addrs_update_bucket_perm__findref_results;
      eauto. }
  destruct
    (store_map_missing_i_equiv store_sll b0 b1 ind)
    as [Hmissing _].
  { intros j Hneq.
    unfold b1.
    destruct (Z.eq_dec j ind); congruence. }
  sep_apply_l_atomic Hmissing.
  change (sll bucket_head l_prev) with
    (store_sll ind (bucket_head, l_prev)).
  sep_apply_l_atomic
    (store_map_merge store_sll ind (bucket_head, l_prev) b1
      ltac:(unfold b1; destruct (Z.eq_dec ind ind);
            [reflexivity | contradiction])).
  Left.
  split_pure_spatial.
  - unfold store_hash_skeleton.
    Exists m_node l (replace_Znth ind bucket_head lh)
      top h_bucks b1.
    split_pure_spatial.
    + unfold NBUCK.
      change NULL with 0.
      normalize.
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact PreH3.
      * dump_pre_spatial.
        exact PreH4.
      * dump_pre_spatial.
        exact Hrepr1.
      * dump_pre_spatial.
        exact Hcontain1.
      * dump_pre_spatial.
        exact PreH7.
  - split_pures.
    + dump_pre_spatial.
      exact Hvalue_none.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_hashtbl_findref_return_wit_2 : hashtbl_findref_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k_list_current.
  subst l_prev.
  subst l_res.
  subst l0.
  assert (Hnode_value : m_node k = Some i_v) by exact PreH10.
  assert (Hvalue : m k = Some &(i_v # "blist" ->ₛ "val")).
  { eapply node_value_map_lookup__findref_returns; eauto. }
  prop_apply_p
    (PtrArray.full_Zlength h_bucks 211
      (replace_Znth ind i_v (replace_Znth ind head lh))).
  Intros_p Hlen_nested.
  assert (Hlen_lh : Zlength lh = 211).
  { rewrite !Zlength_replace_Znth in Hlen_nested.
    exact Hlen_nested. }
  assert (Hbounds_lh : 0 <= ind < Zlength lh) by lia.
  assert (Hin_bucket_head :
    In head ((head :: l_prevres) ++ i_v :: l_resres)).
  { simpl. auto. }
  destruct (proj2 (PreH18 ind head))
    as [head_key [_ Hmap_head]].
  { exists (Znth ind lh 0),
      ((head :: l_prevres) ++ i_v :: l_resres).
    split.
    - exact PreH22.
    - exact Hin_bucket_head. }
  assert (Hin_global : In head l).
  { apply (proj1 (PreH16 head)).
    exists head_key.
    exact Hmap_head. }
  prop_apply_p
    (dll_member_nonzero__findref_results top 0 l head Hin_global).
  Intros_p Hhead_nonzero.
  rewrite Znth_replace_Znth_Same by exact Hbounds_lh.
  rewrite replace_Znth_overwrite__clear_transition.
  sep_apply_l_atomic
    (sllbseg_slot_sll__findref_results
      (&(head # "blist" ->ₛ "next")) i i_v_next
      l_prevres l_resres).
  Intros suffix_head.
  rename H into Hhead_next.
  sep_apply_l_atomic
    (sll_cons_fold__findref_results
      head suffix_head (l_prevres ++ l_resres)
      Hhead_nonzero Hhead_next).
  sep_apply_l_atomic
    (sll_cons_fold__findref_results
      i_v head ((head :: l_prevres) ++ l_resres)
      PreH8 PreH2).
  set (new_l := (i_v :: (head :: l_prevres) ++ l_resres)%list).
  change
    (sll i_v (i_v :: (head :: l_prevres) ++ l_resres))
    with (sll i_v new_l).
  set (b1 := fun j => if Z.eq_dec j ind
                      then Some (i_v, new_l) else b0 j).
  assert (Hrepr1 : repr_all_heads (replace_Znth ind i_v lh) b1).
  { unfold b1.
    eapply repr_all_heads_update_bucket__findref_results; eauto. }
  assert (Hperm :
    Permutation ((head :: l_prevres) ++ i_v :: l_resres) new_l).
  { unfold new_l.
    apply Permutation_sym.
    apply Permutation_middle. }
  assert (Hcontain1 : contain_all_correct_addrs m_node b1).
  { unfold b1.
    eapply contain_all_correct_addrs_update_bucket_perm__findref_results;
      eauto. }
  destruct
    (store_map_missing_i_equiv store_sll b0 b1 ind)
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
    (ptr_string_name__findref_traversal i_v i_v_key k).
  sep_apply_l_atomic
    (store_map_merge store_name k i_v m_node Hnode_value).
  Right.
  Exists i_v.
  split_pure_spatial.
  - unfold store_hash_skeleton.
    Exists m_node l (replace_Znth ind i_v lh)
      top h_bucks b1.
    split_pure_spatial.
    + unfold NBUCK.
      change NULL with 0.
      normalize.
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact PreH15.
      * dump_pre_spatial.
        exact PreH16.
      * dump_pre_spatial.
        exact Hrepr1.
      * dump_pre_spatial.
        exact Hcontain1.
      * dump_pre_spatial.
        exact PreH19.
  - split_pures.
    + dump_pre_spatial.
      exact Hvalue.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_hashtbl_findref_return_wit_3 : hashtbl_findref_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst l_prev.
  subst k_list_current.
  subst l_res.
  subst l0.
  assert (Hnode_value : m_node k = Some i_v) by exact PreH11.
  assert (Hvalue : m k = Some &(i_v # "blist" ->ₛ "val")).
  { eapply node_value_map_lookup__findref_returns; eauto. }
  prop_apply_p
    (PtrArray.full_Zlength h_bucks 211
      (replace_Znth ind i_v (replace_Znth ind i_v_next lh))).
  Intros_p Hlen_nested.
  assert (Hlen_lh : Zlength lh = 211).
  { rewrite !Zlength_replace_Znth in Hlen_nested.
    exact Hlen_nested. }
  assert (Hbounds_lh : 0 <= ind < Zlength lh) by lia.
  rewrite Znth_replace_Znth_Same by exact Hbounds_lh.
  rewrite replace_Znth_overwrite__clear_transition.
  sep_apply_l_atomic
    (sll_cons_fold__findref_results
      i_v i_v_next l_resres PreH9 PreH4).
  set (new_l := (i_v :: l_resres)%list).
  change (sll i_v (i_v :: l_resres)) with (sll i_v new_l).
  set (b1 := fun j => if Z.eq_dec j ind
                      then Some (i_v, new_l) else b0 j).
  assert (Hrepr1 : repr_all_heads (replace_Znth ind i_v lh) b1).
  { unfold b1.
    eapply repr_all_heads_update_bucket__findref_results; eauto. }
  assert (Hperm : Permutation (i_v :: l_resres) new_l).
  { unfold new_l. reflexivity. }
  assert (Hcontain1 : contain_all_correct_addrs m_node b1).
  { unfold b1.
    eapply contain_all_correct_addrs_update_bucket_perm__findref_results;
      eauto. }
  destruct
    (store_map_missing_i_equiv store_sll b0 b1 ind)
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
    (ptr_string_name__findref_traversal i_v i_v_key k).
  sep_apply_l_atomic
    (store_map_merge store_name k i_v m_node Hnode_value).
  Right.
  Exists i_v.
  split_pure_spatial.
  - unfold store_hash_skeleton.
    Exists m_node l (replace_Znth ind i_v lh)
      top h_bucks b1.
    split_pure_spatial.
    + unfold NBUCK.
      change NULL with 0.
      normalize.
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact PreH16.
      * dump_pre_spatial.
        exact PreH17.
      * dump_pre_spatial.
        exact Hrepr1.
      * dump_pre_spatial.
        exact Hcontain1.
      * dump_pre_spatial.
        exact PreH20.
  - split_pures.
    + dump_pre_spatial.
      exact Hvalue.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_hashtbl_findref_partial_solve_wit_3_pure : hashtbl_findref_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct l_res as [| p l_resres].
  - simpl sll.
    Intros_p Hnull.
    contradiction.
  - simpl sll.
    Intros i_v_next.
    rename H into Hnonnull.
    rename H0 into Heq.
    rename H1 into Hnext_nonnull.
    subst p.
    destruct (proj2 (PreH6 ind i_v)) as
      [k_list_current [Hhash Hlookup]].
    { exists (Znth ind lh 0), l0.
      split.
      - exact PreH10.
      - subst l0.
        apply in_or_app.
        right.
        simpl.
        auto. }
    Exists k_list_current.
    split_pures.
    + dump_pre_spatial.
      exact PreH1.
    + dump_pre_spatial.
      exact PreH13.
    + dump_pre_spatial.
      exact Hlookup.
Qed.

Lemma proof_of_hashtbl_findref_which_implies_wit_1 : hashtbl_findref_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_hash_skeleton.
  unfold NBUCK.
  unfold NULL.
  Intros m_node l lh top h_bucks b0.
  Exists top h_bucks lh b0 l m_node.
  split_pure_spatial.
  - cancel.
    normalize.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption.
Qed.

Lemma proof_of_hashtbl_findref_which_implies_wit_2 : hashtbl_findref_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct l_res as [| p l_resres].
  - simpl sll.
    Intros_p Hnull.
    contradiction.
  - simpl sll.
    Intros i_v_next.
    rename H into Hnonnull.
    rename H0 into Heq.
    rename H1 into Hnext_nonnull.
    subst p.
    sep_apply_l_atomic
      (store_map_split store_name k_list_current_2 i_v m_node PreH3).
    unfold store_name.
    Intros i_v_key.
    Exists i_v_key i_v_next l_resres k_list_current_2.
    split_pure_spatial.
    + cancel.
      normalize.
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact PreH1.
      * dump_pre_spatial.
        exact PreH2.
      * dump_pre_spatial.
        exact PreH3.
      * dump_pre_spatial.
        reflexivity.
      * dump_pre_spatial.
        exact Hnext_nonnull.
Qed.

Lemma proof_of_hashtbl_findref_which_implies_wit_3 : hashtbl_findref_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct l_prev as [| head l_prevres].
  - Left.
    simpl sllbseg.
    Intros_p Hcell_nonnull.
    Intros_p Hcell_eq.
    subst i.
    subst i_v.
    split_pure_spatial.
    + change (sizeof(PTR)) with ptr_size_Z.
      change Arch32.ptr_size_Z with ptr_size_Z.
      normalize.
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        reflexivity.
      * dump_pre_spatial.
        reflexivity.
      * dump_pre_spatial.
        exact PreH2.
      * dump_pre_spatial.
        exact PreH3.
  - Right.
    simpl sllbseg.
    Intros_p Hcell_nonnull.
    Intros_p Hhead_nonnull.
    Exists head l_prevres.
    split_pure_spatial.
    + change (sizeof(PTR)) with ptr_size_Z.
      change Arch32.ptr_size_Z with ptr_size_Z.
      normalize.
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact PreH1.
      * dump_pre_spatial.
        exact PreH2.
      * dump_pre_spatial.
        exact PreH3.
      * dump_pre_spatial.
        reflexivity.
Qed.
