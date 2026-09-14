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

Lemma proof_of_hashtbl_remove_entail_wit_1 : hashtbl_remove_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (hash_string_in_range k) as Hhash_range.
  assert (Hretval : 0 <= retval) by exact PreH1.
  pose proof
    (Z.rem_bound_pos retval 211 Hretval ltac:(lia)) as Hindex.
  assert (Hcell :
    h_bucks + (retval % 211) * sizeof(PTR) <> NULL).
  { apply PreH8.
    exact Hindex. }
  prop_apply_p (PtrArray.full_Zlength h_bucks 211 lh_2).
  Intros_p Hlength.
  assert (Hindex_lh : 0 <= retval % 211 < Zlength lh_2) by lia.
  destruct
    (proj2
      (PreH6 (retval % 211) (Znth (retval % 211) lh_2 0))
      (conj Hindex_lh eq_refl)) as [l0 Hbucket].
  sep_apply
    (PtrArray.full_split_to_missing_i
      h_bucks (retval % 211) 211 lh_2 0 Hindex).
  sep_apply_l_atomic
    (store_map_split store_sll (retval % 211)
      (Znth (retval % 211) lh_2 0, l0) b Hbucket).
  simpl store_sll.
  prop_apply_p
    (sll_nodup__clear_transition
      (Znth (retval % 211) lh_2 0) l0).
  Intros_p Hnodup.
  destruct l0 as [|bucket_head bucket_tail].
  - simpl sll.
    Intros_p Hbucket_null.
    sep_apply_l_atomic
      (dll_to_null_segment__remove_entails top_2 0 l).
    Intros dl_prev.
    prop_apply_p
      (dllseg_null_loop_invariants__remove_entails top_2 dl_prev l).
    Intros_p Hloop.
    unfold NULL in *.
    Exists dl_prev top_2 0 h_bucks lh_2 l (@nil addr)
      0 (@nil addr) b (@nil addr) (@nil addr) m1_node_2.
    change (sizeof(PTR)) with ptr_size_Z.
    simpl sllbseg.
    simpl sll.
    simpl dll.
    split_pure_spatial.
    + rewrite Hbucket_null.
      cancel
        (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_bucks).
      cancel
        (store_map_missing_i store_sll b (retval % 211)).
      repeat cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try unfold not_key.
      all: simpl.
      all: try rewrite app_nil_r.
      all: try rewrite Hbucket_null in Hbucket.
      all: try assumption; try reflexivity; try lia; try congruence; try tauto.
  - simpl sll.
    Intros bucket_next.
    rename H into Hbucket_nonnull.
    rename H0 into Hbucket_head.
    rename H1 into Hnext_field.
    subst bucket_head.
    destruct
      (proj2
        (PreH7 (retval % 211) (Znth (retval % 211) lh_2 0)))
      as [bucket_key [Hhash Hmap]].
    { exists (Znth (retval % 211) lh_2 0),
        (Znth (retval % 211) lh_2 0 :: bucket_tail).
      split.
      - exact Hbucket.
      - left.
        reflexivity. }
    assert (Hin_global : In (Znth (retval % 211) lh_2 0) l).
    { apply (proj1 (PreH5 (Znth (retval % 211) lh_2 0))).
      exists bucket_key.
      exact Hmap. }
    sep_apply_l_atomic
      (dll_split_at_member__remove_entails
        top_2 0 l (Znth (retval % 211) lh_2 0) Hin_global).
    Intros dl_prev dl_up dl_tail.
    rename H into Hsplit.
    prop_apply_p
      (dllseg_dll_loop_invariants__remove_entails
        top_2 (Znth (retval % 211) lh_2 0)
        dl_prev dl_up
        (Znth (retval % 211) lh_2 0 :: dl_tail)).
    Intros_p Hloop.
    Exists dl_prev top_2 (Znth (retval % 211) lh_2 0)
      h_bucks lh_2 dl_up
      (Znth (retval % 211) lh_2 0 :: dl_tail)
      (Znth (retval % 211) lh_2 0)
      (Znth (retval % 211) lh_2 0 :: bucket_tail)
      b (Znth (retval % 211) lh_2 0 :: bucket_tail)
      (@nil addr) m1_node_2.
    change (sizeof(PTR)) with ptr_size_Z.
    simpl sllbseg.
    simpl sll.
    normalize.
    Exists bucket_next.
    split_pure_spatial.
    + repeat cancel.
      cancel
        (dllseg top_2 (Znth (retval % 211) lh_2 0)
          0 dl_prev dl_up).
      repeat cancel.
    + rewrite Hsplit in PreH5.
      split_pures.
      all: dump_pre_spatial.
      all: try unfold not_key.
      all: simpl.
      all: try assumption; try reflexivity; try lia; try congruence; try tauto.
Qed.

Lemma proof_of_hashtbl_remove_entail_wit_4 : hashtbl_remove_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (ptr_string_name__findref_traversal itv_2 b_key k_list).
  sep_apply_l_atomic
    (store_map_merge store_name k_list itv_2 m1_node_2 PreH11).
  sep_apply_l_atomic
    (store_map_merge store_uint
      (&(itv_2 # "blist" ->ₛ "val")) val m2 PreH12).
  prop_apply_p
    (store_name_map_injective_all__clear_transition m1_node_2).
  Intros_p Hinjective.
  assert (Hnot :
    not_key k (l_prev_2 ++ itv_2 :: nil) m1_node_2).
  { unfold not_key in *.
    intros p k1 Hin Hlookup.
    apply in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    - eapply PreH9; eauto.
    - simpl in Hin.
      destruct Hin as [Hp | []].
      subst p.
      intro Heq.
      subst k1.
      pose proof
        (Hinjective k_list k itv_2 PreH11 Hlookup) as Hkeys.
      congruence. }
  assert (Hnodup_tail : NoDup l_resres).
  { rewrite PreH5 in PreH10.
    inversion PreH10.
    assumption. }
  assert (Hbucket_lists :
    l0_2 = (l_prev_2 ++ itv_2 :: nil) ++ l_resres).
  { rewrite PreH24, PreH5.
    rewrite <- app_assoc.
    reflexivity. }
  rewrite PreH6 in PreH25.
  sep_apply_l_atomic
    (sllbseg_snoc__findref_traversal
      (h_pre_bucks_2 + ind * sizeof(PTR))
      it itv_2 l_prev_2 PreH3 PreH14).
  sep_apply_l_atomic
    (dll_cons_from_fields__remove_entails
      itv_2 dl_prev_2 b_down dl_downres PreH3).
  sep_apply_l_atomic
    (dllseg_dll_merge__remove_entails
      top_2 itv_2 0 dl_prev_2 dl_up_2
      (itv_2 :: dl_downres)).
  destruct l_resres as [|next_head next_tail].
  - simpl sll.
    Intros_p Hnext_null.
    sep_apply_l_atomic
      (dll_to_null_segment__remove_entails
        top_2 0 (dl_up_2 ++ itv_2 :: dl_downres)).
    Intros dl_prev.
    prop_apply_p
      (dllseg_null_loop_invariants__remove_entails
        top_2 dl_prev (dl_up_2 ++ itv_2 :: dl_downres)).
    Intros_p Hloop.
    unfold NULL in *.
    Exists dl_prev top_2 0 h_pre_bucks_2 lh_2
      (dl_up_2 ++ itv_2 :: dl_downres) (@nil addr)
      buck_2 l0_2 bucket_map_2 (@nil addr)
      (l_prev_2 ++ itv_2 :: nil) m1_node_2.
    change (sizeof(PTR)) with ptr_size_Z.
    simpl sll.
    simpl dll.
    split_pure_spatial.
    + rewrite Hnext_null.
      repeat cancel.
      cancel
        (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr
          |-> h_pre_bucks_2).
      repeat cancel.
      unfold derivable1; auto.
    + split_pures.
      all: dump_pre_spatial.
      all: simpl in Hbucket_lists.
      all: try rewrite app_nil_r.
      all: try rewrite Hnext_null.
      all: try assumption; try reflexivity; try lia; try congruence; try tauto.
  - simpl sll.
    Intros next_next.
    rename H into Hnext_nonnull.
    rename H0 into Hnext_head.
    rename H1 into Hnext_field.
    subst next_head.
    assert (Hbucket_next :
      bucket_map_2 ind =
        Some (buck_2,
          (l_prev_2 ++ itv_2 :: nil) ++ b_next :: next_tail)).
    { rewrite Hbucket_lists in PreH23.
      exact PreH23. }
    destruct
      (current_bucket_nonnull_has_key__findref_traversal
        m1_node_2 bucket_map_2 ind buck_2
        (l_prev_2 ++ itv_2 :: nil) b_next next_tail
        PreH27 Hbucket_next) as [next_key Hnext_map].
    assert (Hin_global :
      In b_next (dl_up_2 ++ itv_2 :: dl_downres)).
    { apply (proj1 (PreH25 b_next)).
      exists next_key.
      exact Hnext_map. }
    sep_apply_l_atomic
      (dll_split_at_member__remove_entails
        top_2 0 (dl_up_2 ++ itv_2 :: dl_downres)
        b_next Hin_global).
    Intros dl_prev dl_up dl_tail.
    rename H into Hdll_split.
    prop_apply_p
      (dllseg_dll_loop_invariants__remove_entails
        top_2 b_next dl_prev dl_up (b_next :: dl_tail)).
    Intros_p Hloop.
    Exists dl_prev top_2 b_next h_pre_bucks_2 lh_2
      dl_up (b_next :: dl_tail) buck_2 l0_2 bucket_map_2
      (b_next :: next_tail) (l_prev_2 ++ itv_2 :: nil)
      m1_node_2.
    change (sizeof(PTR)) with ptr_size_Z.
    simpl sll.
    normalize.
    Exists next_next.
    split_pure_spatial.
    + repeat cancel.
      cancel (dllseg top_2 b_next 0 dl_prev dl_up).
      repeat cancel.
      unfold derivable1; auto.
    + rewrite Hdll_split in PreH25.
      split_pures.
      all: dump_pre_spatial.
      all: try assumption; try reflexivity; try lia; try congruence; try tauto.
Qed.

Lemma proof_of_hashtbl_remove_return_wit_1 : hashtbl_remove_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst itv.
  destruct (PreH16 eq_refl) as [Hl_res Hdl_down].
  subst l_res dl_down.
  rewrite app_nil_r in PreH10.
  subst l0.
  assert (Hhash : hash_string_k k mod NBUCK = ind).
  { unfold NBUCK.
    rewrite <- Z.rem_mod_nonneg by
      (unfold hash_string_k;
       pose proof (hash_string_in_range k);
       lia).
    symmetry.
    exact PreH6. }
  assert (Hm1_node_none : m1_node k = None).
  { eapply current_bucket_exhausted_not_key__lookup_miss_results;
      eauto. }
  assert (Hm1_none : m1 k = None).
  { unfold node_value_map in PreH3.
    rewrite PreH3.
    unfold map_fun.
    rewrite Hm1_node_none.
    reflexivity. }
  pose proof
    (remove_map_absent_eq__lookup_miss_results
      m1_node k Hm1_node_none) as Hremove_node.
  pose proof
    (remove_map_absent_eq__lookup_miss_results
      m1 k Hm1_none) as Hremove_value.
  assert (Hind : 0 <= ind < NBUCK).
  { unfold NBUCK.
    lia. }
  assert (Hind_lh : 0 <= ind < Zlength lh).
  { apply (proj1 (PreH12 ind buck)).
    exists l_prev.
    exact PreH9. }
  set (Rbefore :=
    &(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks).
  set (Rmid := store_map_missing_i store_sll bucket_map ind).
  set (Rtail :=
    store_string key_pre k **
    (PtrArray.missing_i h_pre_bucks ind 0 211 lh **
     (store_map store_name m1_node **
      (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top **
       (dllseg top 0 0 dl_prev dl_up **
        (dll 0 dl_prev (@nil addr) **
         (removed_pre # Int |-> 0 ** store_map store_uint m2))))))).
  lazymatch goal with
  | |- _ |-- ?Q =>
      change
        (Rbefore **
         (it # Ptr |-> 0 **
          (Rmid **
           (sllbseg (h_pre_bucks + ind * sizeof(PTR)) it l_prev **
            (sll 0 (@nil addr) ** Rtail)))) |-- Q)
  end.
  rewrite
    (sllbseg_sll_framed__remove_absent
      (h_pre_bucks + ind * sizeof(PTR)) it l_prev 0 (@nil addr)
      Rbefore Rmid Rtail).
  Intros p0.
  unfold Rbefore, Rmid, Rtail.
  set (bucket_map' :=
    fun j => if Z.eq_dec j ind
             then Some (p0, l_prev) else bucket_map j).
  assert (Hb_new : bucket_map' ind = Some (p0, l_prev)).
  { unfold bucket_map'.
    destruct (Z.eq_dec ind ind); [reflexivity | contradiction]. }
  assert (Hb_outside :
    forall j, j <> ind -> bucket_map j = bucket_map' j).
  { intros j Hneq.
    unfold bucket_map'.
    destruct (Z.eq_dec j ind); [contradiction | reflexivity]. }
  assert (Hrepr_new :
    repr_all_heads (replace_Znth ind p0 lh) bucket_map').
  { unfold bucket_map'.
    eapply
      (repr_all_heads_update_bucket__findref_results
        lh bucket_map ind buck l_prev p0 l_prev);
      eauto. }
  assert (Hcontain_new :
    contain_all_correct_addrs m1_node bucket_map').
  { unfold bucket_map'.
    eapply contain_all_correct_addrs_update_head__remove_absent;
      eauto. }
  destruct
    (store_map_missing_i_equiv
      store_sll bucket_map bucket_map' ind Hb_outside)
    as [Hmissing_to_new _].
  rewrite Hremove_value.
  Left.
  split_pure_spatial.
  - unfold store_hash_skeleton.
    Exists m1_node (dl_up ++ nil)%list
      (replace_Znth ind p0 lh) top h_pre_bucks bucket_map'.
    split_pure_spatial.
    + sep_apply_l_atomic
        (dllseg_dll__remove_absent
          top 0 0 dl_prev dl_up (@nil addr)).
      rewrite app_nil_r.
      sep_apply_r_atomic
        (PtrArray.missing_i_merge_to_full
          h_pre_bucks ind NBUCK p0 lh Hind).
      sep_apply_r_atomic
        (store_map_merge
          store_sll ind (p0, l_prev) bucket_map' Hb_new).
      sep_apply_l_atomic Hmissing_to_new.
      unfold store_sll.
      rewrite !app_nil_r.
      unfold NBUCK, NULL.
      change (sizeof(PTR)) with ptr_size_Z.
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact PreH3.
      * dump_pre_spatial.
        exact PreH11.
      * dump_pre_spatial.
        exact Hrepr_new.
      * dump_pre_spatial.
        exact Hcontain_new.
      * dump_pre_spatial.
        exact PreH14.
  - split_pures.
    + dump_pre_spatial.
      exact Hm1_none.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_hashtbl_remove_return_wit_2 : hashtbl_remove_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k_list.
  assert (Hm1 : m1 k = Some (&(itv # "blist" ->ₛ "val"))).
  { unfold node_value_map in PreH14.
    rewrite PreH14.
    unfold map_fun.
    rewrite PreH17.
    reflexivity. }
  assert (Hhash : hash_string k mod NBUCK = ind).
  { assert (Hnonneg : 0 <= hash_string_k k).
    { unfold hash_string_k.
      pose proof (hash_string_in_range k).
      lia. }
    unfold hash_string_k in Hnonneg.
    unfold NBUCK.
    rewrite <- Z.rem_mod_nonneg by lia.
    unfold hash_string_k in PreH26.
    symmetry.
    exact PreH26. }
  assert (Hind : 0 <= ind < 211) by lia.
  assert (Hbucket :
    bucket_map ind =
      Some (buck, (l_prev ++ itv :: l_resres)%list)).
  { rewrite PreH29.
    f_equal.
    rewrite PreH30, PreH11.
    reflexivity. }
  assert (Hcontain :
    contain_all_addrs m1_node (dl_up ++ itv :: dl_downres)).
  { rewrite <- PreH12.
    exact PreH31. }
  assert (Hnodup : NoDup (itv :: l_resres)).
  { rewrite <- PreH11.
    exact PreH16. }
  assert (Hnewlist :
    ((dl_up_prefix +:: dl_prev) ++ b_down :: dl_down_tail)%list =
    (dl_up ++ dl_downres)%list).
  { rewrite PreH1, PreH4, PreH3.
    reflexivity. }
  assert (Hnewlist_actual :
    (dl_up_prefix ++ dl_prev :: b_down :: dl_down_tail)%list =
    (dl_up ++ dl_downres)%list).
  { rewrite <- Hnewlist.
    clear Hnewlist PreH3.
    induction dl_up_prefix as [|a dl_up_prefix IH]; simpl.
    - reflexivity.
    - f_equal.
      exact IH. }
  sep_apply_l_atomic (ptr_string_name__findref_traversal itv b_key k).
  prop_apply_p
    (store_name_missing_injective__remove_success_returns
      m1_node k itv PreH17).
  Intros_p Hinjective.
  sep_apply_l_atomic
    (sllbseg_unlink__remove_success_returns
      (h_pre_bucks + ind * sizeof(PTR)) it l_prev b_next l_resres).
  Intros bucket_head.
  sep_apply_l_atomic
    (dll_cons__remove_success_returns
      b_down dl_prev b_down_down dl_down_tail PreH2).
  sep_apply_l_atomic
    (dll_cons__remove_success_returns
      dl_prev dl_prev_prev b_down (b_down :: dl_down_tail) PreH5).
  sep_apply_l_atomic
    (dllseg_dll__remove_success_returns
      top dl_prev 0 dl_prev_prev dl_up_prefix
      (dl_prev :: b_down :: dl_down_tail)).
  prop_apply_p
    (dll_not_in_from_down_field__remove_success_returns
      itv b_down top NULL
      (dl_up_prefix ++ dl_prev :: b_down :: dl_down_tail)).
  Intros_p Hnotin_actual.
  assert (Hnotin : ~ In itv (dl_up ++ dl_downres)).
  { rewrite <- Hnewlist_actual.
    exact Hnotin_actual. }
  set (b_new :=
    fun j => if Z.eq_dec j ind
             then Some (bucket_head, (l_prev ++ l_resres)%list)
             else bucket_map j).
  assert (Hnode_new :
    node_value_map
      (KP.remove_map m1_node k)
      (KP.remove_map m1 k)).
  { apply node_value_map_remove__remove_success_returns.
    exact PreH14. }
  assert (Hcontain_new_base :
    contain_all_addrs
      (KP.remove_map m1_node k)
      (dl_up ++ dl_downres)).
  { eapply contain_all_addrs_remove__remove_success_returns; eauto. }
  assert (Hcontain_new :
    contain_all_addrs
      (KP.remove_map m1_node k)
      (dl_up_prefix ++ dl_prev :: b_down :: dl_down_tail)).
  { rewrite Hnewlist_actual.
    exact Hcontain_new_base. }
  assert (Hcorrect_new :
    contain_all_correct_addrs (KP.remove_map m1_node k) b_new).
  { unfold b_new.
    eapply contain_all_correct_addrs_remove_bucket__remove_success_returns;
      eauto. }
  assert (Hind_lh : 0 <= ind < Zlength lh).
  { apply (proj1 (PreH32 ind buck)).
    exists ((l_prev ++ itv :: l_resres)%list).
    exact Hbucket. }
  assert (Hrepr_new :
    repr_all_heads (replace_Znth ind bucket_head lh) b_new).
  { unfold b_new.
    eapply repr_all_heads_update_bucket__findref_results; eauto. }
  assert (Hb_new :
    b_new ind = Some (bucket_head, (l_prev ++ l_resres)%list)).
  { unfold b_new.
    destruct (Z.eq_dec ind ind); [reflexivity | contradiction]. }
  assert (Hb_outside :
    forall j, j <> ind -> bucket_map j = b_new j).
  { intros j Hneq.
    unfold b_new.
    destruct (Z.eq_dec j ind); [contradiction | reflexivity]. }
  assert (Hnode_outside :
    forall key, key <> k ->
      m1_node key = KP.remove_map m1_node k key).
  { intros key Hneq.
    symmetry.
    apply KP.remove_map_diff.
    congruence. }
  change (h_pre_bucks + ind * sizeof(PTR))
    with (h_pre_bucks + ind * ptr_size_Z).
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full
      h_pre_bucks ind 211 bucket_head lh Hind).
  change (sll bucket_head (l_prev ++ l_resres))
    with (store_sll ind (bucket_head, (l_prev ++ l_resres)%list)).
  sep_apply
    (store_map_missing_update__remove_success_returns
      store_sll bucket_map b_new ind
      (bucket_head, (l_prev ++ l_resres)%list) Hb_new Hb_outside).
  sep_apply
    (store_map_missing_to_none__remove_success_returns
      store_name m1_node (KP.remove_map m1_node k) k
      (KP.remove_map_same m1_node k) Hnode_outside).
  assert (Huint_outside :
    forall p, p <> &(itv # "blist" ->ₛ "val") ->
      m2 p = PV.remove_map m2 (&(itv # "blist" ->ₛ "val")) p).
  { intros p Hneq.
    symmetry.
    apply PV.remove_map_diff.
    intro Heq.
    apply Hneq.
    symmetry.
    exact Heq. }
  sep_apply_l_atomic
    (store_map_missing_to_none__remove_success_returns
      store_uint m2 (PV.remove_map m2 (&(itv # "blist" ->ₛ "val")))
      (&(itv # "blist" ->ₛ "val"))
      (PV.remove_map_same m2 (&(itv # "blist" ->ₛ "val")))
      Huint_outside).
  unfold store_name.
  Intros key_addr.
  Right.
  Exists b_down dl_prev key_addr val itv.
  unfold store_hash_skeleton.
  Exists (KP.remove_map m1_node k)
    (dl_up_prefix ++ dl_prev :: b_down :: dl_down_tail)
    (replace_Znth ind bucket_head lh)
    top h_pre_bucks b_new.
  split_pure_spatial.
  - unfold NULL, NBUCK.
    cancel (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top).
    cancel
      (dll top 0
        (dl_up_prefix ++ dl_prev :: b_down :: dl_down_tail)).
    cancel (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks).
    apply
      (remove_return_spatial_reorder__remove_success_returns
        removed_pre key_pre itv key_addr val dl_prev b_down h_pre_bucks
        k (PV.remove_map m2 (&(itv # "blist" ->ₛ "val")))
        (KP.remove_map m1_node k) b_new
        (replace_Znth ind bucket_head lh)).
  - split_pures.
    + dump_pre_spatial.
      exact Hm1.
    + dump_pre_spatial.
      exact PreH18.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact Hnode_new.
    + dump_pre_spatial.
      exact Hcontain_new.
    + dump_pre_spatial.
      exact Hrepr_new.
    + dump_pre_spatial.
      exact Hcorrect_new.
    + dump_pre_spatial.
      exact PreH19.
Qed.

Lemma proof_of_hashtbl_remove_return_wit_3 : hashtbl_remove_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Htop : top <> NULL).
  { unfold NULL.
    apply PreH37.
    rewrite PreH2.
    discriminate. }
  rewrite PreH4.
  sep_apply_l_atomic
    (dllseg_end_prev_zero_impossible__remove_success_returns
      z itv top l0_2 Htop).
  Intros_p Hfalse.
  contradiction.
Qed.

Lemma proof_of_hashtbl_remove_return_wit_4 : hashtbl_remove_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k_list.
  assert (Hm1 : m1 k = Some (&(itv # "blist" ->ₛ "val"))).
  { unfold node_value_map in PreH12.
    rewrite PreH12.
    unfold map_fun.
    rewrite PreH15.
    reflexivity. }
  assert (Hhash : hash_string k mod NBUCK = ind).
  { assert (Hnonneg : 0 <= hash_string_k k).
    { unfold hash_string_k.
      pose proof (hash_string_in_range k).
      lia. }
    unfold hash_string_k in Hnonneg.
    unfold NBUCK.
    rewrite <- Z.rem_mod_nonneg by lia.
    unfold hash_string_k in PreH24.
    symmetry.
    exact PreH24. }
  assert (Hind : 0 <= ind < 211) by lia.
  assert (Hbucket :
    bucket_map ind =
      Some (buck, (l_prev ++ itv :: l_resres)%list)).
  { rewrite PreH27.
    f_equal.
    rewrite PreH28, PreH9.
    reflexivity. }
  assert (Hcontain :
    contain_all_addrs m1_node (dl_up ++ itv :: dl_downres)).
  { rewrite <- PreH10.
    exact PreH29. }
  assert (Hnodup : NoDup (itv :: l_resres)).
  { rewrite <- PreH9.
    exact PreH14. }
  pose proof (PreH35 PreH4) as [_ Hup].
  assert (Hnewlist :
    (b_down :: dl_down_tail)%list = (dl_up ++ dl_downres)%list).
  { rewrite Hup, PreH1.
    reflexivity. }
  sep_apply_l_atomic (ptr_string_name__findref_traversal itv b_key k).
  prop_apply_p
    (store_name_missing_injective__remove_success_returns
      m1_node k itv PreH15).
  Intros_p Hinjective.
  sep_apply_l_atomic
    (sllbseg_unlink__remove_success_returns
      (h_pre_bucks + ind * sizeof(PTR)) it l_prev b_next l_resres).
  Intros bucket_head.
  rewrite Hup.
  sep_apply_l_atomic
    (dllseg_nil_elim__remove_success_returns
      top itv 0 dl_prev PreH4 ltac:(lia)).
  sep_apply_l_atomic
    (dll_cons__remove_success_returns
      b_down dl_prev b_down_down dl_down_tail PreH2).
  rewrite PreH3.
  prop_apply_p
    (dll_not_in_from_down_field__remove_success_returns
      itv b_down b_down NULL (b_down :: dl_down_tail)).
  Intros_p Hnotin_actual.
  assert (Hnotin : ~ In itv (dl_up ++ dl_downres)).
  { rewrite <- Hnewlist.
    exact Hnotin_actual. }
  set (b_new :=
    fun j => if Z.eq_dec j ind
             then Some (bucket_head, (l_prev ++ l_resres)%list)
             else bucket_map j).
  assert (Hnode_new :
    node_value_map
      (KP.remove_map m1_node k)
      (KP.remove_map m1 k)).
  { apply node_value_map_remove__remove_success_returns.
    exact PreH12. }
  assert (Hcontain_new_base :
    contain_all_addrs
      (KP.remove_map m1_node k)
      (dl_up ++ dl_downres)).
  { eapply contain_all_addrs_remove__remove_success_returns; eauto. }
  assert (Hcontain_new :
    contain_all_addrs
      (KP.remove_map m1_node k)
      (b_down :: dl_down_tail)).
  { rewrite Hnewlist.
    exact Hcontain_new_base. }
  assert (Hcorrect_new :
    contain_all_correct_addrs (KP.remove_map m1_node k) b_new).
  { unfold b_new.
    eapply contain_all_correct_addrs_remove_bucket__remove_success_returns;
      eauto. }
  assert (Hind_lh : 0 <= ind < Zlength lh).
  { apply (proj1 (PreH30 ind buck)).
    exists ((l_prev ++ itv :: l_resres)%list).
    exact Hbucket. }
  assert (Hrepr_new :
    repr_all_heads (replace_Znth ind bucket_head lh) b_new).
  { unfold b_new.
    eapply repr_all_heads_update_bucket__findref_results; eauto. }
  assert (Hb_new :
    b_new ind = Some (bucket_head, (l_prev ++ l_resres)%list)).
  { unfold b_new.
    destruct (Z.eq_dec ind ind); [reflexivity | contradiction]. }
  assert (Hb_outside :
    forall j, j <> ind -> bucket_map j = b_new j).
  { intros j Hneq.
    unfold b_new.
    destruct (Z.eq_dec j ind); [contradiction | reflexivity]. }
  assert (Hnode_outside :
    forall key, key <> k ->
      m1_node key = KP.remove_map m1_node k key).
  { intros key Hneq.
    symmetry.
    apply KP.remove_map_diff.
    congruence. }
  change (h_pre_bucks + ind * sizeof(PTR))
    with (h_pre_bucks + ind * ptr_size_Z).
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full
      h_pre_bucks ind 211 bucket_head lh Hind).
  change (sll bucket_head (l_prev ++ l_resres))
    with (store_sll ind (bucket_head, (l_prev ++ l_resres)%list)).
  sep_apply
    (store_map_missing_update__remove_success_returns
      store_sll bucket_map b_new ind
      (bucket_head, (l_prev ++ l_resres)%list) Hb_new Hb_outside).
  sep_apply
    (store_map_missing_to_none__remove_success_returns
      store_name m1_node (KP.remove_map m1_node k) k
      (KP.remove_map_same m1_node k) Hnode_outside).
  assert (Huint_outside :
    forall p, p <> &(itv # "blist" ->ₛ "val") ->
      m2 p = PV.remove_map m2 (&(itv # "blist" ->ₛ "val")) p).
  { intros p Hneq.
    symmetry.
    apply PV.remove_map_diff.
    intro Heq.
    apply Hneq.
    symmetry.
    exact Heq. }
  sep_apply_l_atomic
    (store_map_missing_to_none__remove_success_returns
      store_uint m2 (PV.remove_map m2 (&(itv # "blist" ->ₛ "val")))
      (&(itv # "blist" ->ₛ "val"))
      (PV.remove_map_same m2 (&(itv # "blist" ->ₛ "val")))
      Huint_outside).
  unfold store_name.
  Intros key_addr.
  Right.
  Exists b_down 0 key_addr val itv.
  unfold store_hash_skeleton.
  Exists (KP.remove_map m1_node k)
    (b_down :: dl_down_tail)
    (replace_Znth ind bucket_head lh)
    b_down h_pre_bucks b_new.
  split_pure_spatial.
  - unfold NULL, NBUCK.
    cancel (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> b_down).
    cancel (dll b_down 0 (b_down :: dl_down_tail)).
    cancel (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks).
    apply
      (remove_return_spatial_reorder__remove_success_returns
        removed_pre key_pre itv key_addr val 0 b_down h_pre_bucks
        k (PV.remove_map m2 (&(itv # "blist" ->ₛ "val")))
        (KP.remove_map m1_node k) b_new
        (replace_Znth ind bucket_head lh)).
  - split_pures.
    + dump_pre_spatial. exact Hm1.
    + dump_pre_spatial. exact PreH16.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact Hnode_new.
    + dump_pre_spatial. exact Hcontain_new.
    + dump_pre_spatial. exact Hrepr_new.
    + dump_pre_spatial. exact Hcorrect_new.
    + dump_pre_spatial. exact PreH17.
Qed.

Lemma proof_of_hashtbl_remove_return_wit_5 : hashtbl_remove_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k_list.
  assert (Hm1 : m1 k = Some (&(itv # "blist" ->ₛ "val"))).
  { unfold node_value_map in PreH11.
    rewrite PreH11.
    unfold map_fun.
    rewrite PreH14.
    reflexivity. }
  assert (Hhash : hash_string k mod NBUCK = ind).
  { assert (Hnonneg : 0 <= hash_string_k k).
    { unfold hash_string_k.
      pose proof (hash_string_in_range k).
      lia. }
    unfold hash_string_k in Hnonneg.
    unfold NBUCK.
    rewrite <- Z.rem_mod_nonneg by lia.
    unfold hash_string_k in PreH23.
    symmetry.
    exact PreH23. }
  assert (Hind : 0 <= ind < 211) by lia.
  assert (Hbucket :
    bucket_map ind =
      Some (buck, (l_prev ++ itv :: l_resres)%list)).
  { rewrite PreH26.
    f_equal.
    rewrite PreH27, PreH8.
    reflexivity. }
  assert (Hcontain :
    contain_all_addrs m1_node (dl_up ++ itv :: dl_downres)).
  { rewrite <- PreH9.
    exact PreH28. }
  assert (Hnodup : NoDup (itv :: l_resres)).
  { rewrite <- PreH8.
    exact PreH13. }
  pose proof (PreH34 PreH3) as [_ Hup].
  sep_apply_l_atomic (ptr_string_name__findref_traversal itv b_key k).
  prop_apply_p
    (store_name_missing_injective__remove_success_returns
      m1_node k itv PreH14).
  Intros_p Hinjective.
  sep_apply_l_atomic
    (sllbseg_unlink__remove_success_returns
      (h_pre_bucks + ind * sizeof(PTR)) it l_prev b_next l_resres).
  Intros bucket_head.
  rewrite Hup, PreH1, PreH2.
  sep_apply_l_atomic
    (dllseg_nil_elim__remove_success_returns
      top itv 0 0 PreH3 ltac:(reflexivity)).
  sep_apply_l_atomic
    (dll_zero__remove_success_returns itv dl_downres).
  Intros_p Hdlempty.
  sep_apply_l_atomic
    (frame_dll_nil__remove_success_returns
      (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> 0) 0).
  assert (Hnewlist : nil = (dl_up ++ dl_downres)%list).
  { rewrite Hup, Hdlempty.
    reflexivity. }
  assert (Hnotin : ~ In itv (dl_up ++ dl_downres)).
  { rewrite <- Hnewlist.
    simpl.
    tauto. }
  set (b_new :=
    fun j => if Z.eq_dec j ind
             then Some (bucket_head, (l_prev ++ l_resres)%list)
             else bucket_map j).
  assert (Hnode_new :
    node_value_map
      (KP.remove_map m1_node k)
      (KP.remove_map m1 k)).
  { apply node_value_map_remove__remove_success_returns.
    exact PreH11. }
  assert (Hcontain_new_base :
    contain_all_addrs
      (KP.remove_map m1_node k)
      (dl_up ++ dl_downres)).
  { eapply contain_all_addrs_remove__remove_success_returns; eauto. }
  assert (Hcontain_new :
    contain_all_addrs (KP.remove_map m1_node k) nil).
  { rewrite <- Hnewlist in Hcontain_new_base.
    exact Hcontain_new_base. }
  assert (Hcorrect_new :
    contain_all_correct_addrs (KP.remove_map m1_node k) b_new).
  { unfold b_new.
    eapply contain_all_correct_addrs_remove_bucket__remove_success_returns;
      eauto. }
  assert (Hind_lh : 0 <= ind < Zlength lh).
  { apply (proj1 (PreH29 ind buck)).
    exists ((l_prev ++ itv :: l_resres)%list).
    exact Hbucket. }
  assert (Hrepr_new :
    repr_all_heads (replace_Znth ind bucket_head lh) b_new).
  { unfold b_new.
    eapply repr_all_heads_update_bucket__findref_results; eauto. }
  assert (Hb_new :
    b_new ind = Some (bucket_head, (l_prev ++ l_resres)%list)).
  { unfold b_new.
    destruct (Z.eq_dec ind ind); [reflexivity | contradiction]. }
  assert (Hb_outside :
    forall j, j <> ind -> bucket_map j = b_new j).
  { intros j Hneq.
    unfold b_new.
    destruct (Z.eq_dec j ind); [contradiction | reflexivity]. }
  assert (Hnode_outside :
    forall key, key <> k ->
      m1_node key = KP.remove_map m1_node k key).
  { intros key Hneq.
    symmetry.
    apply KP.remove_map_diff.
    congruence. }
  change (h_pre_bucks + ind * sizeof(PTR))
    with (h_pre_bucks + ind * ptr_size_Z).
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full
      h_pre_bucks ind 211 bucket_head lh Hind).
  change (sll bucket_head (l_prev ++ l_resres))
    with (store_sll ind (bucket_head, (l_prev ++ l_resres)%list)).
  sep_apply
    (store_map_missing_update__remove_success_returns
      store_sll bucket_map b_new ind
      (bucket_head, (l_prev ++ l_resres)%list) Hb_new Hb_outside).
  sep_apply
    (store_map_missing_to_none__remove_success_returns
      store_name m1_node (KP.remove_map m1_node k) k
      (KP.remove_map_same m1_node k) Hnode_outside).
  assert (Huint_outside :
    forall p, p <> &(itv # "blist" ->ₛ "val") ->
      m2 p = PV.remove_map m2 (&(itv # "blist" ->ₛ "val")) p).
  { intros p Hneq.
    symmetry.
    apply PV.remove_map_diff.
    intro Heq.
    apply Hneq.
    symmetry.
    exact Heq. }
  sep_apply_l_atomic
    (store_map_missing_to_none__remove_success_returns
      store_uint m2 (PV.remove_map m2 (&(itv # "blist" ->ₛ "val")))
      (&(itv # "blist" ->ₛ "val"))
      (PV.remove_map_same m2 (&(itv # "blist" ->ₛ "val")))
      Huint_outside).
  unfold store_name.
  Intros key_addr.
  Right.
  Exists 0 0 key_addr val itv.
  unfold store_hash_skeleton.
  Exists (KP.remove_map m1_node k) nil
    (replace_Znth ind bucket_head lh)
    0 h_pre_bucks b_new.
  split_pure_spatial.
  - unfold NULL, NBUCK.
    cancel (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> 0).
    cancel (dll 0 0 nil).
    cancel (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks).
    apply
      (remove_return_terminal_spatial_reorder__remove_success_returns
        removed_pre key_pre itv key_addr val 0 0 h_pre_bucks
        k (PV.remove_map m2 (&(itv # "blist" ->ₛ "val")))
        (KP.remove_map m1_node k) b_new
        (replace_Znth ind bucket_head lh)).
  - split_pures.
    + dump_pre_spatial. exact Hm1.
    + dump_pre_spatial. exact PreH15.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact Hnode_new.
    + dump_pre_spatial. exact Hcontain_new.
    + dump_pre_spatial. exact Hrepr_new.
    + dump_pre_spatial. exact Hcorrect_new.
    + dump_pre_spatial. exact PreH16.
Qed.

Lemma proof_of_hashtbl_remove_return_wit_6 : hashtbl_remove_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Htop : top <> NULL).
  { unfold NULL.
    apply PreH36.
    rewrite PreH1.
    discriminate. }
  rewrite PreH3.
  sep_apply_l_atomic
    (dllseg_end_prev_zero_impossible__remove_success_returns
      z itv top l0_2 Htop).
  Intros_p Hfalse.
  contradiction.
Qed.

Lemma proof_of_hashtbl_remove_return_wit_7 : hashtbl_remove_return_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k_list.
  assert (Hm1 : m1 k = Some (&(itv # "blist" ->ₛ "val"))).
  { unfold node_value_map in PreH13.
    rewrite PreH13.
    unfold map_fun.
    rewrite PreH16.
    reflexivity. }
  assert (Hhash : hash_string k mod NBUCK = ind).
  { assert (Hnonneg : 0 <= hash_string_k k).
    { unfold hash_string_k.
      pose proof (hash_string_in_range k).
      lia. }
    unfold hash_string_k in Hnonneg.
    unfold NBUCK.
    rewrite <- Z.rem_mod_nonneg by lia.
    unfold hash_string_k in PreH25.
    symmetry.
    exact PreH25. }
  assert (Hind : 0 <= ind < NBUCK).
  { unfold NBUCK; lia. }
  assert (Hbucket :
    bucket_map ind = Some (buck, l_prev ++ itv :: l_resres)).
  { rewrite PreH28.
    f_equal.
    rewrite PreH29, PreH10.
    reflexivity. }
  assert (Hcontain :
    contain_all_addrs m1_node (dl_up ++ itv :: dl_downres)).
  { rewrite <- PreH11.
    exact PreH30. }
  assert (Hnodup : NoDup (itv :: l_resres)).
  { rewrite <- PreH10.
    exact PreH15. }
  sep_apply_l_atomic
    (ptr_string_name__findref_traversal itv b_key k).
  prop_apply_p
    (store_name_missing_injective__remove_success_returns
      m1_node k itv PreH16).
  Intros_p Hinjective.
  sep_apply_l_atomic
    (rebuild_removed_node_spatial__remove_success_returns
      h_pre_bucks ind lh bucket_map it l_prev b_next l_resres Hind).
  Intros bucket_head.
  set (b_new :=
    fun j => if Z.eq_dec j ind
             then Some (bucket_head, l_prev ++ l_resres)
             else bucket_map j).
  fold b_new.
  rewrite PreH1.
  sep_apply_l_atomic
    (dll_zero_nil__remove_success_returns itv dl_downres).
  Intros_p Hdlempty.
  set (P :=
    store_string key_pre k **
    (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks **
     (&(itv # "blist" ->ₛ "val") # UInt |-> val **
      (store_map_missing_i store_uint m2
         (&(itv # "blist" ->ₛ "val")) **
       (&(itv # "blist" ->ₛ "down") # Ptr |-> 0 **
        (&(itv # "blist" ->ₛ "up") # Ptr |-> dl_prev **
         (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top **
          removed_pre # Int |-> 1)))))) : Assertion).
  fold b_new.
  fold P.
  etransitivity.
  - apply
      (dllseg_singleton_four_frames__remove_success_returns
      (PtrArray.full h_pre_bucks 211
        (replace_Znth ind bucket_head lh))
      (store_map store_sll
        (fun j => if Z.eq_dec j ind
                  then Some (bucket_head, l_prev ++ l_resres)
                  else bucket_map j))
      (store_map_missing_i store_name m1_node k)
      (store_name k itv)
      P top dl_prev 0 dl_prev_prev dl_up_prefix PreH4).
  - unfold P.
  assert (Hnewlist :
    dl_up_prefix ++ dl_prev :: nil = dl_up ++ dl_downres).
  { rewrite Hdlempty, PreH3, PreH2.
    rewrite app_nil_r.
    reflexivity. }
  set (P2 :=
    &(itv # "blist" ->ₛ "up") # Ptr |-> dl_prev **
    (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top **
     removed_pre # Int |-> 1) : Assertion).
  fold P2.
  etransitivity.
  { apply
      (expose_removed_down_with_dll__remove_success_returns
        (PtrArray.full h_pre_bucks 211
          (replace_Znth ind bucket_head lh))
        (store_map store_sll
          (fun j => if Z.eq_dec j ind
                    then Some (bucket_head, l_prev ++ l_resres)
                    else bucket_map j))
        (store_map_missing_i store_name m1_node k)
        (store_name k itv)
        (store_string key_pre k)
        (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks)
        (&(itv # "blist" ->ₛ "val") # UInt |-> val)
        (store_map_missing_i store_uint m2
          (&(itv # "blist" ->ₛ "val")))
        P2 (dl_up_prefix ++ dl_prev :: nil) itv 0 top 0). }
  Intros_p Hnotin_actual.
  assert (Hnotin : ~ In itv (dl_up ++ dl_downres)).
  { rewrite <- Hnewlist.
    exact Hnotin_actual. }
  pose proof
    (remove_node_model_invariants__remove_success_returns
      m1_node m1 bucket_map k itv dl_up dl_downres lh ind buck
      l_prev l_resres bucket_head Hinjective PreH13 Hcontain PreH31
      PreH32 PreH16 (eq_sym Hhash) Hbucket PreH14 Hnodup Hnotin)
    as Hmodels.
  destruct Hmodels as [Hnode_new [Hcontain_new [Hrepr_new Hcorrect_new]]].
  fold b_new in Hrepr_new, Hcorrect_new.
  assert (Hcontain_actual :
    contain_all_addrs
      (KP.remove_map m1_node k) (dl_up_prefix ++ dl_prev :: nil)).
  { rewrite Hnewlist.
    exact Hcontain_new. }
  assert (Hnode_outside : forall key, key <> k ->
    m1_node key = KP.remove_map m1_node k key).
  { intros key Hneq.
    symmetry.
    apply KP.remove_map_diff.
    congruence. }
  sep_apply_l_atomic
    (store_map_missing_to_none__remove_success_returns
      store_name m1_node (KP.remove_map m1_node k) k
      (KP.remove_map_same m1_node k) Hnode_outside).
  assert (Huint_outside :
    forall p, p <> &(itv # "blist" ->ₛ "val") ->
      m2 p = PV.remove_map m2 (&(itv # "blist" ->ₛ "val")) p).
  { intros p Hneq.
    symmetry.
    apply PV.remove_map_diff.
    congruence. }
  sep_apply_l_atomic
    (store_map_missing_to_none__remove_success_returns
      store_uint m2 (PV.remove_map m2 (&(itv # "blist" ->ₛ "val")))
      (&(itv # "blist" ->ₛ "val"))
      (PV.remove_map_same m2 (&(itv # "blist" ->ₛ "val")))
      Huint_outside).
  unfold store_name.
  Intros key_addr.
  Right.
  Exists 0 dl_prev key_addr val itv.
  unfold store_hash_skeleton.
  Exists (KP.remove_map m1_node k)
    (dl_up_prefix ++ dl_prev :: nil)
    (replace_Znth ind bucket_head lh)
    top h_pre_bucks b_new.
  split_pure_spatial.
  + unfold NULL, NBUCK.
    repeat cancel.
    unfold P2, b_new, store_name.
    cancel (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top).
    cancel (dll top 0 (dl_up_prefix ++ dl_prev :: nil)).
    cancel (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks).
    cancel (PtrArray.full h_pre_bucks 211
      (replace_Znth ind bucket_head lh)).
    cancel (store_map store_sll
      (fun j => if Z.eq_dec j ind
                then Some (bucket_head, l_prev ++ l_resres)
                else bucket_map j)).
    cancel (store_map
      (fun k0 p => EX key_addr0,
        &(p # "blist" ->ₛ "key") # Ptr |-> key_addr0 **
        store_string key_addr0 k0)
      (KP.remove_map m1_node k)).
    cancel (store_string key_pre k).
    cancel (removed_pre # Int |-> 1).
    cancel (store_map store_uint
      (PV.remove_map m2 (&(itv # "blist" ->ₛ "val")))).
    cancel (&(itv # "blist" ->ₛ "key") # Ptr |-> key_addr).
    cancel (store_string key_addr k).
    cancel (&(itv # "blist" ->ₛ "up") # Ptr |-> dl_prev).
    unfold derivable1.
    auto.
  + split_pures.
    * dump_pre_spatial. exact Hm1.
    * dump_pre_spatial. exact PreH17.
    * dump_pre_spatial. reflexivity.
    * dump_pre_spatial. exact Hnode_new.
    * dump_pre_spatial. exact Hcontain_actual.
    * dump_pre_spatial. exact Hrepr_new.
    * dump_pre_spatial. exact Hcorrect_new.
    * dump_pre_spatial. exact PreH18.
Qed.

Lemma proof_of_hashtbl_remove_partial_solve_wit_3_pure_split_goal_1 : hashtbl_remove_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply derivable1s_coq_prop_r.
  unfold current_bucket_suffix.
  split.
  - exact PreH15.
  - exists buck.
    rewrite PreH12 in PreH11.
    exact PreH11.
Qed.

Lemma proof_of_hashtbl_remove_partial_solve_wit_3_pure : hashtbl_remove_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply
    (proof_of_hashtbl_remove_partial_solve_wit_3_pure_split_goal_1_adapter__remove_search
      removed_pre key_pre h_pre k m2 dl_prev top itv it h_pre_bucks
      lh dl_up dl_down buck l0 bucket_map ind l_res l_prev m1_node
      PreH15 PreH11 PreH12).
Qed.

Lemma proof_of_hashtbl_remove_partial_solve_wit_5_pure_split_goal_1 : hashtbl_remove_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply derivable1s_coq_prop_r.
  apply PreH39.
  rewrite PreH5.
  discriminate.
Qed.

Lemma proof_of_hashtbl_remove_partial_solve_wit_5_pure : hashtbl_remove_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_hashtbl_remove_partial_solve_wit_5_pure_split_goal_1.
Qed.

Lemma proof_of_hashtbl_remove_which_implies_wit_1 : hashtbl_remove_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_hash_skeleton.
  Intros m1_node l lh top h_bucks b.
  Exists top h_bucks lh b l m1_node.
  unfold NULL, NBUCK.
  split_pure_spatial.
  - normalize; repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption.
Qed.

Lemma proof_of_hashtbl_remove_which_implies_wit_2 : hashtbl_remove_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold current_bucket_suffix in PreH7.
  destruct PreH7 as [Hcontain [buck Hbucket]].
  destruct l_res as [|r l_resres].
  - simpl sll.
    Intros_p Hzero.
    contradiction.
  - simpl sll.
    Intros b_next.
    subst r.
    destruct dl_down as [|d dl_downres].
    + simpl dll.
      Intros_p Hzero.
      contradiction.
    + simpl dll.
      Intros b_down.
      subst d.
      destruct
        (current_bucket_nonnull_has_key__findref_traversal
          m1_node bucket_map ind buck l_prev b l_resres Hcontain Hbucket)
        as [k_list Hname].
      assert (Hvalue_addr :
        m1 k_list = Some &(b # "blist" ->ₛ "val")).
      { unfold node_value_map in PreH4.
        rewrite PreH4.
        unfold map_fun.
        rewrite Hname.
        reflexivity. }
      destruct (proj1 PreH3 k_list) as
        [Hnone | [value_addr [val [Hvalue_addr' Hvalue]]]].
      * rewrite Hvalue_addr in Hnone.
        discriminate.
      * rewrite Hvalue_addr in Hvalue_addr'.
        inversion Hvalue_addr'.
        subst value_addr.
        sep_apply_l_atomic
          (store_map_split store_name k_list b m1_node Hname).
        unfold store_name.
        Intros b_key.
        sep_apply_l_atomic
          (store_map_split store_uint &(b # "blist" ->ₛ "val") val m2 Hvalue).
        Exists b_down b_key b_next val k_list dl_downres l_resres.
        split_pure_spatial.
        -- normalize; repeat cancel.
        -- split_pures.
           all: dump_pre_spatial.
           all: auto.
Qed.

Lemma proof_of_hashtbl_remove_which_implies_wit_3 : hashtbl_remove_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst dl_up.
  sep_apply_l_atomic
    (dllseg_split_last__remove_setup_extraction
      top top_next b 0 dl_prev dl_up_tail ltac:(assumption)).
  Intros dl_prev_prev dl_up_prefix.
  Exists dl_prev_prev dl_up_prefix.
  split_pure_spatial.
  - normalize; repeat cancel.
  - dump_pre_spatial.
    assumption.
Qed.

Lemma proof_of_hashtbl_remove_which_implies_wit_4 : hashtbl_remove_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct dl_downres as [|head tail].
  - simpl dll.
    Intros_p Hnull.
    unfold derivable1.
    intros.
    exfalso.
    unfold NULL in Hnull.
    congruence.
  - simpl dll.
    Intros b_down_down.
    Exists b_down_down tail.
    subst head.
    split_pure_spatial.
    + normalize; repeat cancel.
    + dump_pre_spatial.
      reflexivity.
Qed.
