From SimpleC.Verification Require Import VCPrelude.
Require Import ListLib.General.Length.
From SimpleC.EE.Applications_human.hash_table Require Import
  hash_table_def hash_table_goal hash_table_proof_auto hash_table_lib.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_entails_emp_unfold_return_wit_1_split_goal_spatial : entails_emp_unfold_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_entails_emp_unfold_return_wit_1 : entails_emp_unfold_return_wit_1.
Proof.
  LLM_pre_process auto.
Qed.

Lemma proof_of_ht_specs_get_hash_spec_return_wit_1 : ht_specs_get_hash_spec_return_wit_1.
Proof. 
  LLM_pre_process auto.
  entailer!.
  unfold ht_specs, ht_hash_spec.
  rewrite !derivable1_andp_elim1.
  apply func_ptr_spec_mono. clear.
  intros.
  Intros_r k. Exists_l k.
  apply HoareFun_conseq.
  - entailer!.
  - simpl. intros. entailer!.
Qed.

Lemma proof_of_ht_specs_get_equal_spec_return_wit_1 : ht_specs_get_equal_spec_return_wit_1.
Proof.
  LLM_pre_process auto.
  entailer!.
  unfold ht_specs, ht_equal_spec.
  do 2 rewrite derivable1_andp_elim1.
  rewrite derivable1_andp_elim2.
  apply func_ptr_spec_mono. clear.
  intros.
  Intros_r a b. Exists_l a b.
  apply HoareFun_conseq.
  - entailer!.
  - simpl. intros (x, y) r. unfold derivable1, andp, orp. tauto.
Qed.

Lemma proof_of_ht_specs_get_key_free_spec_return_wit_1 : ht_specs_get_key_free_spec_return_wit_1.
Proof.
  LLM_pre_process auto.
  unfold ht_specs, ht_free_spec.
  LLM_pre_process auto.
  rewrite (derivable1_andp_elim2 (ht_hash_spec _ _ _)).
  rewrite (derivable1_andp_elim2 (ht_equal_spec _ _ _)).
  rewrite (derivable1_andp_elim1 (_ || _)).
  simpl.
  rewrite logic_equiv_andp_orp_distr_r.
  Split.
  - Left. entailer!.
  - Right. rewrite func_ptr_spec_nonzero'. entailer!.
    apply func_ptr_spec_mono. clear.
    intros. Intros_r k. Exists_l k.
    apply HoareFun_conseq; simpl; intros; entailer!.
Qed.

Lemma proof_of_ht_specs_get_value_free_spec_return_wit_1 : ht_specs_get_value_free_spec_return_wit_1.
Proof.
  LLM_pre_process auto.
  unfold ht_specs, ht_free_spec.
  LLM_pre_process auto.
  rewrite (derivable1_andp_elim2 (ht_hash_spec _ _ _)).
  rewrite (derivable1_andp_elim2 (ht_equal_spec _ _ _)).
  rewrite (derivable1_andp_elim2 (_ || _)).
  simpl.
  rewrite logic_equiv_andp_orp_distr_r.
  Split.
  - Left. entailer!.
  - Right. rewrite func_ptr_spec_nonzero'. entailer!.
    apply func_ptr_spec_mono. clear.
    intros. Intros_r k. Exists_l k.
    apply HoareFun_conseq; simpl; intros; entailer!.
Qed.

Lemma proof_of_ht_store_map_unfold_return_wit_1 : ht_store_map_unfold_return_wit_1.
Proof.
  LLM_pre_process auto.
  unfold ht_store_map, ht_store.
  LLM_pre_process auto.
  Intros hash equal key_free value_free cap bucks buckets ptrs.
  Exists bucks hash equal key_free value_free buckets ptrs cap.
  entailer!.
Qed.

Lemma proof_of_ht_bucket_chains_split_Znth_return_wit_1_split_goal_spatial : ht_bucket_chains_split_Znth_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_ht_bucket_chains_split_Znth_return_wit_1 : ht_bucket_chains_split_Znth_return_wit_1.
Proof.
  LLM_pre_process auto.
  sep_apply (ht_bucket_chains_split_Znth storeK storeV); eauto.
  entailer!.
Qed.

Lemma proof_of_ht_chain_nonnull_unfold_return_wit_1 : ht_chain_nonnull_unfold_return_wit_1.
Proof.
  LLM_pre_process auto.
  sep_apply (ht_chain_nonnull_unfold storeK storeV); eauto.
  Intros cur_key cur_val cur_next.
  Intros cur_k cur_v rest_tail.
  Exists cur_next cur_val cur_key cur_k cur_v rest_tail.
  entailer!.
Qed.

Lemma proof_of_ht_int_hash_return_wit_1 : ht_int_hash_return_wit_1.
Proof.
  LLM_pre_process auto.
  entailer!.
  rewrite (unsigned_last_nbits_eq
             (Z.shiftr (unsigned_last_nbits key_pre 64) 32) 32);
    [reflexivity |].
  pose proof (unsigned_Lastnbits_range key_pre 64 ltac:(lia)) as Hrange.
  unfold Z.shiftr.
  rewrite Z.shiftl_div_pow2; try lia.
  replace (- - (32)) with 32 by lia.
  split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma proof_of_ht_init_return_wit_1_split_goal_spatial : ht_init_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_ht_init_return_wit_1 : ht_init_return_wit_1.
Proof.
  LLM_pre_process auto.
  unfold ht_store_map.
  Exists hash_pre equal_pre key_free_pre value_free_pre.
  Exists capacity_pre retval.
  Exists (repeat_Z (@nil (K * V)) capacity_pre).
  unfold ht_store.
  Exists (zeros capacity_pre).
  assert (Zlength (repeat_Z (@nil (K * V)) capacity_pre) = capacity_pre) as Hlen.
  { unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia. }
  assert (Zlength (zeros capacity_pre) = capacity_pre) as Hlen2.
  { unfold zeros. rewrite Zlength_correct, repeat_length. lia. }
  unfold ht_specs.
  entailer!.
  - rewrite (ht_bucket_chains_zeros_repeat_nil storeK storeV capacity_pre).
    entailer!.
  - unfold buckets_abs, repeat_Z.
    induction (Z.to_nat capacity_pre); simpl.
    + unfold map_empty, empty_mapping. reflexivity.
    + exact IHn.
  - unfold buckets_hash, repeat_Z.
    intros idx k v Hidx Hin.
    rewrite Znth_repeat in Hin.
    contradiction.
  - unfold buckets_unique, repeat_Z.
    induction (Z.to_nat capacity_pre); simpl; auto.
Qed.

Lemma proof_of_ht_add_entail_wit_1_split_goal_1 : ht_add_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_ht_add_entail_wit_1_split_goal_2 : ht_add_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_ht_add_entail_wit_1 : ht_add_entail_wit_1.
Proof.
  LLM_pre_process auto.
  subst.
  pose proof (Z.rem_bound_pos (key_hash k) (Zlength ptrs)).
  entailer!.
Qed.

Lemma proof_of_ht_add_entail_wit_2_split_goal_1 : ht_add_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_ht_add_entail_wit_2 : ht_add_entail_wit_2.
Proof.
  LLM_pre_process auto.
  subst.
  Exists nil.
  Exists (Znth (key_hash k % (Zlength ptrs)) buckets __default__List__Prod_K_V).
  entailer!.
Qed.

Lemma proof_of_ht_add_entail_wit_5 : ht_add_entail_wit_5.
Proof.
  LLM_pre_process auto.
  rewrite derivable1_andp_elim2.
  subst.
  Exists (l1_2 ++ [(cur_k, cur_v)]).
  Exists rest_tail.
  entailer!.
  - sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth ((key_hash k) % (Zlength ptrs)) ptrs 0)
      node cur_next cur_key cur_val cur_k cur_v l1_2);
      entailer!.
  - intros pk pv Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (PreH8 pk pv Hin).
    + simpl in Hin. destruct Hin as [Heq | []].
      injection Heq; intros; subst; exact PreH1.
  - rewrite <- PreH6.
    rewrite <- (app_assoc l1_2 ((cur_k, cur_v) :: nil) rest_tail). reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_1 : ht_add_return_wit_1.
Proof.
  LLM_pre_process auto.
  do 3 rewrite derivable1_andp_elim2.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  Exists new_m.
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks
    (replace_Znth index (l1 ++ (k, v) :: rest_tail) buckets).
  Exists (replace_Znth index (Znth index ptrs 0) ptrs).
  entailer!.
  - rewrite <- PreH13.
    sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth index ptrs 0) node cur_next key_pre val_pre k v l1);
      entailer!.
    unfold ht_chain.
    sep_apply (ht_chain_seg_app storeK storeV
      (Znth index ptrs 0) cur_next 0 (l1 +:: (k, v)) rest_tail);
      entailer!.
    rewrite <- app_assoc. simpl.
    fold (ht_chain storeK storeV
      (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail)).
    sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
      index ptrs buckets (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail));
      entailer!.
    rewrite replace_Znth_Znth.
    entailer!. clear -PreH8.
    unfold entails_emp in PreH8.
    sep_apply (PreH8 cur_key cur_k). entailer!.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Z.rem_mod_nonneg in PreH13 by lia.
    eapply buckets_abs_replace_first_in_bucket
      with (old_v := cur_v); eauto.
    rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
      by (rewrite PreH24, PreH13; apply Z.mod_pos_bound; lia).
    rewrite <- PreH14, PreH11. reflexivity.
  - rewrite Z.rem_mod_nonneg in PreH13 by lia.
    eapply buckets_hash_replace_entry
      with (old_entry := (cur_k, cur_v)); eauto.
    + rewrite PreH13. apply Z.mod_pos_bound. lia.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH24, PreH13; apply Z.mod_pos_bound; lia).
      rewrite <- PreH14, PreH11. reflexivity.
  - eapply buckets_unique_replace_entry
      with (old_k := cur_k) (old_v := cur_v); eauto.
    + rewrite PreH24, PreH13; split; assumption.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH24, PreH13; split; assumption).
      rewrite <- PreH14, PreH11. reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_2 : ht_add_return_wit_2.
Proof.
  LLM_pre_process auto.
  subst cur_key.
  unfold store_exclusive in PreH7.
  do 5 rewrite derivable1_andp_elim2.
  sep_apply (PreH7 key_pre cur_k k).
  entailer!.
Qed.

Lemma proof_of_ht_add_return_wit_3 : ht_add_return_wit_3.
Proof.
  LLM_pre_process auto.
  do 3 rewrite derivable1_andp_elim2.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  Exists new_m.
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks
    (replace_Znth index (l1 ++ (k, v) :: rest_tail) buckets).
  Exists (replace_Znth index (Znth index ptrs 0) ptrs).
  entailer!.
  - rewrite <- PreH12.
    sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth index ptrs 0) node cur_next key_pre val_pre k v l1);
      entailer!.
    unfold ht_chain.
    sep_apply (ht_chain_seg_app storeK storeV
      (Znth index ptrs 0) cur_next 0 (l1 +:: (k, v)) rest_tail);
      entailer!.
    rewrite <- app_assoc. simpl.
    fold (ht_chain storeK storeV
      (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail)).
    sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
      index ptrs buckets (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail));
      entailer!.
    rewrite replace_Znth_Znth.
    entailer!. clear -PreH7.
    unfold entails_emp in PreH7.
    sep_apply (PreH7 cur_key cur_k). entailer!.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Z.rem_mod_nonneg in PreH12 by lia.
    eapply buckets_abs_replace_first_in_bucket
      with (old_v := cur_v); eauto.
    rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
      by (rewrite PreH23, PreH12; apply Z.mod_pos_bound; lia).
    rewrite <- PreH13, PreH10. reflexivity.
  - rewrite Z.rem_mod_nonneg in PreH12 by lia.
    eapply buckets_hash_replace_entry
      with (old_entry := (cur_k, cur_v)); eauto.
    + rewrite PreH12. apply Z.mod_pos_bound. lia.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH23, PreH12; apply Z.mod_pos_bound; lia).
      rewrite <- PreH13, PreH10. reflexivity.
  - eapply buckets_unique_replace_entry
      with (old_k := cur_k) (old_v := cur_v); eauto.
    + rewrite PreH23, PreH12; split; assumption.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH23, PreH12; split; assumption).
      rewrite <- PreH13, PreH10. reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_4 : ht_add_return_wit_4.
Proof.
  LLM_pre_process auto.
  do 4 rewrite derivable1_andp_elim2.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  Exists new_m.
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks
    (replace_Znth index (l1 ++ (k, v) :: rest_tail) buckets).
  Exists (replace_Znth index (Znth index ptrs 0) ptrs).
  entailer!.
  - rewrite <- PreH13.
    sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth index ptrs 0) node cur_next key_pre val_pre k v l1);
      entailer!.
    unfold ht_chain.
    sep_apply (ht_chain_seg_app storeK storeV
      (Znth index ptrs 0) cur_next 0 (l1 +:: (k, v)) rest_tail);
      entailer!.
    rewrite <- app_assoc. simpl.
    fold (ht_chain storeK storeV
      (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail)).
    sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
      index ptrs buckets (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail));
      entailer!.
    rewrite replace_Znth_Znth.
    entailer!.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Z.rem_mod_nonneg in PreH13 by lia.
    eapply buckets_abs_replace_first_in_bucket
      with (old_v := cur_v); eauto.
    rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
      by (rewrite PreH24, PreH13; apply Z.mod_pos_bound; lia).
    rewrite <- PreH14, PreH11. reflexivity.
  - rewrite Z.rem_mod_nonneg in PreH13 by lia.
    eapply buckets_hash_replace_entry
      with (old_entry := (cur_k, cur_v)); eauto.
    + rewrite PreH13. apply Z.mod_pos_bound. lia.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH24, PreH13; apply Z.mod_pos_bound; lia).
      rewrite <- PreH14, PreH11. reflexivity.
  - eapply buckets_unique_replace_entry
      with (old_k := cur_k) (old_v := cur_v); eauto.
    + rewrite PreH24, PreH13; split; assumption.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH24, PreH13; split; assumption).
      rewrite <- PreH14, PreH11. reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_5 : ht_add_return_wit_5.
Proof.
  LLM_pre_process auto.
  do 3 rewrite derivable1_andp_elim2.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  Exists new_m.
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks
    (replace_Znth index (l1 ++ (k, v) :: rest_tail) buckets).
  Exists (replace_Znth index (Znth index ptrs 0) ptrs).
  entailer!.
  - rewrite <- PreH12.
    sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth index ptrs 0) node cur_next key_pre val_pre k v l1);
      entailer!.
    unfold ht_chain.
    sep_apply (ht_chain_seg_app storeK storeV
      (Znth index ptrs 0) cur_next 0 (l1 +:: (k, v)) rest_tail);
      entailer!.
    rewrite <- app_assoc. simpl.
    fold (ht_chain storeK storeV
      (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail)).
    sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
      index ptrs buckets (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail));
      entailer!.
    rewrite replace_Znth_Znth.
    unfold entails_emp in PreH3.
    sep_apply (PreH3 cur_val cur_v). entailer!.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Z.rem_mod_nonneg in PreH12 by lia.
    eapply buckets_abs_replace_first_in_bucket
      with (old_v := cur_v); eauto.
    rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
      by (rewrite PreH23, PreH12; apply Z.mod_pos_bound; lia).
    rewrite <- PreH13, PreH10. reflexivity.
  - rewrite Z.rem_mod_nonneg in PreH12 by lia.
    eapply buckets_hash_replace_entry
      with (old_entry := (cur_k, cur_v)); eauto.
    + rewrite PreH12. apply Z.mod_pos_bound. lia.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH23, PreH12; apply Z.mod_pos_bound; lia).
      rewrite <- PreH13, PreH10. reflexivity.
  - eapply buckets_unique_replace_entry
      with (old_k := cur_k) (old_v := cur_v); eauto.
    + rewrite PreH23, PreH12; split; assumption.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH23, PreH12; split; assumption).
      rewrite <- PreH13, PreH10. reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_6 : ht_add_return_wit_6.
Proof.
  LLM_pre_process auto.
  subst cur_val.
  unfold store_exclusive in PreH3.
  do 5 rewrite derivable1_andp_elim2.
  sep_apply (PreH3 val_pre cur_v v).
  entailer!.
Qed.

Lemma proof_of_ht_add_return_wit_7 : ht_add_return_wit_7.
Proof.
  LLM_pre_process auto.
  do 2 rewrite derivable1_andp_elim2.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  Exists new_m.
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks
    (replace_Znth index (l1 ++ (k, v) :: rest_tail) buckets).
  Exists (replace_Znth index (Znth index ptrs 0) ptrs).
  entailer!.
  - rewrite <- PreH11.
    sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth index ptrs 0) node cur_next key_pre val_pre k v l1);
      entailer!.
    unfold ht_chain.
    sep_apply (ht_chain_seg_app storeK storeV
      (Znth index ptrs 0) cur_next 0 (l1 +:: (k, v)) rest_tail);
      entailer!.
    rewrite <- app_assoc. simpl.
    fold (ht_chain storeK storeV
      (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail)).
    sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
      index ptrs buckets (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail));
      entailer!.
    rewrite replace_Znth_Znth.
    unfold entails_emp in PreH3, PreH6.
    sep_apply (PreH3 cur_val cur_v).
    sep_apply (PreH6 cur_key cur_k). entailer!.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Z.rem_mod_nonneg in PreH11 by lia.
    eapply buckets_abs_replace_first_in_bucket
      with (old_v := cur_v); eauto.
    rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
      by (rewrite PreH22, PreH11; apply Z.mod_pos_bound; lia).
    rewrite <- PreH12, PreH9. reflexivity.
  - rewrite Z.rem_mod_nonneg in PreH11 by lia.
    eapply buckets_hash_replace_entry
      with (old_entry := (cur_k, cur_v)); eauto.
    + rewrite PreH11. apply Z.mod_pos_bound. lia.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH22, PreH11; apply Z.mod_pos_bound; lia).
      rewrite <- PreH12, PreH9. reflexivity.
  - eapply buckets_unique_replace_entry
      with (old_k := cur_k) (old_v := cur_v); eauto.
    + rewrite PreH22, PreH11; split; assumption.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH22, PreH11; split; assumption).
      rewrite <- PreH12, PreH9. reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_8 : ht_add_return_wit_8.
Proof.
  LLM_pre_process auto.
  subst cur_val.
  unfold store_exclusive in PreH3.
  do 4 rewrite derivable1_andp_elim2.
  sep_apply (PreH3 val_pre cur_v v).
  entailer!.
Qed.

Lemma proof_of_ht_add_return_wit_9 : ht_add_return_wit_9.
Proof.
  LLM_pre_process auto.
  subst cur_key.
  unfold store_exclusive in PreH6.
  do 4 rewrite derivable1_andp_elim2.
  sep_apply (PreH6 key_pre cur_k k).
  entailer!.
Qed.

Lemma proof_of_ht_add_return_wit_10 : ht_add_return_wit_10.
Proof.
  LLM_pre_process auto.
  subst cur_key.
  unfold store_exclusive in PreH6.
  do 5 rewrite derivable1_andp_elim2.
  sep_apply (PreH6 key_pre cur_k k).
  entailer!.
Qed.

Lemma proof_of_ht_add_return_wit_11 : ht_add_return_wit_11.
Proof.
  LLM_pre_process auto.
  do 2 rewrite derivable1_andp_elim2.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  Exists new_m.
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks
    (replace_Znth index (l1 ++ (k, v) :: rest_tail) buckets).
  Exists (replace_Znth index (Znth index ptrs 0) ptrs).
  entailer!.
  - rewrite <- PreH12.
    sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth index ptrs 0) node cur_next key_pre val_pre k v l1);
      entailer!.
    unfold ht_chain.
    sep_apply (ht_chain_seg_app storeK storeV
      (Znth index ptrs 0) cur_next 0 (l1 +:: (k, v)) rest_tail);
      entailer!.
    rewrite <- app_assoc. simpl.
    fold (ht_chain storeK storeV
      (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail)).
    sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
      index ptrs buckets (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail));
      entailer!.
    rewrite replace_Znth_Znth.
    unfold entails_emp in PreH3, PreH7.
    sep_apply (PreH3 cur_val cur_v).
    sep_apply (PreH7 cur_key cur_k). entailer!.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Z.rem_mod_nonneg in PreH12 by lia.
    eapply buckets_abs_replace_first_in_bucket
      with (old_v := cur_v); eauto.
    rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
      by (rewrite PreH23, PreH12; apply Z.mod_pos_bound; lia).
    rewrite <- PreH13, PreH10. reflexivity.
  - rewrite Z.rem_mod_nonneg in PreH12 by lia.
    eapply buckets_hash_replace_entry
      with (old_entry := (cur_k, cur_v)); eauto.
    + rewrite PreH12. apply Z.mod_pos_bound. lia.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH23, PreH12; apply Z.mod_pos_bound; lia).
      rewrite <- PreH13, PreH10. reflexivity.
  - eapply buckets_unique_replace_entry
      with (old_k := cur_k) (old_v := cur_v); eauto.
    + rewrite PreH23, PreH12; split; assumption.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH23, PreH12; split; assumption).
      rewrite <- PreH13, PreH10. reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_12 : ht_add_return_wit_12.
Proof.
  LLM_pre_process auto.
  subst cur_val.
  unfold store_exclusive in PreH3.
  do 4 rewrite derivable1_andp_elim2.
  sep_apply (PreH3 val_pre cur_v v).
  entailer!.
Qed.

Lemma proof_of_ht_add_return_wit_13 : ht_add_return_wit_13.
Proof.
  LLM_pre_process auto.
  do 3 rewrite derivable1_andp_elim2.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  Exists new_m.
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks
    (replace_Znth index (l1 ++ (k, v) :: rest_tail) buckets).
  Exists (replace_Znth index (Znth index ptrs 0) ptrs).
  entailer!.
  - rewrite <- PreH13.
    sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth index ptrs 0) node cur_next key_pre val_pre k v l1);
      entailer!.
    unfold ht_chain.
    sep_apply (ht_chain_seg_app storeK storeV
      (Znth index ptrs 0) cur_next 0 (l1 +:: (k, v)) rest_tail);
      entailer!.
    rewrite <- app_assoc. simpl.
    fold (ht_chain storeK storeV
      (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail)).
    sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
      index ptrs buckets (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail));
      entailer!.
    rewrite replace_Znth_Znth.
    unfold entails_emp in PreH4.
    sep_apply (PreH4 cur_val cur_v). entailer!.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Z.rem_mod_nonneg in PreH13 by lia.
    eapply buckets_abs_replace_first_in_bucket
      with (old_v := cur_v); eauto.
    rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
      by (rewrite PreH24, PreH13; apply Z.mod_pos_bound; lia).
    rewrite <- PreH14, PreH11. reflexivity.
  - rewrite Z.rem_mod_nonneg in PreH13 by lia.
    eapply buckets_hash_replace_entry
      with (old_entry := (cur_k, cur_v)); eauto.
    + rewrite PreH13. apply Z.mod_pos_bound. lia.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH24, PreH13; apply Z.mod_pos_bound; lia).
      rewrite <- PreH14, PreH11. reflexivity.
  - eapply buckets_unique_replace_entry
      with (old_k := cur_k) (old_v := cur_v); eauto.
    + rewrite PreH24, PreH13; split; assumption.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH24, PreH13; split; assumption).
      rewrite <- PreH14, PreH11. reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_14 : ht_add_return_wit_14.
Proof.
  LLM_pre_process auto.
  do 2 rewrite derivable1_andp_elim2.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  Exists new_m.
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks
    (replace_Znth index (l1 ++ (k, v) :: rest_tail) buckets).
  Exists (replace_Znth index (Znth index ptrs 0) ptrs).
  entailer!.
  - rewrite <- PreH12.
    sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth index ptrs 0) node cur_next key_pre val_pre k v l1);
      entailer!.
    unfold ht_chain.
    sep_apply (ht_chain_seg_app storeK storeV
      (Znth index ptrs 0) cur_next 0 (l1 +:: (k, v)) rest_tail);
      entailer!.
    rewrite <- app_assoc. simpl.
    fold (ht_chain storeK storeV
      (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail)).
    sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
      index ptrs buckets (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail));
      entailer!.
    rewrite replace_Znth_Znth.
    unfold entails_emp in PreH4, PreH7.
    sep_apply (PreH4 cur_val cur_v).
    sep_apply (PreH7 cur_key cur_k). entailer!.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Z.rem_mod_nonneg in PreH12 by lia.
    eapply buckets_abs_replace_first_in_bucket
      with (old_v := cur_v); eauto.
    rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
      by (rewrite PreH23, PreH12; apply Z.mod_pos_bound; lia).
    rewrite <- PreH13, PreH10. reflexivity.
  - rewrite Z.rem_mod_nonneg in PreH12 by lia.
    eapply buckets_hash_replace_entry
      with (old_entry := (cur_k, cur_v)); eauto.
    + rewrite PreH12. apply Z.mod_pos_bound. lia.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH23, PreH12; apply Z.mod_pos_bound; lia).
      rewrite <- PreH13, PreH10. reflexivity.
  - eapply buckets_unique_replace_entry
      with (old_k := cur_k) (old_v := cur_v); eauto.
    + rewrite PreH23, PreH12; split; assumption.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH23, PreH12; split; assumption).
      rewrite <- PreH13, PreH10. reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_15 : ht_add_return_wit_15.
Proof.
  LLM_pre_process auto.
  subst cur_key.
  unfold store_exclusive in PreH7.
  do 4 rewrite derivable1_andp_elim2.
  sep_apply (PreH7 key_pre cur_k k).
  entailer!.
Qed.

Lemma proof_of_ht_add_return_wit_16 : ht_add_return_wit_16.
Proof.
  LLM_pre_process auto.
  do 2 rewrite derivable1_andp_elim2.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  Exists new_m.
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks
    (replace_Znth index (l1 ++ (k, v) :: rest_tail) buckets).
  Exists (replace_Znth index (Znth index ptrs 0) ptrs).
  entailer!.
  - rewrite <- PreH13.
    sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth index ptrs 0) node cur_next key_pre val_pre k v l1);
      entailer!.
    unfold ht_chain.
    sep_apply (ht_chain_seg_app storeK storeV
      (Znth index ptrs 0) cur_next 0 (l1 +:: (k, v)) rest_tail);
      entailer!.
    rewrite <- app_assoc. simpl.
    fold (ht_chain storeK storeV
      (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail)).
    sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
      index ptrs buckets (Znth index ptrs 0) (l1 ++ (k, v) :: rest_tail));
      entailer!.
    rewrite replace_Znth_Znth.
    unfold entails_emp in PreH4, PreH8.
    sep_apply (PreH4 cur_val cur_v).
    sep_apply (PreH8 cur_key cur_k). entailer!.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Zlength_replace_Znth. auto.
  - rewrite Z.rem_mod_nonneg in PreH13 by lia.
    eapply buckets_abs_replace_first_in_bucket
      with (old_v := cur_v); eauto.
    rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
      by (rewrite PreH24, PreH13; apply Z.mod_pos_bound; lia).
    rewrite <- PreH14, PreH11. reflexivity.
  - rewrite Z.rem_mod_nonneg in PreH13 by lia.
    eapply buckets_hash_replace_entry
      with (old_entry := (cur_k, cur_v)); eauto.
    + rewrite PreH13. apply Z.mod_pos_bound. lia.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH24, PreH13; apply Z.mod_pos_bound; lia).
      rewrite <- PreH14, PreH11. reflexivity.
  - eapply buckets_unique_replace_entry
      with (old_k := cur_k) (old_v := cur_v); eauto.
    + rewrite PreH24, PreH13; split; assumption.
    + rewrite (Znth_indep buckets index nil __default__List__Prod_K_V)
        by (rewrite PreH24, PreH13; split; assumption).
      rewrite <- PreH14, PreH11. reflexivity.
Qed.

Lemma proof_of_ht_add_return_wit_17 : ht_add_return_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite derivable1_andp_elim2.
  subst node.
  destruct l2 as [| [lk lv] tail].
  - rewrite app_nil_r in PreH4.
    rewrite (Znth_indep buckets index __default__List__Prod_K_V nil)
      in PreH4 by (rewrite PreH14, PreH3; split; assumption).
    assert (Hindex : index = key_hash k mod cap) by
      (rewrite PreH3, Z.rem_mod_nonneg by assumption; reflexivity).
    edestruct (buckets_insert_new_head key_eq key_hash
      cap index buckets l1 m k v)
      as [new_m [Hinsert [Hnew_abs [Hnew_hash Hnew_unique]]]];
      try solve [eauto].
    Exists new_m.
    unfold ht_store_map, ht_store.
    Exists hash equal key_free value_free cap bucks
      (replace_Znth index ((k, v) :: l1) buckets).
    Exists (replace_Znth index retval_2 ptrs).
    entailer!.
    + rewrite ht_chain_null_nil_equiv, sepcon_emp_logic_equiv'.
      fold (ht_chain storeK storeV (Znth index ptrs 0) l1).
      sep_apply (ht_chain_cons storeK storeV retval_2 key_pre val_pre
        (Znth index ptrs 0) k v l1 PreH1).
      rewrite <- PreH3.
      sep_apply (ht_bucket_chains_merge_replace_Znth storeK storeV
        index ptrs buckets retval_2 ((k, v) :: l1)); entailer!.
    + rewrite Zlength_replace_Znth; auto.
    + rewrite Zlength_replace_Znth; auto.
  - unfold ht_chain; simpl.
    andp_lift (“ 0 <> 0 ”); apply coq_prop_andp_left; intros; lia.
Qed.

Lemma proof_of_ht_add_which_implies_wit_1_split_goal_spatial : ht_add_which_implies_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_ht_add_which_implies_wit_1 : ht_add_which_implies_wit_1.
Proof.
  LLM_pre_process auto.
  unfold ht_chain_seg.
  entailer!.
Qed.

Lemma proof_of_ht_find_entail_wit_1 : ht_find_entail_wit_1.
Proof.
  LLM_pre_process auto.
  subst.
  pose proof (Z.rem_bound_pos (key_hash k) (Zlength ptrs)).
  entailer!.
Qed.

Lemma proof_of_ht_find_entail_wit_2 : ht_find_entail_wit_2.
Proof.
  LLM_pre_process auto.
  subst.
  Exists nil.
  Exists (Znth ((key_hash k) % (Zlength ptrs)) buckets
    __default__List__Prod_K_V).
  entailer!.
Qed.

Lemma proof_of_ht_find_entail_wit_5 : ht_find_entail_wit_5.
Proof.
  LLM_pre_process auto.
  rewrite derivable1_andp_elim2.
  subst.
  Exists (l1_2 ++ [(cur_k, cur_v)]).
  Exists rest_tail.
  entailer!.
  - sep_apply (ht_chain_seg_snoc storeK storeV
      (Znth ((key_hash k) % (Zlength ptrs)) ptrs 0)
      node cur_next cur_key cur_val cur_k cur_v l1_2);
      entailer!.
  - intros pk pv Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (PreH8 pk pv Hin).
    + simpl in Hin. destruct Hin as [Heq | []].
      injection Heq; intros; subst pk pv.
      unfold key_eq_equiv in PreH7.
      destruct PreH7 as [_ Hsym _].
      intro Hkcur. apply PreH1. exact (Hsym _ _ Hkcur).
  - rewrite <- PreH6.
    rewrite <- (app_assoc l1_2 ((cur_k, cur_v) :: nil) rest_tail).
    reflexivity.
Qed.

Lemma proof_of_ht_find_return_wit_1 : ht_find_return_wit_1.
Proof.
  LLM_pre_process auto.
  Right.
  subst node.
  destruct l2 as [| [lk lv] tail].
  2: { unfold ht_chain; simpl.
       andp_lift (“ 0 <> 0 ”); apply coq_prop_andp_left; intros; lia. }
  rewrite app_nil_r in PreH3.
  rewrite (Znth_indep buckets index __default__List__Prod_K_V nil)
    in PreH3 by (rewrite PreH13, PreH2; split; assumption).
  unfold ht_store_map, ht_store.
  Exists hash equal key_free value_free cap bucks buckets ptrs.
  entailer!.
  - rewrite PreH2, PreH3.
    rewrite PreH2.
    fold (ht_chain storeK storeV
      (Znth (Z.rem (key_hash k) cap) ptrs 0)
      (Znth (Z.rem (key_hash k) cap) buckets nil)).
    rewrite logic_equiv_corable_andp_sepcon1.
    + apply derivable1_andp_mono.
      * reflexivity.
      * rewrite derivable1_andp_elim2.
        cancel.
        rewrite ht_chain_null_nil_equiv, sepcon_emp_logic_equiv'.
        cancel.
        rewrite derivable1_sepcon_comm.
        apply (ht_bucket_chains_merge_remove_Znth storeK storeV
          (Z.rem (key_hash k) cap) ptrs buckets).
        -- rewrite PreH12; split; assumption.
        -- rewrite PreH12, PreH13; reflexivity.
    + apply ht_specs_corable.
  - eapply buckets_abs_get_none_at; eauto.
    + rewrite Z.rem_mod_nonneg by assumption; reflexivity.
    + intros pk pv Hin; apply (PreH5 pk pv).
      rewrite PreH3, PreH2; exact Hin.
Qed.

Lemma proof_of_ht_find_return_wit_2 : ht_find_return_wit_2.
Proof.
  LLM_pre_process auto.
  Left.
  subst l2.
  assert (Hhit : key_eq k cur_k).
  { unfold key_eq_equiv in PreH7.
    destruct PreH7 as [_ Hsym _].
    exact (Hsym _ _ PreH1). }
  rewrite (Znth_indep buckets index __default__List__Prod_K_V nil)
    in PreH6 by (rewrite PreH16, PreH5; split; assumption).
  assert (Hindex : index = key_hash k mod cap).
  { rewrite PreH5, Z.rem_mod_nonneg by assumption. reflexivity. }
  assert (Hget : map_get k m (Some cur_v)).
  { eapply (buckets_abs_get_some_at key_eq key_hash cap index buckets m
               k cur_k cur_v l1 rest_tail); try eassumption.
    - rewrite PreH5; split; assumption.
    - symmetry; exact PreH6. }
  Exists cur_v; entailer!.
  unfold ht_store_map_value_hole, ht_store_value_hole.
  Exists hash equal key_free value_free cap bucks buckets ptrs.
  entailer!.
  unfold ht_bucket_chains_value_hole.
  rewrite <- Hindex, <- PreH6.
  rewrite logic_equiv_corable_andp_sepcon1.
  - apply derivable1_andp_mono.
    + reflexivity.
    + rewrite derivable1_andp_elim2.
      rewrite derivable1_andp_elim2.
      rewrite PreH5.
      unfold ht_chain_value_hole.
      Exists l1 cur_k cur_v rest_tail node cur_key cur_next.
      entailer!.
  - apply ht_specs_corable.
Qed.

Lemma proof_of_ht_find_which_implies_wit_1 : ht_find_which_implies_wit_1.
Proof.
  LLM_pre_process auto.
  unfold ht_chain_seg.
  entailer!.
Qed.

Lemma proof_of_ht_remove_entail_wit_1 : ht_remove_entail_wit_1.
Proof.
  LLM_pre_process auto.
  subst.
  pose proof (Z.rem_bound_pos (key_hash k) (Zlength ptrs)).
  entailer!.
Qed.

Lemma proof_of_ht_remove_entail_wit_2 : ht_remove_entail_wit_2.
Proof.
  LLM_pre_process auto.
  subst.
  Exists (Znth (Z.rem (key_hash k) (Zlength ptrs)) ptrs 0) nil
    (Znth (Z.rem (key_hash k) (Zlength ptrs)) buckets
      __default__List__Prod_K_V).
  entailer!.
  - rewrite derivable1_andp_elim2.
    sep_apply (PtrArray.full_split_to_missing_i bucks
      (Z.rem (key_hash k) (Zlength ptrs)) (Zlength ptrs) ptrs 0); try lia.
    unfold ht_chain_bseg; entailer!.
  - simpl; apply Znth_indep; rewrite PreH8; lia.
Qed.

Lemma proof_of_ht_remove_entail_wit_5 : ht_remove_entail_wit_5.
Proof.
  LLM_pre_process auto.
  rewrite derivable1_andp_elim2.
  subst rest_2.
  Exists cur_next (pre_2 ++ [(cur_k, cur_v)]) rest_tail.
  entailer!.
  - sep_apply (ht_chain_bseg_snoc storeK storeV
      (bucks + index * sizeof(PTR)) node_ref node_2 cur_key cur_val
      cur_k cur_v pre_2); [entailer! | exact PreH4].
  - intros pk pv Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | [Heq | []]].
    + exact (PreH18 pk pv Hin).
    + injection Heq; intros; subst; exact PreH1.
  - rewrite PreH16, <- (app_assoc pre_2 ((cur_k, cur_v) :: nil) rest_tail).
    reflexivity.
Qed.

Lemma proof_of_ht_remove_return_wit_1 : ht_remove_return_wit_1.
Proof.
  LLM_pre_process auto.
  Right; subst node; destruct rest as [| [rk rv] tail].
  - eapply derivable1_trans.
    + apply derivable1_andp_mono; [reflexivity |].
      sep_apply (ht_bucket_chains_bseg_merge storeK storeV
        index cap bucks ptrs buckets node_ref 0 pre nil); try lia; entailer!.
    + Intros head.
      rewrite app_nil_r in PreH13.
      assert (Hb : replace_Znth index pre buckets = buckets) by
        (rewrite <- PreH13; apply replace_Znth_Znth; lia).
      rewrite app_nil_r, Hb.
      assert (Hindex : index = key_hash k mod cap) by
        (rewrite PreH10, Z.rem_mod_nonneg by assumption; reflexivity).
      assert (Hget : map_get k m None) by
        (eapply buckets_abs_get_none_at; eauto).
      unfold ht_store_map, ht_store.
      Exists hash equal key_free value_free cap bucks buckets
        (replace_Znth index head ptrs); entailer!.
      * rewrite logic_equiv_corable_andp_sepcon1;
          [entailer! | apply ht_specs_corable].
      * rewrite Zlength_replace_Znth; auto.
  - unfold ht_chain; simpl.
    andp_lift (“ 0 <> 0 ”); apply coq_prop_andp_left; intros; lia.
Qed.

Lemma proof_of_ht_remove_return_wit_2 : ht_remove_return_wit_2.
Proof.
  LLM_pre_process auto.
  do 2 rewrite derivable1_andp_elim2.
  Left; subst rest.
  assert (Hindex : index = key_hash k mod cap) by
    (rewrite PreH17, Z.rem_mod_nonneg by assumption; reflexivity).
  assert (Hget : map_get k m (Some cur_v)) by
    (eapply buckets_abs_get_some_at; eauto).
  destruct (buckets_remove_first_in_bucket key_eq key_hash
    cap index buckets pre rest_tail m k cur_k cur_v
    PreH21 PreH12 PreH9 PreH11 Hindex PreH14 PreH20 PreH22 PreH5
    PreH13 PreH15) as [new_m [Hremove [Hnew_abs [Hnew_hash Hnew_unique]]]].
  eapply derivable1_trans.
  - apply derivable1_andp_mono; [reflexivity |].
    sep_apply (ht_bucket_chains_bseg_merge storeK storeV
      index cap bucks ptrs buckets node_ref cur_next pre rest_tail);
      try lia; entailer!.
  - Intros head.
    Exists new_m cur_v.
    unfold ht_store_map, ht_store.
    Exists hash equal key_free value_free cap bucks
      (replace_Znth index (pre ++ rest_tail) buckets)
      (replace_Znth index head ptrs); entailer!.
    + rewrite logic_equiv_corable_andp_sepcon1;
        [entailer! | apply ht_specs_corable].
    + rewrite Zlength_replace_Znth; auto.
    + rewrite Zlength_replace_Znth; auto.
Qed.

Lemma proof_of_ht_remove_return_wit_3 : ht_remove_return_wit_3.
Proof.
  LLM_pre_process auto.
  rewrite derivable1_andp_elim2.
  Left; subst rest cur_key.
  unfold entails_emp in PreH3.
  eapply derivable1_trans.
  1: {
    apply derivable1_andp_mono; [reflexivity |].
    rewrite (logic_equiv_sepcon_comm
      (storeK key_pre k) (storeK key_pre cur_k ** _)).
    sepcon_assoc_change.
    sep_apply (PreH3 key_pre cur_k).
    rewrite sepcon_emp_logic_equiv'.
    reflexivity.
  }
  assert (Hindex : index = key_hash k mod cap) by
    (rewrite PreH16, Z.rem_mod_nonneg by assumption; reflexivity).
  assert (Hget : map_get k m (Some cur_v)) by
    (eapply buckets_abs_get_some_at; eauto).
  destruct (buckets_remove_first_in_bucket key_eq key_hash
    cap index buckets pre rest_tail m k cur_k cur_v
    PreH20 PreH11 PreH8 PreH10 Hindex PreH13 PreH19 PreH21 PreH4
    PreH12 PreH14) as [new_m [Hremove [Hnew_abs [Hnew_hash Hnew_unique]]]].
  eapply derivable1_trans.
  - apply derivable1_andp_mono; [reflexivity |].
    sep_apply (ht_bucket_chains_bseg_merge storeK storeV
      index cap bucks ptrs buckets node_ref cur_next pre rest_tail);
      try lia; entailer!.
  - Intros head.
    Exists new_m cur_v.
    unfold ht_store_map, ht_store.
    Exists hash equal key_free value_free cap bucks
      (replace_Znth index (pre ++ rest_tail) buckets)
      (replace_Znth index head ptrs); entailer!.
    + rewrite logic_equiv_corable_andp_sepcon1;
        [entailer! | apply ht_specs_corable].
    + rewrite Zlength_replace_Znth; auto.
    + rewrite Zlength_replace_Znth; auto.
Qed.

Lemma proof_of_ht_remove_return_wit_4 : ht_remove_return_wit_4.
Proof.
  LLM_pre_process auto.
  do 3 rewrite derivable1_andp_elim2.
  subst cur_key.
  sep_apply (PreH3 key_pre k cur_k); entailer!.
  apply coq_prop_andp_left; intros Hfalse; contradiction.
Qed.

Lemma proof_of_ht_remove_return_wit_5 : ht_remove_return_wit_5.
Proof.
  LLM_pre_process auto.
  rewrite derivable1_andp_elim2.
  Left; subst rest.
  unfold entails_emp in PreH4.
  eapply derivable1_trans.
  1: {
    apply derivable1_andp_mono; [reflexivity |].
    rewrite (logic_equiv_sepcon_comm
      (storeK key_pre k) (storeK cur_key cur_k ** _)).
    sepcon_assoc_change.
    sep_apply (PreH4 cur_key cur_k).
    rewrite sepcon_emp_logic_equiv'.
    reflexivity.
  }
  assert (Hindex : index = key_hash k mod cap) by
    (rewrite PreH17, Z.rem_mod_nonneg by assumption; reflexivity).
  assert (Hget : map_get k m (Some cur_v)) by
    (eapply buckets_abs_get_some_at; eauto).
  destruct (buckets_remove_first_in_bucket key_eq key_hash
    cap index buckets pre rest_tail m k cur_k cur_v
    PreH21 PreH12 PreH9 PreH11 Hindex PreH14 PreH20 PreH22 PreH5
    PreH13 PreH15) as [new_m [Hremove [Hnew_abs [Hnew_hash Hnew_unique]]]].
  eapply derivable1_trans.
  - apply derivable1_andp_mono; [reflexivity |].
    sep_apply (ht_bucket_chains_bseg_merge storeK storeV
      index cap bucks ptrs buckets node_ref cur_next pre rest_tail);
      try lia; entailer!.
  - Intros head.
    Exists new_m cur_v.
    unfold ht_store_map, ht_store.
    Exists hash equal key_free value_free cap bucks
      (replace_Znth index (pre ++ rest_tail) buckets)
      (replace_Znth index head ptrs); entailer!.
    + rewrite logic_equiv_corable_andp_sepcon1;
        [entailer! | apply ht_specs_corable].
    + rewrite Zlength_replace_Znth; auto.
    + rewrite Zlength_replace_Znth; auto.
Qed.
