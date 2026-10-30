From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P047_1523C_compression_and_expansion_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P047_1523C_compression_and_expansion_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (BoundedItem_Znth n_pre active (depth - 1) PreH18) as Hbound.
  assert (Hindex : 0 <= depth - 1 < Zlength active) by lia.
  specialize (Hbound Hindex).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (BoundedItem_Znth n_pre active (depth - 1) PreH18) as Hbound.
  assert (Hindex : 0 <= depth - 1 < Zlength active) by lia.
  specialize (Hbound Hindex).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH4 as HPre.
  unfold Pre in PreH4.
  destruct PreH4 as [_ [_ [items Hitems]]].
  assert (HSpec : Spec last_numbers items).
  {
    unfold Spec.
    exact Hitems.
  }
  assert (Hbounds : forall k,
    0 <= k < n_pre -> 1 <= Znth k last_numbers 0 <= n_pre).
  {
    intros k Hk.
    rewrite PreH5 in *.
    apply PreH3.
    exact Hk.
  }
  Exists
    (repeat None (Z.to_nat 1005))
    (@nil Z)
    (@nil Z)
    (@nil Z)
    items.
  sep_apply_l_atomic
    (IntArray.undef_full_to_mixed_full (&( "stack" )) 1005).
  sep_apply_l_atomic
    (IntArray.undef_full_to_undef_seg flat_pre (n_pre * n_pre)).
  sep_apply_l_atomic
    (IntArray.undef_full_to_undef_seg lengths_pre n_pre).
  rewrite (IntArray.seg_empty flat_pre 0 0).
  rewrite (IntArray.seg_empty lengths_pre 0 0).
  split_pure_spatial.
  -
    cancel (IntArray.mixed_full (&( "stack" )) 1005
      (repeat None (Z.to_nat 1005))).
    cancel (IntArray.full values_pre n_pre last_numbers).
    cancel (IntArray.undef_seg flat_pre 0 (n_pre * n_pre)).
    cancel (IntArray.undef_seg lengths_pre 0 n_pre).
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia;
      try (unfold CurrentItem; left; split; reflexivity);
      try apply BoundedItem_nil;
      try (unfold FlatPrefix; rewrite Zsublist_nil by lia; reflexivity);
      try (unfold LengthsPrefix; split; [reflexivity | intros; lia]);
      try (rewrite Zlength_correct, repeat_length; reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Spec_nonone_pop__semantic_transitions
    last_numbers items_2 active_2 line PreH8 PreH15 ltac:(lia) PreH1)
    as [Hline Hpop].
  assert (Hdepth : 1 <= depth).
  { destruct Hpop as
      [prefix [last [suffix [Hactive [Htarget [Hx Hsuffix]]]]]].
    rewrite Hactive in PreH14.
    rewrite Zlength_app, Zlength_cons in PreH14.
    pose proof (Zlength_nonneg prefix).
    pose proof (Zlength_nonneg suffix). lia. }
  Exists cells_2 lengths_data_2 flat_data_2 active_2
    (Znth line items_2 nil) items_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.mixed_full_split_to_mixed_missing_i
        (&( "stack")) (depth - 1) 1005 cells_2
        __default__App_option_Z ltac:(lia)).
    rewrite (PreH23 (depth - 1) ltac:(lia)).
    unfold IntArray.mixedstoreA. simpl. cancel.
  - split_pures;
      dump_pre_spatial; try assumption; try reflexivity;
      try (apply PreH23; lia); try lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PopTarget_remove_last__semantic_transitions
    n_pre active_2 target_2 x PreH19 PreH18
    ltac:(rewrite <- PreH17; exact PreH1))
    as [Hactive_len [Hremove_len [Hpop [Hbounded Hprefix]]]].
  Exists cells_2 lengths_data_2 flat_data_2 (removelast active_2)
    target_2 items_2.
  split_pure_spatial.
  - fold (IntArray.mixedstoreA
      (&( "stack")) (depth - 1)
      (Some (Znth (depth - 1) active_2 0))).
    sep_apply_l_atomic
      (IntArray.mixed_missing_i_merge_to_mixed_full
        (&( "stack")) (depth - 1) 1005
        (Some (Znth (depth - 1) active_2 0)) cells_2).
    + dump_pre_spatial. lia.
    + rewrite <- PreH27.
      rewrite replace_Znth_Znth.
      sep_apply_l_atomic
        (IntArray.mixed_full_split_to_mixed_missing_i
          (&( "stack")) (depth - 1 - 1) 1005 cells_2
          __default__App_option_Z ltac:(lia)).
      rewrite (PreH26 (depth - 1 - 1) ltac:(lia)).
      rewrite <- (Hprefix (depth - 1 - 1) ltac:(rewrite Hremove_len; lia)).
      unfold IntArray.mixedstoreA. simpl. cancel.
  - split_pures;
      dump_pre_spatial; try assumption; try reflexivity; try lia;
      try (rewrite Hremove_len, <- PreH17; lia);
      try (intros k Hk;
        rewrite Hprefix by (rewrite Hremove_len; lia);
        apply PreH26; lia);
      try (rewrite Hprefix by (rewrite Hremove_len; lia);
        apply PreH26; lia).
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Spec_one_append__semantic_transitions
    n_pre last_numbers items_2 active_2 line PreH8 PreH15
    ltac:(lia) PreH16 PreH3 PreH1) as Happend.
  pose proof (stack_append_one_invariant__semantic_transitions
    cells_2 active_2 depth __default__App_option_Z PreH14
    ltac:(rewrite PreH22; lia) PreH23) as [Hcells_len Hcells].
  Exists (replace_Znth depth (Some 1) cells_2)
    lengths_data_2 flat_data_2 (Znth line items_2 nil) items_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_int_undef_store_int
        (&( "x" )) (Znth line last_numbers 0)).
    cancel.
  - split_pures;
      dump_pre_spatial; try assumption; try reflexivity; try lia;
      try (rewrite Happend, Zlength_app, Zlength_cons; lia);
      try (rewrite Happend; apply BoundedItem_append_one; assumption);
      try (rewrite Hcells_len; assumption);
      try (rewrite Happend; exact Hcells).
  rewrite Happend, Zlength_app, Zlength_cons, Zlength_nil, <- PreH14.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH6 line ltac:(lia)) as Hxrange.
  rewrite <- PreH12 in Hxrange.
  pose proof (PopTarget_preserves_bounds n_pre active_2 target x
    PreH19 Hxrange PreH18) as Htarget_bound.
  destruct PreH18 as
    (prefix & last & suffix & Hactive & Htarget & Hx & Hfresh).
  assert (Hsuffix_nil : suffix = nil).
  {
    destruct suffix as [|s suffix]; [reflexivity |].
    exfalso.
    pose proof (Zlength_nonneg prefix) as Hprefix_nonneg.
    pose proof (Zlength_nonneg suffix) as Hsuffix_nonneg.
    assert (Hlastneq :
      Znth (Zlength (s :: suffix) - 1) (s :: suffix) 0 <> last).
    {
      apply (Forall_Znth__semantic_transitions
        Z (fun y => y <> last) (s :: suffix) 0).
      - exact Hfresh.
      - rewrite Zlength_cons. lia.
    }
    apply Hlastneq.
    assert (Hdepth :
      depth = Zlength prefix + 1 + Zlength (s :: suffix)).
    {
      rewrite PreH17, Hactive, Zlength_app, Zlength_cons.
      lia.
    }
    pose proof PreH1 as Htop.
    rewrite Hactive in Htop.
    replace (prefix ++ last :: s :: suffix)
      with ((prefix ++ last :: nil) ++ s :: suffix) in Htop
      by (rewrite <- app_assoc; reflexivity).
    assert (Hindex : Zlength (prefix ++ last :: nil) <= depth - 1).
    {
      rewrite Zlength_app, Zlength_cons, Zlength_nil.
      rewrite Zlength_cons in Hdepth.
      lia.
    }
    rewrite app_Znth2 in Htop by lia.
    assert (Heqindex :
      depth - 1 - Zlength (prefix ++ last :: nil) =
      Zlength (s :: suffix) - 1).
    {
      rewrite Zlength_app; repeat rewrite Zlength_cons; simpl.
      rewrite Zlength_cons in Hdepth.
      lia.
    }
    rewrite Heqindex in Htop.
    lia.
  }
  subst suffix.
  Exists (replace_Znth (depth - 1) (Some x) cells_2)
    lengths_data_2 flat_data_2 target items_2.
  split_pure_spatial.
  - fold (IntArray.mixedstoreA (&( "stack" )) (depth - 1) (Some x)).
    sep_apply_l_atomic
      (IntArray.mixed_missing_i_merge_to_mixed_full
        (&( "stack" )) (depth - 1) 1005 (Some x) cells_2 ltac:(lia)).
    sep_apply_l_atomic (store_int_undef_store_int (&( "x" )) x).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try reflexivity.
    all: try lia.
    + rewrite Htarget, PreH17, Hactive.
      repeat rewrite Zlength_app.
      repeat rewrite Zlength_cons.
      simpl. lia.
    + rewrite Zlength_replace_Znth.
      exact PreH25.
    + intros k Hk.
      assert (Hdepthprefix : depth = Zlength prefix + 1).
      {
        rewrite PreH17, Hactive, Zlength_app, Zlength_cons.
        simpl. lia.
      }
      destruct (Z.eq_dec k (depth - 1)) as [Heq | Hneq].
      * subst k.
        rewrite Znth_replace_Znth_Same by lia.
        rewrite Htarget, app_Znth2 by lia.
        replace (depth - 1 - Zlength prefix) with 0 by lia.
        simpl. rewrite Hx. reflexivity.
      * rewrite Znth_replace_Znth_Diff by lia.
        rewrite (PreH26 k ltac:(lia)).
        rewrite Hactive, Htarget.
        rewrite !app_Znth1 by lia.
        reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists cells_2 (lengths_data_2 ++ depth :: nil) flat_data_2
    flat_data_2 active_2 items_2.
  split_pure_spatial.
  - cancel (IntArray.full values_pre n_pre last_numbers).
    cancel (IntArray.mixed_full (&( "stack" )) 1005 cells_2).
    cancel (IntArray.seg flat_pre 0 total flat_data_2).
    cancel (IntArray.undef_seg flat_pre total (n_pre * n_pre)).
    cancel (IntArray.seg lengths_pre 0 (line + 1)
      (lengths_data_2 ++ depth :: nil)).
    cancel (IntArray.undef_seg lengths_pre (line + 1) n_pre).
  - split_pures;
      dump_pre_spatial;
      try assumption;
      try lia;
      try nia;
      try solve [simpl; rewrite app_nil_r; reflexivity];
      try solve [
        replace depth with (Zlength (Znth line items_2 nil)) by
          (rewrite <- PreH10, <- PreH13; reflexivity);
        eapply LengthsPrefix_snoc__flattening_and_completion; eauto; lia].
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists cells_2 lengths_data_2 flat_data_2 flat_before_2 active_2 items_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.mixed_full_split_to_mixed_missing_i
        (&( "stack" )) i 1005 cells_2 __default__App_option_Z ltac:(lia)).
    rewrite PreH27.
    simpl.
    cancel (IntArray.full values_pre n_pre last_numbers).
    cancel (IntArray.seg flat_pre 0 total flat_data_2).
    cancel (IntArray.undef_seg flat_pre total (n_pre * n_pre)).
    cancel (IntArray.seg lengths_pre 0 (line + 1) lengths_data_2).
    cancel (IntArray.undef_seg lengths_pre (line + 1) n_pre).
    cancel (IntArray.mixed_missing_i (&( "stack" )) i 0 1005 cells_2).
    cancel (((&( "stack" )) + i * sizeof(INT)) # Int
      |-> Znth i active_2 0).
    lia.
  - split_pures;
      dump_pre_spatial;
      try assumption;
      try lia;
      try nia;
      try solve [apply PreH27; lia].
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists cells_2 lengths_data_2
    (flat_data_2 ++ Znth i active_2 0 :: nil)
    flat_before_2 active_2 items_2.
  split_pure_spatial.
  - cancel (IntArray.full values_pre n_pre last_numbers).
    cancel (IntArray.mixed_full (&( "stack" )) 1005 cells_2).
    cancel (IntArray.seg flat_pre 0 (total + 1)
      (flat_data_2 ++ Znth i active_2 0 :: nil)).
    cancel (IntArray.undef_seg flat_pre (total + 1) (n_pre * n_pre)).
    cancel (IntArray.seg lengths_pre 0 (line + 1) lengths_data_2).
    cancel (IntArray.undef_seg lengths_pre (line + 1) n_pre).
  - split_pures;
      dump_pre_spatial;
      try assumption;
      try lia;
      try nia;
      try solve [
        rewrite Zlength_app, Zlength_cons, Zlength_nil;
        lia].
  all: try match goal with
    | Hflat : ?fd = ?fb ++ sublist 0 ?idx ?xs
      |- ?fd ++ Znth ?idx ?xs 0 :: nil =
         ?fb ++ sublist 0 (?idx + 1) ?xs =>
        rewrite Hflat;
        rewrite (sublist_snoc_Znth__flattening_and_completion
          Z 0 idx xs) by lia;
        symmetry;
        apply app_assoc
    end.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = depth) by lia.
  subst i.
  assert (Hflatnext : FlatPrefix items_2 (line + 1) flat_data_2).
  {
    rewrite PreH20.
    replace (sublist 0 depth active_2) with active_2.
    - rewrite PreH11.
      eapply FlatPrefix_snoc__flattening_and_completion; eauto; lia.
    - symmetry; apply sublist_self.
      lia.
  }
  assert (Hcurrent : CurrentItem items_2 (line + 1) active_2).
  {
    unfold CurrentItem.
    right.
    split; [lia |].
    replace (line + 1 - 1) with line by lia.
    exact PreH11.
  }
  Exists cells_2 lengths_data_2 flat_data_2 active_2 items_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hline : line = n_pre) by lia.
  subst line.
  pose proof (FlatPrefix_full__flattening_and_completion
    items_2 n_pre flat_data_2 PreH19 ltac:(lia)) as Hflat.
  destruct (LengthsPrefix_full__flattening_and_completion
    items_2 n_pre lengths_data_2 ltac:(lia) PreH20) as [Hlen Hnth].
  Exists lengths_data_2 flat_data_2 items_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_int_undef_store_int (&("depth")) depth).
    sep_apply_l_atomic
      (IntArray.mixed_full_to_undef_full (&("stack")) 1005 cells).
    sep_apply_l_atomic
      (IntArray.seg_to_full flat_pre 0 total flat_data_2).
    sep_apply_l_atomic
      (IntArray.seg_to_full lengths_pre 0 n_pre lengths_data_2).
    IntArray.ArraySimplify.
    replace (flat_pre + 0 * sizeof(INT)) with flat_pre by lia.
    replace (total - 0) with total by lia.
    replace (lengths_pre + 0 * sizeof(INT)) with lengths_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    repeat cancel.
    cancel (IntArray.undef_seg flat_pre total (n_pre * n_pre)).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    intros k Hk.
    rewrite (Znth_indep items_2 k __default__List_Z nil ltac:(lia)).
    apply Hnth.
    exact Hk.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst flat_data.
  subst total.
  Exists lengths_data_2 items.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. reflexivity.
Qed.
