From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P070_886D_restoration_of_string_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P070_886D_restoration_of_string_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P070_886D_restoration_of_string_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH8 PreH9 PreH20) as Hi.
  unfold string_length in Hi.
  rewrite c_string_Znth_inside by (unfold string_length; lia).
  specialize (PreH12 z i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH8 PreH9 PreH20) as Hi.
  unfold string_length in Hi.
  rewrite c_string_Znth_inside by (unfold string_length; lia).
  specialize (PreH12 z i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH22 PreH23 PreH34) as Hi.
  unfold string_length in Hi.
  specialize (PreH19 z ltac:(lia)).
  unfold string_length in PreH19.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH23 PreH24 PreH35) as Hi.
  unfold string_length in Hi.
  specialize (PreH20 z ltac:(lia)).
  unfold string_length in PreH20.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_1 : solver_safety_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH22 PreH23 PreH34) as Hi.
  unfold string_length in Hi.
  specialize (PreH19 z ltac:(lia)).
  unfold string_length in PreH19.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_2 : solver_safety_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_27_split_goal_1 : solver_safety_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH21 PreH22 PreH33) as Hi.
  unfold string_length in Hi.
  specialize (PreH18 z ltac:(lia)).
  unfold string_length in PreH18.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_27_split_goal_2 : solver_safety_wit_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_27_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_27_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_1 : solver_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH19 PreH20 PreH31) as Hi.
  unfold string_length in Hi.
  specialize (PreH16 z ltac:(lia)).
  unfold string_length in PreH16.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_2 : solver_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold InitState.
  split; [reflexivity |].
  split.
  - unfold AllMinusOne. intros k Hk. rewrite Zlength_nil in Hk. lia.
  - split.
    + unfold AllMinusOne. intros k Hk. rewrite Zlength_nil in Hk. lia.
    + unfold repeat_Z.
      apply repeat_zero_state__initialization_and_row_frame.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5. lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_5 : solver_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH4 k ltac:(lia)).
  specialize (PreH8 k ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply init_state_append_minus_one__initialization_and_row_frame.
  exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnext_prefix_len : Zlength next_prefix = 26) by lia.
  assert (Hprev_prefix_len : Zlength prev_prefix = 26) by lia.
  assert (Hi : i = 26) by lia.
  subst i.
  pose proof PreH13 as Hinit.
  unfold InitState in Hinit.
  destruct Hinit as [_ [_ [_ [Hused_boolean Hused_zero]]]].
  destruct Hused_boolean as [Hused_len Hused_values].
  pose proof
    (encodes_graph_empty_from_init__initialization_and_row_frame
      next_prefix prev_prefix used_l_2
      Hnext_prefix_len Hprev_prefix_len PreH13)
    as Henc.
  assert (Hgraph :
      GraphBuildState g 0 next_prefix prev_prefix used_l_2).
  {
    unfold GraphBuildState. split.
    - exact PreH2.
    - unfold sublist. simpl. exact Henc.
  }
  pose proof Henc as Henc_facts.
  unfold EncodesGraph, BoundedGraphArray in Henc_facts.
  destruct Henc_facts as
    [_ [[Hnext_len Hnext_bounds]
      [[Hprev_len Hprev_bounds] _]]].
  Exists used_l_2 prev_prefix next_prefix.
  split_pure_spatial.
  - rewrite Hnext_prefix_len.
    rewrite !IntArray.undef_seg_empty.
    sep_apply_l_atomic
      (IntArray.seg_to_full (&( "next" )) 0 26 next_prefix).
    replace (&( "next" ) + 0 * sizeof(INT)) with (&( "next" )) by lia.
    replace (26 - 0) with 26 by lia.
    sep_apply_l_atomic
      (IntArray.seg_to_full (&( "prev" )) 0 26 prev_prefix).
    replace (&( "prev" ) + 0 * sizeof(INT)) with (&( "prev" )) by lia.
    replace (26 - 0) with 26 by lia.
    cancel (CharPtrArray2.full words_pre n_pre rows).
    cancel (CharArray.undef_full out_pre 64).
    cancel (IntArray.full (&( "next" )) 26 next_prefix).
    cancel (IntArray.full (&( "prev" )) 26 prev_prefix).
    cancel (IntArray.full (&( "used" )) 26 used_l_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH6 z ltac:(lia)).
  destruct PreH6 as [[[[Hpositive Hupper] Hrow] Hvalid] Hstrlen].
  assert (Hrow_default :
      Znth z rows __default__List_Z = Znth z rows (@nil Z)) by
    (apply Znth_indep; lia).
  rewrite Hrow_default, Hrow.
  rewrite c_string_Zlength.
  unfold naive_C_Rules.string_length.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  apply word_scan_state_zero__initialization_and_row_frame.
  exact PreH14.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH13. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH12. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_5 : solver_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_6 : solver_entail_wit_5_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Zlength_nonneg.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_7 : solver_entail_wit_5_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5. lia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH18 PreH19 PreH30) as Hi.
  rewrite c_string_Znth_inside by lia.
  assert (Hzi : ((0 <= z < n_pre /\ 0 <= i) /\ i < Zlength (Znth z g nil))).
  { split. { split. { split; lia. } exact PreH18. } exact Hi. }
  specialize (PreH22 z i Hzi).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH18 PreH19 PreH30) as Hi.
  rewrite c_string_Znth_inside by lia.
  assert (Hzi : ((0 <= z < n_pre /\ 0 <= i) /\ i < Zlength (Znth z g nil))).
  { split. { split. { split; lia. } exact PreH18. } exact Hi. }
  specialize (PreH22 z i Hzi).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (x := Znth i (c_string (Znth z g nil)) 0 - 97) in *.
  assert (Hi : i < Zlength (Znth z g nil)).
  { apply c_string_nonzero_index_lt; assumption. }
  assert (Hchar : Znth i (Znth z g nil) 0 = 97 + x).
  { unfold x. rewrite c_string_Znth_inside by (unfold string_length; lia). lia. }
  assert (Hprev : Znth x prev_l_2 (-1) = last).
  { rewrite (Znth_indep prev_l_2 x (-1) 0) by lia. exact PreH1. }
  pose proof PreH33 as Hstate.
  unfold WordScanState in Hstate.
  destruct Hstate as [_ [Henc _]]. unfold EncodesGraph in Henc.
  destruct Henc as (_ & _ & _ & _ & _ & Hnextiff & Hpreviff).
  assert (Hadj : AdjacentInWords
      (List.app (sublist 0 z g) ((sublist 0 i (Znth z g nil)) :: nil))
      (97 + last) (97 + x)).
  { apply (proj1 (Hpreviff last x ltac:(lia) ltac:(lia))). exact Hprev. }
  assert (Hnext : Znth last next_l_2 (-1) = x).
  { apply (proj2 (Hnextiff last x ltac:(lia) ltac:(lia))). exact Hadj. }
  apply word_scan_step_existing_edge__word_scan_steps; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_2 : solver_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_3 : solver_entail_wit_7_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_4 : solver_entail_wit_7_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_5 : solver_entail_wit_7_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_6 : solver_entail_wit_7_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH22 PreH23 PreH34) as Hi.
  unfold string_length in Hi. lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (x := Znth i (c_string (Znth z g nil)) 0 - 97) in *.
  assert (Hi : i < Zlength (Znth z g nil)).
  { apply c_string_nonzero_index_lt; assumption. }
  assert (Hchar : Znth i (Znth z g nil) 0 = 97 + x).
  { unfold x. rewrite c_string_Znth_inside by (unfold string_length; lia). lia. }
  assert (Hnext : Znth last next_l_2 (-1) = x).
  { rewrite (Znth_indep next_l_2 last (-1) 0) by lia. exact PreH3. }
  assert (Hprev : Znth x prev_l_2 (-1) = last).
  { rewrite (Znth_indep prev_l_2 x (-1) 0) by lia. exact PreH1. }
  apply word_scan_step_existing_edge__word_scan_steps; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_2 : solver_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_3 : solver_entail_wit_7_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_4 : solver_entail_wit_7_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_5 : solver_entail_wit_7_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_6 : solver_entail_wit_7_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH23 PreH24 PreH35) as Hi.
  unfold string_length in Hi. lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_7_3_split_goal_1 : solver_entail_wit_7_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (x := Znth i (c_string (Znth z g nil)) 0 - 97) in *.
  assert (Hi : i < Zlength (Znth z g nil)).
  { apply c_string_nonzero_index_lt; assumption. }
  assert (Hchar : Znth i (Znth z g nil) 0 = 97 + x).
  { unfold x. rewrite c_string_Znth_inside by (unfold string_length; lia). lia. }
  assert (Hnext : Znth last next_l_2 (-1) = x).
  { rewrite (Znth_indep next_l_2 last (-1) 0) by lia. exact PreH2. }
  pose proof PreH33 as Hstate.
  unfold WordScanState in Hstate.
  destruct Hstate as [_ [Henc _]]. unfold EncodesGraph in Henc.
  destruct Henc as (_ & _ & _ & _ & _ & Hnextiff & Hpreviff).
  assert (Hadj : AdjacentInWords
      (List.app (sublist 0 z g) ((sublist 0 i (Znth z g nil)) :: nil))
      (97 + last) (97 + x)).
  { apply (proj1 (Hnextiff last x ltac:(lia) ltac:(lia))). exact Hnext. }
  assert (Hprev : Znth x prev_l_2 (-1) = last).
  { apply (proj2 (Hpreviff last x ltac:(lia) ltac:(lia))). exact Hadj. }
  apply word_scan_step_existing_edge__word_scan_steps; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_3_split_goal_2 : solver_entail_wit_7_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_3_split_goal_3 : solver_entail_wit_7_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_3_split_goal_4 : solver_entail_wit_7_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_3_split_goal_5 : solver_entail_wit_7_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_3_split_goal_6 : solver_entail_wit_7_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH22 PreH23 PreH34) as Hi.
  unfold string_length in Hi. lia.
Qed.

Lemma proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_3_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_7_3_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_7_4_split_goal_1 : solver_entail_wit_7_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (x := Znth i (c_string (Znth z g nil)) 0 - 97) in *.
  assert (Hi : i < Zlength (Znth z g nil)).
  { apply c_string_nonzero_index_lt; assumption. }
  assert (Hchar : Znth i (Znth z g nil) 0 = 97 + x).
  { unfold x. rewrite c_string_Znth_inside by (unfold string_length; lia). lia. }
  assert (Hnext : Znth last next_l_2 (-1) = -1).
  { pose proof (PreH30 last ltac:(lia)) as Hbounds.
    pose proof (Znth_indep next_l_2 last (-1) 0 ltac:(lia)) as Hsame.
    destruct Hbounds as [Hlow Hhigh]. rewrite Hsame in Hlow. lia. }
  assert (Hprev : Znth x prev_l_2 (-1) = -1).
  { pose proof (PreH31 x ltac:(lia)) as Hbounds.
    pose proof (Znth_indep prev_l_2 x (-1) 0 ltac:(lia)) as Hsame.
    destruct Hbounds as [Hlow Hhigh]. rewrite Hsame in Hlow. lia. }
  apply word_scan_step_new_edge__word_scan_steps; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_4_split_goal_2 : solver_entail_wit_7_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_4_split_goal_3 : solver_entail_wit_7_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_4_split_goal_4 : solver_entail_wit_7_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_4_split_goal_5 : solver_entail_wit_7_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_4_split_goal_6 : solver_entail_wit_7_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (c_string_nonzero_index_lt (Znth z g nil) i PreH21 PreH22 PreH33) as Hi.
  unfold string_length in Hi. lia.
Qed.

Lemma proof_of_solver_entail_wit_7_4 : solver_entail_wit_7_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_4_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_7_4_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_7_5_split_goal_1 : solver_entail_wit_7_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (x := Znth i (c_string (Znth z g nil)) 0 - 97) in *.
  assert (Hi : i < Zlength (Znth z g nil)).
  { apply c_string_nonzero_index_lt; assumption. }
  assert (Hchar_i : Znth i (Znth z g nil) 0 = 97 + x).
  { unfold x. rewrite c_string_Znth_inside by (unfold string_length; lia). lia. }
  assert (Hlast : last = -1) by lia.
  assert (Hi0 : i = 0).
  { pose proof PreH30 as Hstate. unfold WordScanState in Hstate.
    destruct Hstate as [_ [_ [_ [_ Hcase]]]].
    destruct Hcase as [[Hzero Hminus] | [Hpos Hlastold]]; [lia|].
    specialize (PreH23 z (i - 1) ltac:(repeat split; lia)). lia. }
  subst i last.
  apply word_scan_step_first_char__word_scan_steps; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_5_split_goal_2 : solver_entail_wit_7_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_5_split_goal_3 : solver_entail_wit_7_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_5_split_goal_4 : solver_entail_wit_7_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i < Zlength (Znth z g nil)) by
    (apply c_string_nonzero_index_lt; auto).
  unfold string_length in Hi. lia.
Qed.

Lemma proof_of_solver_entail_wit_7_5 : solver_entail_wit_7_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_5_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold c_string in PreH20.
  eapply word_scan_finish_graph_build__graph_build_boundary; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_spatial : solver_entail_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH5 z ltac:(lia)) as Hrow.
  destruct Hrow as [[[_ Hrow] _] _].
  pose proof
    (CharPtrArray2.missing_i_merge_to_full
       words_pre z n_pre saved_s rows (Znth z rows (@nil Z))) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change
    (CharPtrArray2.ElemArray.full saved_s
       (Zlength (Znth z rows (@nil Z))) (Znth z rows (@nil Z)))
    with
    (CharArray.full saved_s
       (Zlength (Znth z rows (@nil Z))) (Znth z rows (@nil Z))) in Hmerge.
  rewrite Hrow in Hmerge.
  replace (Zlength (Znth z g (@nil Z)) + 1)
    with (Zlength (c_string (Znth z g (@nil Z)))) by
    (unfold c_string; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  sep_apply Hmerge; try lia.
  rewrite <- Hrow.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_4 : solver_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_1 : solver_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply traversal_state_zero__traversal_initialization.
  - unfold BooleanArray.
    split.
    + unfold repeat_Z.
      rewrite Zlength_correct, repeat_length.
      reflexivity.
    + intros k Hk.
      left.
      unfold repeat_Z.
      apply Znth_repeat.
  - unfold AllZero.
    intros k Hk.
    unfold repeat_Z.
    apply Znth_repeat.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_2 : solver_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace z with n_pre in PreH15 by lia.
  exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_3 : solver_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH14.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_4 : solver_entail_wit_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH13.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_5 : solver_entail_wit_10_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_6 : solver_entail_wit_10_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply path_scan_start__traversal_initialization; eauto.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH18.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_3 : solver_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH17.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GraphBuildState in PreH20.
  destruct PreH20 as [_ Henc].
  eapply path_scan_step__path_extension; eauto.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__path_entry_step.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_3 : solver_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_4 : solver_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GraphBuildState in PreH20.
  destruct PreH20 as [_ Henc].
  assert (Hc : 0 <= c < 26) by lia.
  pose proof (output_matches_visited_length_bound__path_extension
    _ _ _ _ _ _ _ _ Henc PreH21 Hc PreH1) as Hroom.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hroom.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_5 : solver_entail_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Heq : Znth c next_l_2 (-1) = Znth c next_l_2 0).
  { apply Znth_indep. lia. }
  assert (Hc : 0 <= c < 26) by lia.
  specialize (PreH18 c Hc).
  rewrite Heq in PreH18.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_6 : solver_entail_wit_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Heq : Znth c next_l_2 (-1) = Znth c next_l_2 0).
  { apply Znth_indep. lia. }
  assert (Hc : 0 <= c < 26) by lia.
  specialize (PreH18 c Hc).
  rewrite Heq in PreH18.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_13_1_split_goal_1 : solver_entail_wit_13_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (c = -1) by lia. subst c.
  unfold GraphBuildState in PreH19.
  destruct PreH19 as [_ Henc].
  eapply path_scan_finish_head__traversal_closure; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_2_split_goal_1 : solver_entail_wit_13_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PathScanState in PreH21.
  destruct PreH21 as
    (visited_before & output_before & path & Htraversal & Hhead & Hpath &
     Hmarked & Houtput & Hcurrent).
  destruct Hcurrent as [Hminusone | [Hbounds Hzero]].
  - lia.
  - congruence.
Qed.

Lemma proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GraphBuildState, EncodesGraph in PreH16.
  destruct PreH16 as (_ & _ & _ & Hprev & _).
  exact ((proj2 Hprev) k_2 H).
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GraphBuildState, EncodesGraph in PreH16.
  destruct PreH16 as (_ & _ & Hnext & _).
  exact ((proj2 Hnext) k H).
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply traversal_state_skip_nonhead__traversal_closure.
  - lia.
  - exact PreH19.
  - left. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_1 : solver_entail_wit_14_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hdefaults : Znth start prev_l_2 (-1) = Znth start prev_l_2 0).
  { apply Znth_indep. lia. }
  apply traversal_state_skip_nonhead__traversal_closure.
  - lia.
  - exact PreH20.
  - right. rewrite Hdefaults. lia.
Qed.

Lemma proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CoverageScanState.
  unfold GraphBuildState in PreH17.
  destruct PreH17 as [_ Hgraph].
  unfold EncodesGraph in Hgraph.
  destruct Hgraph as [_ [_ [_ [Hused _]]]].
  unfold TraversalState in PreH18.
  destruct PreH18 as [Hcompleted _].
  unfold CompletedHeadSet in Hcompleted.
  destruct Hcompleted as [Hvisited _].
  split; [exact Hused|].
  split; [exact Hvisited|].
  intros k Hk.
  exfalso; lia.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace 26 with start by lia.
  exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_3 : solver_entail_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH16.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_4 : solver_entail_wit_15_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH15.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_16_split_goal_1 : solver_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (c = 26) by lia. subst c.
  unfold GraphBuildState in PreH17.
  destruct PreH17 as [Hpre Hgraph].
  rewrite PreH2 in Hgraph.
  rewrite (sublist_self g (Zlength g) eq_refl) in Hgraph.
  unfold SuccessfulTraversal.
  split; [exact Hgraph|].
  split; [exact PreH18|].
  split; [exact PreH19|].
  eapply covered_traversal_good_restoration__successful_traversal; eauto.
Qed.

Lemma proof_of_solver_entail_wit_16 : solver_entail_wit_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_17_1_split_goal_1 : solver_entail_wit_17_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply coverage_scan_step__coverage_scan; eauto.
Qed.

Lemma proof_of_solver_entail_wit_17_1 : solver_entail_wit_17_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_17_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_17_2_split_goal_1 : solver_entail_wit_17_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply coverage_scan_step__coverage_scan; eauto.
Qed.

Lemma proof_of_solver_entail_wit_17_2 : solver_entail_wit_17_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_17_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SuccessfulTraversal in PreH8.
  destruct PreH8 as [_ [_ [_ Hgood]]].
  Exists output_l.
  unfold Spec.
  sep_apply_l_atomic
    (CharArray.seg_to_full out_pre 0 (len + 1) (output_l +:: 0)).
  replace (out_pre + 0 * sizeof(CHAR)) with out_pre by lia.
  replace (len + 1 - 0) with (len + 1) by lia.
  rewrite PreH7.
  split_pure_spatial.
  - cancel (CharPtrArray2.full words_pre n_pre rows).
    cancel (CharArray.full out_pre (len + 1) (output_l +:: 0)).
    cancel (CharArray.undef_seg out_pre (len + 1) 64).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact Hgood.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Henc : EncodesGraph g next_l prev_l used_l).
  {
    unfold GraphBuildState in PreH19.
    destruct PreH19 as [Hpre Henc].
    rewrite sublist_self in Henc by lia.
    exact Henc.
  }
  assert (Hspec : Spec g None).
  {
    unfold Spec.
    eapply used_unvisited_no_restoration__cycle_failure_return; eauto; lia.
  }
  Exists output_l len.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.seg_to_full out_pre 0 len output_l).
    replace (out_pre + 0 * sizeof(CHAR)) with out_pre by lia.
    replace (len - 0) with len by lia.
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hilt : i < Zlength (Znth z g (@nil Z))).
  { eapply c_string_nonzero_index_lt.
    - lia.
    - unfold string_length. lia.
    - auto. }
  set (cur := Znth i (c_string (Znth z g (@nil Z))) 0 - 97).
  assert (Hcurvalue : Znth i (Znth z g (@nil Z)) 0 = 97 + cur).
  { unfold cur. rewrite <- c_string_Znth_inside by (unfold string_length; lia). lia. }
  pose proof (outgoing_conflict_no_restoration__word_failure_returns
    g z i next_l prev_l used_l seen_l last cur PreH32
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cur; lia)
    Hilt Hcurvalue PreH2 ltac:(unfold cur; exact PreH1)) as Hspec.
  Exists (@nil Z) 0.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.undef_full_to_undef_seg out_pre 64).
    rewrite (CharArray.full_empty out_pre 0).
    cancel (CharArray.undef_seg out_pre 0 64).
    pose proof (PreH18 z ltac:(lia)) as Hrow.
    destruct Hrow as [[[_ Hrow] _] _].
    assert (Hrowlen : Zlength (Znth z g (@nil Z)) + 1 =
      Zlength (Znth z rows (@nil Z))).
    { rewrite Hrow. unfold c_string.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    rewrite Hrowlen.
    rewrite <- Hrow.
    pose proof (CharPtrArray2.missing_i_merge_to_full
      words_pre z n_pre saved_s rows (Znth z rows (@nil Z))) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    change (CharPtrArray2.ElemArray.full saved_s
      (Zlength (Znth z rows (@nil Z))) (Znth z rows (@nil Z))) with
      (CharArray.full saved_s (Zlength (Znth z rows (@nil Z)))
        (Znth z rows (@nil Z))) in Hmerge.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by (rewrite PreH18; lia).
    cancel.
    all: try cancel; try lia; try (dump_pre_spatial; lia).
    all: try (split_pures; dump_pre_spatial; lia).
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: simpl; try assumption; try lia.
    all: rewrite Zlength_nil; reflexivity.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hilt : i < Zlength (Znth z g (@nil Z))).
  { eapply c_string_nonzero_index_lt.
    - lia.
    - unfold string_length. lia.
    - auto. }
  set (cur := Znth i (c_string (Znth z g (@nil Z))) 0 - 97).
  assert (Hcurvalue : Znth i (Znth z g (@nil Z)) 0 = 97 + cur).
  { unfold cur. rewrite <- c_string_Znth_inside by (unfold string_length; lia). lia. }
  pose proof (incoming_conflict_no_restoration__word_failure_returns
    g z i next_l prev_l used_l seen_l last cur PreH33
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cur; lia)
    Hilt Hcurvalue PreH2 ltac:(unfold cur; exact PreH1)) as Hspec.
  Exists (@nil Z) 0.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.undef_full_to_undef_seg out_pre 64).
    rewrite (CharArray.full_empty out_pre 0).
    cancel (CharArray.undef_seg out_pre 0 64).
    pose proof (PreH19 z ltac:(lia)) as Hrow.
    destruct Hrow as [[[_ Hrow] _] _].
    assert (Hrowlen : Zlength (Znth z g (@nil Z)) + 1 =
      Zlength (Znth z rows (@nil Z))).
    { rewrite Hrow. unfold c_string.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    rewrite Hrowlen.
    rewrite <- Hrow.
    pose proof (CharPtrArray2.missing_i_merge_to_full
      words_pre z n_pre saved_s rows (Znth z rows (@nil Z))) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    change (CharPtrArray2.ElemArray.full saved_s
      (Zlength (Znth z rows (@nil Z))) (Znth z rows (@nil Z))) with
      (CharArray.full saved_s (Zlength (Znth z rows (@nil Z)))
        (Znth z rows (@nil Z))) in Hmerge.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by (rewrite PreH19; lia).
    cancel.
    all: try cancel; try lia; try (dump_pre_spatial; lia).
    all: try (split_pures; dump_pre_spatial; lia).
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: simpl; try assumption; try lia.
    all: rewrite Zlength_nil; reflexivity.
Qed.

Lemma proof_of_solver_return_wit_5 : solver_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH34 as Hstate.
  unfold WordScanState in Hstate.
  destruct Hstate as [_ [Henc _]].
  pose proof (encoded_next_prev_zero_defaults__word_failure_returns
    _ _ _ _ last
    (Znth i (c_string (Znth z g (@nil Z))) 0 - 97)
    Henc ltac:(lia) ltac:(lia) PreH3) as Hprev.
  exfalso.
  apply PreH1.
  exact Hprev.
Qed.

Lemma proof_of_solver_return_wit_6 : solver_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hilt : i < Zlength (Znth z g (@nil Z))).
  { eapply c_string_nonzero_index_lt.
    - lia.
    - unfold string_length. lia.
    - auto. }
  set (cur := Znth i (c_string (Znth z g (@nil Z))) 0 - 97).
  assert (Hcurvalue : Znth i (Znth z g (@nil Z)) 0 = 97 + cur).
  { unfold cur. rewrite <- c_string_Znth_inside by (unfold string_length; lia). lia. }
  pose proof (duplicate_scanned_character_no_restoration__word_failure_returns
    g z i next_l prev_l used_l seen_l last cur PreH29
    ltac:(lia) ltac:(lia) ltac:(unfold cur; lia) Hilt Hcurvalue
    ltac:(unfold cur; exact PreH31)) as Hspec.
  Exists (@nil Z) 0.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.undef_full_to_undef_seg out_pre 64).
    rewrite (CharArray.full_empty out_pre 0).
    cancel (CharArray.undef_seg out_pre 0 64).
    pose proof (PreH15 z ltac:(lia)) as Hrow.
    destruct Hrow as [[[_ Hrow] _] _].
    assert (Hrowlen : Zlength (Znth z g (@nil Z)) + 1 =
      Zlength (Znth z rows (@nil Z))).
    { rewrite Hrow. unfold c_string.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    rewrite Hrowlen.
    rewrite <- Hrow.
    pose proof (CharPtrArray2.missing_i_merge_to_full
      words_pre z n_pre saved_s rows (Znth z rows (@nil Z))) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    change (CharPtrArray2.ElemArray.full saved_s
      (Zlength (Znth z rows (@nil Z))) (Znth z rows (@nil Z))) with
      (CharArray.full saved_s (Zlength (Znth z rows (@nil Z)))
        (Znth z rows (@nil Z))) in Hmerge.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by (rewrite PreH15; lia).
    cancel.
    all: try cancel; try lia; try (dump_pre_spatial; lia).
    all: try (split_pures; dump_pre_spatial; lia).
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: simpl; try assumption; try lia.
    all: rewrite Zlength_nil; reflexivity.
Qed.
