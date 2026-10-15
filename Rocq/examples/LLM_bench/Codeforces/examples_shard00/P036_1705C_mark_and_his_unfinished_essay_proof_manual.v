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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P036_1705C_mark_and_his_unfinished_essay_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P036_1705C_mark_and_his_unfinished_essay_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P036_1705C_mark_and_his_unfinished_essay_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_2_split_goal_1 : solver_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH11 as [Hstateslen [Hinitial Hstep]].
  specialize (Hstep i ltac:(lia)).
  specialize (PreH16 i ltac:(lia)).
  rewrite (Znth_default__copy_safety _ ops i (0,0) __default__Prod_Z_Z) in Hstep by lia.
  rewrite (Znth_default__copy_safety _ states i nil __default__List_Z) in Hstep by lia.
  destruct Hstep as [[HL HLR] [HR Hnext]].
  destruct PreH16 as [Hleft Hright].
  rewrite Hleft, Hright in *.

  change (length <= 219902325555200000) in PreH21.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_2_split_goal_2 : solver_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH11 as [Hstateslen [Hinitial Hstep]].
  specialize (Hstep i ltac:(lia)).
  specialize (PreH16 i ltac:(lia)).
  rewrite (Znth_default__copy_safety _ ops i (0,0) __default__Prod_Z_Z) in Hstep by lia.
  rewrite (Znth_default__copy_safety _ states i nil __default__List_Z) in Hstep by lia.
  destruct Hstep as [[HL HLR] [HR Hnext]].
  destruct PreH16 as [Hleft Hright].
  rewrite Hleft, Hright in *.

  change (length <= 219902325555200000) in PreH21.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_2_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_3_split_goal_1 : solver_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH11 as [Hstateslen [Hinitial Hstep]].
  specialize (Hstep i ltac:(lia)).
  specialize (PreH16 i ltac:(lia)).
  rewrite (Znth_default__copy_safety _ ops i (0,0) __default__Prod_Z_Z) in Hstep by lia.
  rewrite (Znth_default__copy_safety _ states i nil __default__List_Z) in Hstep by lia.
  destruct Hstep as [[HL HLR] [HR Hnext]].
  destruct PreH16 as [Hleft Hright].
  rewrite Hleft, Hright in *.

  change (length <= 219902325555200000) in PreH21.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_3_split_goal_2 : solver_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH11 as [Hstateslen [Hinitial Hstep]].
  specialize (Hstep i ltac:(lia)).
  specialize (PreH16 i ltac:(lia)).
  rewrite (Znth_default__copy_safety _ ops i (0,0) __default__Prod_Z_Z) in Hstep by lia.
  rewrite (Znth_default__copy_safety _ states i nil __default__List_Z) in Hstep by lia.
  destruct Hstep as [[HL HLR] [HR Hnext]].
  destruct PreH16 as [Hleft Hright].
  rewrite Hleft, Hright in *.

  change (length <= 219902325555200000) in PreH21.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH11 as [Hstateslen [Hinitial Hstep]].
  specialize (Hstep i ltac:(lia)).
  specialize (PreH16 i ltac:(lia)).
  rewrite (Znth_default__copy_safety _ ops i (0,0) __default__Prod_Z_Z) in Hstep by lia.
  rewrite (Znth_default__copy_safety _ states i nil __default__List_Z) in Hstep by lia.
  destruct Hstep as [[HL HLR] [HR Hnext]].
  destruct PreH16 as [Hleft Hright].
  rewrite Hleft, Hright in *.

  change (length <= 219902325555200000) in PreH21.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH11 as [Hstateslen [Hinitial Hstep]].
  specialize (Hstep i ltac:(lia)).
  specialize (PreH16 i ltac:(lia)).
  rewrite (Znth_default__copy_safety _ ops i (0,0) __default__Prod_Z_Z) in Hstep by lia.
  rewrite (Znth_default__copy_safety _ states i nil __default__List_Z) in Hstep by lia.
  destruct Hstep as [[HL HLR] [HR Hnext]].
  destruct PreH16 as [Hleft Hright].
  rewrite Hleft, Hright in *.

  change (length <= 219902325555200000) in PreH21.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyPasteStates in PreH12.
  unfold StateLengthsPrefix in PreH18.
  destruct PreH12 as [_ [_ Hops]].
  destruct PreH18 as [_ Hbefore].
  specialize (PreH17 i ltac:(lia)).
  specialize (Hops i ltac:(lia)).
  specialize (Hbefore i ltac:(lia)).
  destruct PreH17 as [Hleft Hright].
  destruct Hops as [[Hlo Hlr] [Hrlen Hnext]].
  rewrite (Znth_indep ops i __default__Prod_Z_Z (0, 0)) in Hleft by lia.
  replace (i - 0) with i in * by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyPasteStates in PreH12.
  unfold StateLengthsPrefix in PreH18.
  destruct PreH12 as [_ [_ Hops]].
  destruct PreH18 as [_ Hbefore].
  specialize (PreH17 i ltac:(lia)).
  specialize (Hops i ltac:(lia)).
  specialize (Hbefore i ltac:(lia)).
  destruct PreH17 as [Hleft Hright].
  destruct Hops as [[Hlo Hlr] [Hrlen Hnext]].
  rewrite (Znth_indep ops i __default__Prod_Z_Z (0, 0)) in Hleft by lia.
  replace (i - 0) with i in * by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyPasteStates in PreH12.
  unfold StateLengthsPrefix in PreH18.
  destruct PreH12 as [_ [_ Hops]].
  destruct PreH18 as [_ Hbefore].
  specialize (PreH17 i ltac:(lia)).
  specialize (Hops i ltac:(lia)).
  specialize (Hbefore i ltac:(lia)).
  destruct PreH17 as [Hleft Hright].
  destruct Hops as [[Hlo Hlr] [Hrlen Hnext]].
  rewrite (Znth_indep ops i __default__Prod_Z_Z (0, 0)) in Hleft by lia.
  replace (i - 0) with i in * by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyPasteStates in PreH12.
  unfold StateLengthsPrefix in PreH18.
  destruct PreH12 as [_ [_ Hops]].
  destruct PreH18 as [_ Hbefore].
  specialize (PreH17 i ltac:(lia)).
  specialize (Hops i ltac:(lia)).
  specialize (Hbefore i ltac:(lia)).
  destruct PreH17 as [Hleft Hright].
  destruct Hops as [[Hlo Hlr] [Hrlen Hnext]].
  rewrite (Znth_indep ops i __default__Prod_Z_Z (0, 0)) in Hleft by lia.
  replace (i - 0) with i in * by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyPasteStates in PreH12.
  unfold StateLengthsPrefix in PreH18.
  destruct PreH12 as [_ [_ Hops]].
  destruct PreH18 as [_ Hbefore].
  specialize (PreH17 i ltac:(lia)).
  specialize (Hops i ltac:(lia)).
  specialize (Hbefore i ltac:(lia)).
  destruct PreH17 as [Hleft Hright].
  destruct Hops as [[Hlo Hlr] [Hrlen Hnext]].
  rewrite (Znth_indep ops i __default__Prod_Z_Z (0, 0)) in Hleft by lia.
  replace (i - 0) with i in * by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CopyPasteStates in PreH12.
  unfold StateLengthsPrefix in PreH18.
  destruct PreH12 as [_ [_ Hops]].
  destruct PreH18 as [_ Hbefore].
  specialize (PreH17 i ltac:(lia)).
  specialize (Hops i ltac:(lia)).
  specialize (Hbefore i ltac:(lia)).
  destruct PreH17 as [Hleft Hright].
  destruct Hops as [[Hlo Hlr] [Hrlen Hnext]].
  rewrite (Znth_indep ops i __default__Prod_Z_Z (0, 0)) in Hleft by lia.
  replace (i - 0) with i in * by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_2.
Qed. 

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH10 as HPre.
  unfold Pre in PreH10.
  destruct PreH10 as
    (_ & _ & _ & _ & states & Hstates_len & Hstate0 & Hsteps & Hqueries).
  assert (Hstates : CopyPasteStates text ops states).
  {
    unfold CopyPasteStates.
    split.
    - exact Hstates_len.
    - split.
      + exact Hstate0.
      + exact Hsteps.
  }
  Exists (@nil Z) states.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.undef_full_to_undef_seg (&( "before" )) 40).
    rewrite (Int64Array.seg_empty (&( "before" )) 0).
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + rewrite (Znth_indep states 0 __default__List_Z (@nil Z)) by lia.
      unfold string_length in PreH1.
      rewrite Hstate0.
      exact PreH1.
    + unfold string_length in PreH1.
      lia.
    + unfold string_length in PreH1.
      lia.
    + unfold StateLengthsPrefix.
      split.
      * reflexivity.
      * intros i Hi. lia.
Qed. 

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH11 as Hstates_all.
  destruct PreH11 as [Hstates_len [Hinitial Hstep]].
  specialize (Hstep i ltac:(lia)).
  destruct Hstep as [[Hleft Hright] [Hright_bound Hnext]].
  pose proof PreH16 as Hops_ids.
  specialize (PreH16 i ltac:(lia)).
  destruct PreH16 as [Hleft_id Hright_id].
  rewrite (Znth_indep ops i __default__Prod_Z_Z (0, 0)) in
    Hleft_id, Hright_id by lia.
  rewrite (Znth_indep states_2 i __default__List_Z nil) in PreH19 by
    (rewrite Hstates_len; lia).
  assert (Hnext_len :
    Zlength (Znth (i + 1) states_2 __default__List_Z) =
    length + (Znth i rights 0 - Znth i lefts 0 + 1)).
  {
    rewrite (Znth_indep states_2 (i + 1) __default__List_Z nil) by
      (rewrite Hstates_len; lia).
    rewrite Hnext.
    unfold CopyPasteStep.
    rewrite Zlength_app, Zlength_sublist by lia.
    lia.
  }
  assert (Hnext_cap :
    Zlength (Znth (i + 1) states_2 __default__List_Z) <=
      219902325555200000).
  {
    rewrite (Znth_indep states_2 (i + 1) __default__List_Z nil) by
      (rewrite Hstates_len; lia).
    assert (Hpow := copy_paste_states_length_pow_bound__copy_state_transition
      text ops states_2 (i + 1)).
    specialize (Hpow Hstates_all PreH4 ltac:(lia)).
    assert (Hmono : 2 ^ (i + 1) <= 2 ^ 40).
    { apply Z.pow_le_mono_r; lia. }
    assert (Hcalc : 200000 * 2 ^ 40 = 219902325555200000).
    { change (219902325555200000 = 219902325555200000).
      reflexivity. }
    nia.
  }
  assert (Hprefix :
    StateLengthsPrefix states_2 (i + 1) (before_data_2 ++ length :: nil)).
  {
    unfold StateLengthsPrefix in *.
    destruct PreH22 as [Hbefore_len Hbefore].
    split.
    - rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    - intros j Hj.
      destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
      + rewrite Znth_app_left__copy_state_transition by lia.
        apply Hbefore.
        lia.
      + assert (j = i) by lia.
        subst j.
        assert (HZ : Znth i (before_data_2 ++ length :: nil) 0 = length).
        { rewrite <- Hbefore_len at 1.
          apply Znth_app_last__copy_state_transition. }
        rewrite HZ.
        exact PreH19.
  }
  Exists (before_data_2 ++ length :: nil) states_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.full s_pre (string_length text + 1) (c_string text)).
    cancel (Int64Array.full l_pre c_pre lefts).
    cancel (Int64Array.full r_pre c_pre rights).
    cancel (Int64Array.full queries_pre q_pre queries_data).
    cancel (CharArray.undef_full answers_pre q_pre).
    cancel (Int64Array.seg &( "before") 0 (i + 1)
      (before_data_2 ++ length :: nil)).
    cancel (Int64Array.undef_seg &( "before") (i + 1) 40).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = c_pre) by lia.
  subst i.
  assert (Hanswer : AnswerPrefix text ops queries_data 0 nil).
  {
    unfold AnswerPrefix.
    repeat split; try reflexivity; try lia.
  }
  Exists nil before_data_2 states_2.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.undef_full_to_undef_seg answers_pre q_pre).
    rewrite CharArray.seg_empty.
    CharArray.ArraySimplify.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HC : c_pre = Zlength ops) by assumption.
  assert (HQ : q_pre = Zlength queries_data) by assumption.
  assert (HS : CopyPasteStates text ops states_2) by assumption.
  assert (HP : Pre text ops queries_data) by assumption.
  pose proof (backtrack_start__backtrack_transitions text ops queries_data states_2 z HP HS ltac:(lia)) as [HB HK].
  rewrite <- HC in HB.
  Exists out_2 before_data_2 states_2.
  unfold store_string.
  split_pure_spatial; [repeat progress cancel |].
  split_pures; dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HS : CopyPasteStates text ops states_2) by assumption.
  assert (HB : BacktrackedPosition states_2 (Znth z queries_data 0) i k) by assumption.
  pose proof (backtrack_finish__backtrack_transitions text ops states_2 (Znth z queries_data 0) i k HS HB ltac:(lia)) as [HK HF].
  Exists out_2 before_data_2 states_2.
  split_pure_spatial; [repeat progress cancel |].
  split_pures; dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HC : c_pre = Zlength ops) by assumption.
  assert (HS : CopyPasteStates text ops states_2) by assumption.
  assert (HB : BacktrackedPosition states_2 (Znth z queries_data 0) i k) by assumption.
  assert (HL : StateLengthsPrefix states_2 c_pre before_data_2) by assumption.
  destruct HL as [_ HL]. specialize (HL i ltac:(lia)).
  assert (HO : fst (Znth i ops (0,0)) = Znth i lefts 0).
  { rewrite (Znth_indep ops i (0,0) __default__Prod_Z_Z) by lia.
    match goal with H : forall j, 0 <= j < c_pre -> _ |- _ => specialize (H i ltac:(lia)); tauto end. }
  pose proof (backtrack_right__backtrack_transitions text ops states_2 (Znth z queries_data 0) i k HS HB ltac:(lia) ltac:(replace (i-0) with i in * by lia; lia)) as HN.
  rewrite HO, <- HL in HN.
  replace (i-0) with i by lia.
  assert (HK : 1 <= Znth i lefts 0 + k - Znth i before_data_2 0 - 1 <= 200000 * 2^40).
  { pose proof HN as [_ [_ [HK _]]].
    replace (i-1+1) with i in HK by lia.
    pose proof (CopyPasteStates_length_at__backtrack_transitions text ops states_2 i HS ltac:(lia)) as HM.
    assert (HP : 2^i <= 2^40) by (apply Z.pow_le_mono_r; lia).
    pose proof (Zlength_nonneg text). nia. }
  Exists out_2 before_data_2 states_2.
  unfold store_string.
  split_pure_spatial; [repeat progress cancel |].
  split_pures; dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HC : c_pre = Zlength ops) by assumption.
  assert (HS : CopyPasteStates text ops states_2) by assumption.
  assert (HB : BacktrackedPosition states_2 (Znth z queries_data 0) i k) by assumption.
  assert (HL : StateLengthsPrefix states_2 c_pre before_data_2) by assumption.
  destruct HL as [_ HL]. specialize (HL i ltac:(lia)).
  pose proof (backtrack_left__backtrack_transitions text ops states_2 (Znth z queries_data 0) i k HS HB ltac:(lia) ltac:(replace (i-0) with i in * by lia; lia)) as HN.
  Exists out_2 before_data_2 states_2.
  unfold store_string.
  split_pure_spatial; [repeat progress cancel |].
  split_pures; dump_pre_spatial; try assumption; try lia.
Qed. 

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (out_2 ++ (Znth (k - 1) (c_string text) 0 :: nil)) before_data_2 states_2.
  split_pure_spatial.
  - unfold store_string.
    cancel (CharArray.seg answers_pre 0 (z + 1)
      (out_2 ++ (Znth (k - 1) (c_string text) 0 :: nil))).
    cancel (CharArray.undef_seg answers_pre (z + 1) q_pre).
    cancel (CharArray.full s_pre (string_length text + 1) (c_string text)).
    cancel (Int64Array.full l_pre c_pre lefts).
    cancel (Int64Array.full r_pre c_pre rights).
    cancel (Int64Array.full queries_pre q_pre queries_data).
    cancel (Int64Array.seg (&( "before" )) 0 c_pre before_data_2).
    cancel (Int64Array.undef_seg (&( "before" )) c_pre 40).
  - split_pures; dump_pre_spatial; try lia; try assumption; try auto.
    unfold AnswerPrefix in PreH20 |- *.
    destruct PreH20 as [Hzq [Hout Hprefix]].
    split; [lia |].
    split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + intros j Hj.
      destruct (Z_lt_ge_dec j z) as [Hjz | Hjz].
      * rewrite app_Znth1 by lia.
        apply Hprefix; lia.
      * assert (j = z) by lia; subst j.
        rewrite app_Znth2 by lia.
        rewrite Hout.
        replace (z - z) with 0 by lia.
        rewrite Znth0_cons.
        rewrite c_string_Znth_inside by (unfold string_length; lia).
        unfold FinalCharacter in PreH23.
        exact PreH23.
Qed. 

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hz : z = q_pre) by lia.
  subst z.
  Exists out_2 states_2.
  split_pure_spatial.
  - rewrite (CharArray.undef_seg_empty answers_pre q_pre).
    sep_apply_l_atomic
      (CharArray.seg_to_full answers_pre 0 q_pre out_2).
    replace (answers_pre + 0 * sizeof(CHAR)) with answers_pre by lia.
    replace (q_pre - 0) with q_pre by lia.
    sep_apply_l_atomic
      (Int64Array.seg_to_undef_seg (&( "before" )) 0 c_pre before_data).
    sep_apply_l_atomic
      (Int64Array.undef_seg_merge_to_undef_full (&( "before" )) 0 c_pre 40).
    + dump_pre_spatial. lia.
    + replace (&( "before" ) + 0 * sizeof(INT64)) with (&( "before" )) by lia.
      replace (40 - 0) with 40 by lia.
      cancel (store_string s_pre text).
      cancel (Int64Array.full l_pre c_pre lefts).
      cancel (Int64Array.full r_pre c_pre rights).
      cancel (Int64Array.full queries_pre q_pre queries_data).
      cancel (CharArray.full answers_pre q_pre out_2).
      cancel (Int64Array.undef_full (&( "before" )) 40).
  - split_pures.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial. exact PreH17.
    + dump_pre_spatial.
      unfold AnswerPrefix in PreH20.
      unfold Spec.
      destruct PreH20 as [_ [Hout_len Hout]].
      apply (Forall2_nth_iff Z Z
        (fun query answer =>
           answer = Znth (query - 1) (fold_left CopyPasteStep ops text) 0)
        queries_data out_2 0 0).
      split.
      * rewrite PreH12 in Hout_len.
        rewrite !Zlength_correct in Hout_len.
        lia.
      * intros n Hn.
        specialize (Hout (Z.of_nat n)).
        unfold Znth in *.
        rewrite !Nat2Z.id in Hout.
        apply Hout.
        rewrite PreH12, Zlength_correct.
        lia.
Qed. 

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold valid_string, all_ascii, no_inner_nul.
  split; intros i Hi; destruct (PreH12 i Hi); lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_2 : solver_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold string_length.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_2.
Qed. 

