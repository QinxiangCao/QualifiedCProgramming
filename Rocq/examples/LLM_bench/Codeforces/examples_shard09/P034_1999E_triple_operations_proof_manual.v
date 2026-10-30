From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P034_1999E_triple_operations_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P034_1999E_triple_operations_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P034_1999E_triple_operations_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold TripleTablesPrefix in PreH13.
  destruct PreH13 as
      (Hf_len & Hp_len & Hn & Hf0 & Hp0 & Hf_bound & Hp_bound & Hf_rec & Hp_rec).
  pose proof (Hf_bound (i ÷ 3) (conj PreH1 PreH2)) as Hf_i.
  destruct Hf_i as [Hf_nonneg Hf_upper].
  replace (i ÷ 3 - 0) with (i ÷ 3) by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold TripleTablesPrefix in PreH13.
  destruct PreH13 as
      (Hf_len & Hp_len & Hn & Hf0 & Hp0 & Hf_bound & Hp_bound & Hf_rec & Hp_rec).
  pose proof (Hf_bound (i ÷ 3) (conj PreH1 PreH2)) as Hf_i.
  destruct Hf_i as [Hf_nonneg Hf_upper].
  replace (i ÷ 3 - 0) with (i ÷ 3) by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold TripleTablesPrefix in PreH13.
  destruct PreH13 as
      (Hf_len & Hp_len & Hn & Hf0 & Hp0 & Hf_bound & Hp_bound & Hf_rec & Hp_rec).
  pose proof (Hf_bound (i ÷ 3) (conj PreH1 PreH2)) as Hf_i.
  pose proof (Hp_bound (i - 1) ltac:(lia)) as Hp_i.
  destruct Hf_i as [Hf_nonneg Hf_upper].
  destruct Hp_i as [Hp_nonneg Hp_upper].
  assert (Hlast :
      Znth i (app fvs (cons (Znth (i ÷ 3) fvs 0 + 1) nil)) 0 =
      Znth (i ÷ 3) fvs 0 + 1).
  { rewrite <- Hf_len. apply Znth_app_last__table_numeric_safety. }
  replace (i ÷ 3 - 0) with (i ÷ 3) in * by lia.
  replace (i - 1 - 0) with (i - 1) by lia.
  replace (i - 0) with i by lia.
  rewrite Hlast.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold TripleTablesPrefix in PreH13.
  destruct PreH13 as
      (Hf_len & Hp_len & Hn & Hf0 & Hp0 & Hf_bound & Hp_bound & Hf_rec & Hp_rec).
  pose proof (Hf_bound (i ÷ 3) (conj PreH1 PreH2)) as Hf_i.
  pose proof (Hp_bound (i - 1) ltac:(lia)) as Hp_i.
  destruct Hf_i as [Hf_nonneg Hf_upper].
  destruct Hp_i as [Hp_nonneg Hp_upper].
  assert (Hlast :
      Znth i (app fvs (cons (Znth (i ÷ 3) fvs 0 + 1) nil)) 0 =
      Znth (i ÷ 3) fvs 0 + 1).
  { rewrite <- Hf_len. apply Znth_app_last__table_numeric_safety. }
  replace (i ÷ 3 - 0) with (i ÷ 3) in * by lia.
  replace (i - 1 - 0) with (i - 1) by lia.
  replace (i - 0) with i by lia.
  rewrite Hlast.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH6 i ltac:(lia)) as Hquery.
  destruct Hquery as [[Hl Hlr] Hr].
  unfold TripleTablesPrefix in PreH9.
  destruct PreH9 as (_ & _ & _ & _ & _ & Hfvs & Hpres & _ & _).
  pose proof (Hfvs (Znth i ls 0) ltac:(lia)) as Hfvsl.
  pose proof (Hpres (Znth i ls 0) ltac:(lia)) as Hpresl.
  pose proof (Hpres (Znth i rs 0) ltac:(lia)) as Hpresr.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH6 i ltac:(lia)) as Hquery.
  destruct Hquery as [[Hl Hlr] Hr].
  unfold TripleTablesPrefix in PreH9.
  destruct PreH9 as (_ & _ & _ & _ & _ & Hfvs & Hpres & _ & _).
  pose proof (Hfvs (Znth i ls 0) ltac:(lia)) as Hfvsl.
  pose proof (Hpres (Znth i ls 0) ltac:(lia)) as Hpresl.
  pose proof (Hpres (Znth i rs 0) ltac:(lia)) as Hpresr.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH6 i ltac:(lia)) as Hquery.
  destruct Hquery as [[Hl Hlr] Hr].
  unfold TripleTablesPrefix in PreH9.
  destruct PreH9 as (_ & _ & _ & _ & _ & Hfvs & Hpres & _ & _).
  pose proof (Hpres (Znth i ls 0) ltac:(lia)) as Hpresl.
  pose proof (Hpres (Znth i rs 0) ltac:(lia)) as Hpresr.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_2 : solver_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH6 i ltac:(lia)) as Hquery.
  destruct Hquery as [[Hl Hlr] Hr].
  unfold TripleTablesPrefix in PreH9.
  destruct PreH9 as (_ & _ & _ & _ & _ & Hfvs & Hpres & _ & _).
  pose proof (Hpres (Znth i ls 0) ltac:(lia)) as Hpresl.
  pose proof (Hpres (Znth i rs 0) ltac:(lia)) as Hpresr.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH6 i ltac:(lia)) as Hquery.
  destruct Hquery as [[Hl Hlr] Hr].
  unfold TripleTablesPrefix in PreH9.
  destruct PreH9 as (_ & _ & _ & _ & _ & Hfvs & Hpres & _ & _).
  pose proof (Hfvs (Znth i ls 0) ltac:(lia)) as Hfvsl.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH6 i ltac:(lia)) as Hquery.
  destruct Hquery as [[Hl Hlr] Hr].
  unfold TripleTablesPrefix in PreH9.
  destruct PreH9 as (_ & _ & _ & _ & _ & Hfvs & Hpres & _ & _).
  pose proof (Hfvs (Znth i ls 0) ltac:(lia)) as Hfvsl.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (0 :: nil).
  Exists (0 :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic (Int64Array.seg_single (&( "pre" )) 0 0).
    sep_apply_l_atomic (IntArray.seg_single (&( "fv" )) 0 0).
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full l_pre q_pre ls).
    cancel (IntArray.full r_pre q_pre rs).
    cancel (Int64Array.undef_full out_pre q_pre).
    cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact triple_tables_prefix_one__table_invariants.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_lt; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  replace (i / 3 - 0) with (i / 3) by lia.
  replace (i - 1 - 0) with (i - 1) by lia.
  replace (i - 0) with i by lia.
  eapply triple_tables_prefix_snoc__table_invariants; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = 200005) by lia.
  subst i.
  pose proof
    (triple_tables_prefix_full_bridge__table_invariants
       fvs_2 pres_2 PreH9) as Hbridge.
  pose proof
    (TripleTablesBridge_closed_form fvs_2 pres_2 Hbridge) as Hclosed.
  Exists (@nil Z).
  Exists fvs_2 pres_2.
  split_pure_spatial.
  - rewrite (IntArray.seg_shape_empty (&( "fv" )) 200005).
    rewrite (Int64Array.seg_shape_empty (&( "pre" )) 200005).
    sep_apply_l_atomic
      (IntArray.seg_to_full (&( "fv" )) 0 200005 fvs_2).
    sep_apply_l_atomic
      (Int64Array.seg_to_full (&( "pre" )) 0 200005 pres_2).
    sep_apply_l_atomic
      (Int64Array.undef_full_to_undef_seg out_pre q_pre).
    replace (&( "fv" ) + 0 * sizeof(INT)) with (&( "fv" )) by lia.
    replace (&( "pre" ) + 0 * sizeof(INT64)) with (&( "pre" )) by lia.
    replace (200005 - 0) with 200005 by lia.
    cancel (IntArray.full l_pre q_pre ls).
    cancel (IntArray.full r_pre q_pre rs).
    cancel (Int64Array.undef_seg out_pre 0 q_pre).
    cancel (IntArray.full (&( "fv" )) 200005 fvs_2).
    cancel (Int64Array.full (&( "pre" )) 200005 pres_2).
    rewrite (Int64Array.seg_empty out_pre 0 0).
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    unfold TripleOutputsPrefix.
    split.
    + reflexivity.
    + intros j Hj. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply triple_outputs_prefix_snoc__output_transition.
  - exact PreH12.
  - apply PreH11.
    apply PreH6.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i_2 = q_pre) by lia.
  subst i_2.
  unfold TripleOutputsPrefix in PreH12.
  destruct PreH12 as [Houts_len Houts_spec].
  Exists fvs_2 pres_2 outs_2.
  split_pure_spatial.
  - rewrite (Int64Array.undef_seg_empty out_pre q_pre).
    sep_apply_l_atomic
      (Int64Array.seg_to_full out_pre 0 q_pre outs_2).
    replace (out_pre + 0 * sizeof(INT64)) with out_pre by lia.
    replace (q_pre - 0) with q_pre by lia.
    cancel (IntArray.full l_pre q_pre ls).
    cancel (IntArray.full r_pre q_pre rs).
    cancel (Int64Array.full out_pre q_pre outs_2).
    cancel (IntArray.full ( &( "fv" ) ) 200005 fvs_2).
    cancel (Int64Array.full ( &( "pre" ) ) 200005 pres_2).
  - split_pures.
    + dump_pre_spatial. exact Houts_len.
    + dump_pre_spatial. exact Houts_spec.
    + dump_pre_spatial. exact PreH10.
Qed.
