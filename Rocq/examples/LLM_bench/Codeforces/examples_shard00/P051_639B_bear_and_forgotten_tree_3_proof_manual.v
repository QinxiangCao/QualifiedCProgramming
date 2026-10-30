From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P051_639B_bear_and_forgotten_tree_3_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P051_639B_bear_and_forgotten_tree_3_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P051_639B_bear_and_forgotten_tree_3_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_1_split_goal_1 : solver_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Feasible.
  split.
  - lia.
  - right. lia.
Qed.

Lemma proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_2_split_goal_1 : solver_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Feasible.
  split.
  - lia.
  - left. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros k Hk; apply PreH15; exact Hk).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_2 : solver_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_1 : solver_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_1 : solver_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_2 : solver_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_2 : solver_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcount : count = n_pre - 1) by lia.
  subst count.
  assert (Hpre : Pre n_pre d_pre h_pre).
  { unfold Pre. lia. }
  match goal with
  | Hfeas : Feasible n_pre d_pre h_pre,
    Hus : Zlength eu_data_2 = _,
    Hvs : Zlength ev_data_2 = _,
    Hcanon : forall k : Z, _ ->
      CanonicalEndpoints d_pre h_pre k
        (Znth k eu_data_2 0) (Znth k ev_data_2 0) |- _ =>
      assert (Hus' : Zlength eu_data_2 = n_pre - 1) by lia;
      assert (Hvs' : Zlength ev_data_2 = n_pre - 1) by lia;
      assert (Hcanon' : forall k, 0 <= k < n_pre - 1 ->
        CanonicalEndpoints d_pre h_pre k
          (Znth k eu_data_2 0) (Znth k ev_data_2 0))
        by (intros k Hk; apply Hcanon; lia);
      pose proof (canonical_endpoint_arrays_realize_spec__constructive_returns
        n_pre d_pre h_pre eu_data_2 ev_data_2 Hpre Hfeas
        Hus' Hvs' Hcanon') as Hcert
  end.
  destruct Hcert as [Hspec [Hedges Hproj]].
  Exists ev_data_2 eu_data_2 (combine eu_data_2 ev_data_2).
  rewrite Hedges.
  split_pure_spatial.
  - rewrite Hcount.
    rewrite !IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full eu_pre 0 (n_pre - 1) eu_data_2).
    replace (eu_pre + 0 * sizeof (INT)) with eu_pre by lia.
    replace (n_pre - 1 - 0) with (n_pre - 1) by lia.
    sep_apply (IntArray.seg_to_full ev_pre 0 (n_pre - 1) ev_data_2).
    replace (ev_pre + 0 * sizeof (INT)) with ev_pre by lia.
    replace (n_pre - 1 - 0) with (n_pre - 1) by lia.
    cancel (IntArray.full eu_pre (n_pre - 1) eu_data_2).
    cancel (IntArray.full ev_pre (n_pre - 1) ev_data_2).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hcount.
    + dump_pre_spatial. intros i Hi.
      rewrite (Znth_indep (combine eu_data_2 ev_data_2) i
        __default__Prod_Z_Z (0, 0)) by (rewrite Hedges; exact Hi).
      apply Hproj. rewrite Hedges. exact Hi.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcount : count = n_pre - 1) by lia.
  subst count.
  assert (Hpre : Pre n_pre d_pre h_pre).
  { unfold Pre. lia. }
  match goal with
  | Hfeas : Feasible n_pre d_pre h_pre,
    Hus : Zlength eu_data_2 = _,
    Hvs : Zlength ev_data_2 = _,
    Hcanon : forall k : Z, _ ->
      CanonicalEndpoints d_pre h_pre k
        (Znth k eu_data_2 0) (Znth k ev_data_2 0) |- _ =>
      assert (Hus' : Zlength eu_data_2 = n_pre - 1) by lia;
      assert (Hvs' : Zlength ev_data_2 = n_pre - 1) by lia;
      assert (Hcanon' : forall k, 0 <= k < n_pre - 1 ->
        CanonicalEndpoints d_pre h_pre k
          (Znth k eu_data_2 0) (Znth k ev_data_2 0))
        by (intros k Hk; apply Hcanon; lia);
      pose proof (canonical_endpoint_arrays_realize_spec__constructive_returns
        n_pre d_pre h_pre eu_data_2 ev_data_2 Hpre Hfeas
        Hus' Hvs' Hcanon') as Hcert
  end.
  destruct Hcert as [Hspec [Hedges Hproj]].
  Exists ev_data_2 eu_data_2 (combine eu_data_2 ev_data_2).
  rewrite Hedges.
  split_pure_spatial.
  - rewrite Hcount.
    rewrite !IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full eu_pre 0 (n_pre - 1) eu_data_2).
    replace (eu_pre + 0 * sizeof (INT)) with eu_pre by lia.
    replace (n_pre - 1 - 0) with (n_pre - 1) by lia.
    sep_apply (IntArray.seg_to_full ev_pre 0 (n_pre - 1) ev_data_2).
    replace (ev_pre + 0 * sizeof (INT)) with ev_pre by lia.
    replace (n_pre - 1 - 0) with (n_pre - 1) by lia.
    cancel (IntArray.full eu_pre (n_pre - 1) eu_data_2).
    cancel (IntArray.full ev_pre (n_pre - 1) ev_data_2).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hcount.
    + dump_pre_spatial. intros i Hi.
      rewrite (Znth_indep (combine eu_data_2 ev_data_2) i
        __default__Prod_Z_Z (0, 0)) by (rewrite Hedges; exact Hi).
      apply Hproj. rewrite Hedges. exact Hi.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      unfold Spec.
      right.
      split; [reflexivity|].
      intros e Htree.
      pose proof
        (valid_remembered_tree_diameter_le_twice_height
          n_pre d_pre h_pre e Htree) as Hbound.
      lia.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      unfold Spec.
      right.
      split; [reflexivity|].
      intros e Htree.
      pose proof
        (valid_remembered_tree_diameter_one_size_bound__infeasible_returns
          n_pre h_pre e ltac:(rewrite <- PreH2; exact Htree)) as Hnle.
      lia.
Qed.
