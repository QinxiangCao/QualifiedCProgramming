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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P061_2042C_competitive_fishing_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P061_2042C_competitive_fishing_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P061_2042C_competitive_fishing_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (@nil Z).
  replace (n_pre - 2 + 1) with (n_pre - 1) by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval (n_pre - 1)).
    rewrite IntArray.seg_empty.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + intros j Hj. apply PreH7. lia.
    + rewrite Zlength_nil. lia.
    + unfold GainBuildState.
      rewrite PreH8.
      split.
      * symmetry. apply Zsublist_nil. lia.
      * unfold SuffixGain.
        pose proof (sublist_single 48 (Zlength f - 1) f ltac:(lia)) as Hsingle.
        replace (Zlength f - 1 + 1) with (Zlength f) in Hsingle by lia.
        rewrite Hsingle.
        simpl.
        unfold FishingValue.
        assert (Hlast : Znth (Zlength f - 1) f 48 = 49).
        { rewrite <- PreH8.
          rewrite app_Znth1 in PreH1 by lia.
          rewrite (Znth_indep f (n_pre - 1) 48 0) by lia.
          exact PreH1. }
        rewrite Hlast. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (@nil Z).
  replace (n_pre - 2 + 1) with (n_pre - 1) by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval (n_pre - 1)).
    rewrite IntArray.seg_empty.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + intros j Hj. apply PreH7. lia.
    + rewrite Zlength_nil. lia.
    + unfold GainBuildState.
      rewrite PreH8.
      split.
      * symmetry. apply Zsublist_nil. lia.
      * unfold SuffixGain.
        pose proof (sublist_single 48 (Zlength f - 1) f ltac:(lia)) as Hsingle.
        replace (Zlength f - 1 + 1) with (Zlength f) in Hsingle by lia.
        rewrite Hsingle.
        simpl.
        unfold FishingValue.
        rewrite PreH8 in PreH1.
        rewrite app_Znth1 in PreH1 by lia.
        pose proof (PreH7 (Zlength f - 1) ltac:(lia)) as [Hzero | Hone].
        { rewrite (Znth_indep f (Zlength f - 1) 48 0) by lia.
          rewrite Hzero. reflexivity. }
        { exfalso. apply PreH1. exact Hone. }
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (sum :: built_gains_2).
  replace (i - 1 + 1) with i by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_single gain i sum).
    sep_apply_l_atomic
      (IntArray.seg_merge_to_seg gain i (i + 1) (n_pre - 1)
        (sum :: nil) built_gains_2 ltac:(lia)).
    simpl.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + assert (Hchars : forall j, 0 <= j < Zlength f ->
        Znth j f 0 = 48 \/ Znth j f 0 = 49).
      { intros j Hj. apply PreH8. lia. }
      unfold GainBuildState in PreH14.
      destruct PreH14 as [_ Hsum].
      pose proof (suffix_gain_span_bounds__gain_construction f (i + 1)
        ltac:(lia) Hchars) as Hspan.
      lia.
    + rewrite Zlength_cons, PreH13. lia.
    + assert (Hchar : Znth i f 48 = 49).
      { rewrite app_Znth1 in PreH1 by (rewrite PreH7; lia).
        rewrite (Znth_indep f i 48 0) by (rewrite PreH7; lia).
        exact PreH1. }
      replace (sum + 1) with
        (sum + FishingValue (Znth i f 48)) by
        (unfold FishingValue; rewrite Hchar; reflexivity).
      apply gain_build_state_step__gain_construction; [lia | exact PreH14].
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (sum :: built_gains_2).
  replace (i - 1 + 1) with i by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_single gain i sum).
    sep_apply_l_atomic
      (IntArray.seg_merge_to_seg gain i (i + 1) (n_pre - 1)
        (sum :: nil) built_gains_2 ltac:(lia)).
    simpl.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + assert (Hchars : forall j, 0 <= j < Zlength f ->
        Znth j f 0 = 48 \/ Znth j f 0 = 49).
      { intros j Hj. apply PreH8. lia. }
      unfold GainBuildState in PreH14.
      destruct PreH14 as [_ Hsum].
      pose proof (suffix_gain_span_bounds__gain_construction f (i + 1)
        ltac:(lia) Hchars) as Hspan.
      lia.
    + rewrite Zlength_cons, PreH13. lia.
    + rewrite app_Znth1 in PreH1 by (rewrite PreH7; lia).
      pose proof (PreH8 i ltac:(lia)) as [Hzero | Hone].
      2: { exfalso. apply PreH1. exact Hone. }
      assert (Hchar : Znth i f 48 = 48).
      { rewrite (Znth_indep f i 48 0) by (rewrite PreH7; lia).
        exact Hzero. }
      replace (sum + -1) with
        (sum + FishingValue (Znth i f 48)) by
        (unfold FishingValue; rewrite Hchar; reflexivity).
      apply gain_build_state_step__gain_construction; [lia | exact PreH14].
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = -1) by lia. subst i.
  replace (-1 + 1) with 0 in * by lia.
  Exists built_gains.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic (IntArray.seg_to_full gain 0 (n_pre - 1) built_gains).
    replace (gain + 0 * sizeof(INT)) with gain by lia.
    replace (n_pre - 1 - 0) with (n_pre - 1) by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + assert (Hchars : forall j, 0 <= j < Zlength f ->
          Znth j f 0 = 48 \/ Znth j f 0 = 49).
      { intros j Hj. apply PreH7. lia. }
      assert (Hbuilt : built_gains = FishingGains f).
      { apply (gain_build_state_zero__gain_construction f built_gains sum);
          [lia | exact PreH13]. }
      rewrite Hbuilt.
      intros j Hj.
      rewrite <- PreH6.
      apply suffix_gain_bounds__gain_construction; [exact Hchars | lia].
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PreparedGains.
  split.
  - assert (Hcanonical : canonical_gains = FishingGains f).
    { apply (gain_build_state_zero__gain_construction f canonical_gains sum);
        [lia | exact PreH14]. }
    rewrite <- Hcanonical. exact PreH1.
  - exact PreH2.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (permutation_preserves_Znth_bounds__gain_construction
    canonical_gains sorted (-n_pre) n_pre PreH1).
  intros j Hj. apply PreH11. lia.
  rewrite PreH3. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GainSearchState.
  split.
  - reflexivity.
  - intros count Hcount.
    replace count with 0 by lia.
    simpl.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH8.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GainSearchState in *.
  destruct PreH19 as [Hcur Hbelow].
  split.
  - rewrite (fold_sublist_snoc__gain_search sorted_gains_2 i) by lia.
    lia.
  - intros count Hcount.
    destruct (Z_le_gt_dec count i) as [Hle | Hgt].
    + apply Hbelow.
      lia.
    + replace count with (i + 1) by lia.
      rewrite (fold_sublist_snoc__gain_search sorted_gains_2 i) by lia.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GainSearchState in PreH19.
  destruct PreH19 as [Hcur _].
  rewrite Hcur.
  rewrite <- (fold_sublist_snoc__gain_search sorted_gains_2 i) by lia.
  apply (bounded_prefix_sum_lower__gain_search
    sorted_gains_2 n_pre (i + 1)); try lia.
  intros j Hj.
  specialize (PreH17 j Hj).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply Z.ge_le in PreH1.
  assert (Hiend : i = Zlength sorted_gains_2) by lia.
  assert (Hresult :
    FishingSearchResult k_pre f sorted_gains_2 ans).
  { eapply gain_search_terminal_result__final_result;
      [exact PreH18|exact Hiend|exact PreH10]. }
  assert (Hspec : Spec k_pre f ans).
  { eapply fishing_search_result_implies_spec__final_result;
      [lia|exact PreH17|exact Hresult]. }
  Exists sorted_gains_2.
  rewrite PreH15.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (n_pre + 1) (f ++ 0 :: nil)).
    cancel (IntArray.full gain (n_pre - 1) sorted_gains_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hflen : 1 <= Zlength f) by lia.
  assert (Hinext : 0 <= i < Zlength sorted_gains) by lia.
  assert (Hresult :
    FishingSearchResult k_pre f sorted_gains (i + 2)).
  { eapply gain_search_success_result__final_result;
      [exact Hflen|exact PreH18|exact Hinext|exact PreH1|exact PreH19]. }
  assert (Hspec : Spec k_pre f (i + 2)).
  { eapply fishing_search_result_implies_spec__final_result;
      [exact Hflen|exact PreH18|exact Hresult]. }
  specialize (PreH17 i ltac:(lia)) as Hith.
  destruct Hith as [Hithlo Hithhi].
  assert (Hpointupper : forall j,
    0 <= j < Zlength sorted_gains -> Znth j sorted_gains 0 <= n_pre).
  { intros j Hj. apply (proj2 (PreH17 j ltac:(lia))). }
  pose proof (gain_search_next_sum_upper__final_result
    k_pre sorted_gains i cur n_pre Hinext Hpointupper PreH19) as Hsumupper.
  assert (Hnextupper :
    cur + Znth i sorted_gains 0 <= 40000000000) by nia.
  Exists sorted_gains.
  rewrite PreH16.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (n_pre + 1) (f ++ 0 :: nil)).
    cancel (IntArray.full gain (n_pre - 1) sorted_gains).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.
