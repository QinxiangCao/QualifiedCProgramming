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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P031_1194C_from_s_to_t_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P031_1194C_from_s_to_t_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P031_1194C_from_s_to_t_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_22_split_goal_1 : solver_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (count_state_cell_bounds__count_init_safety
       source pool target i 0 0 counts (Znth i source 0 - 97)
       PreH23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcount.
  rewrite PreH3.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_2 : solver_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH24 (Znth i source 0 - 97) ltac:(lia)) as Hcount.
  rewrite PreH3.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_1 : solver_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (count_state_cell_bounds__count_init_safety
       source pool target (Zlength source) i 0 counts (Znth i pool 0 - 97)
       PreH23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcount.
  rewrite PreH3.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_2 : solver_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH24 (Znth i pool 0 - 97) ltac:(lia)) as Hcount.
  rewrite PreH3.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_35_split_goal_1 : solver_safety_wit_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (count_state_cell_bounds__count_init_safety
       source pool target (Zlength source) (Zlength pool) i counts
       (Znth i target 0 - 97)
       PreH23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcount.
  rewrite PreH3.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_35_split_goal_2 : solver_safety_wit_35_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH24 (Znth i target 0 - 97) ltac:(lia)) as Hcount.
  rewrite PreH3.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_35_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_35_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NonnegativeCounts.
  intros c Hc.
  unfold repeat_Z.
  rewrite Znth_repeat.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CountState.
  split.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    lia.
  - intros c Hc.
    unfold LetterCount.
    repeat rewrite Zsublist_nil by lia.
    simpl.
    unfold repeat_Z.
    rewrite Znth_repeat.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply greedy_prefix_zero__count_init_safety.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply app_Znth1.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_5 : solver_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply app_Znth1.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_6 : solver_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_7 : solver_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH8.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_8 : solver_entail_wit_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_7.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_8.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchars : Znth i source 0 = Znth j target 0).
  { rewrite <- PreH25, <- PreH21. exact PreH1. }
  pose proof
    (greedy_prefix_match_equal_step__greedy_match
       source target j i ltac:(lia) ltac:(lia) Hchars PreH28) as Hgreedy.
  destruct (Z.eq_dec (j + 1) (Zlength target)) as [Hjt | Hjt].
  - destruct (Z.eq_dec (i + 1) (Zlength source)) as [His | His].
    + Left. Left. Right. Exists counts_2.
      split_pure_spatial.
      * cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
        cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
        cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
        cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
        cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
        cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
        cancel (IntArray.full (&( "cnt" )) 26 counts_2).
      * split_pures; dump_pre_spatial;
          try assumption; try lia; try eauto;
          try (rewrite Hjt; rewrite app_Znth2 by lia;
               rewrite Z.sub_diag; apply Znth0_cons);
          try (rewrite His; rewrite app_Znth2 by lia;
               rewrite Z.sub_diag; apply Znth0_cons).
    + pose proof (PreH13 (i + 1) ltac:(lia)) as Hsource_next.
      destruct Hsource_next as (Hsource_lo & Hsource_hi).
      Left. Left. Left. Exists counts_2.
      split_pure_spatial.
      * cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
        cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
        cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
        cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
        cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
        cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
        cancel (IntArray.full (&( "cnt" )) 26 counts_2).
      * split_pures; dump_pre_spatial;
          try assumption; try lia; try eauto;
          try (rewrite app_Znth1 by lia; reflexivity);
          try (rewrite Hjt; rewrite app_Znth2 by lia;
               rewrite Z.sub_diag; apply Znth0_cons).
  - destruct (Z.eq_dec (i + 1) (Zlength source)) as [His | His].
    + pose proof (PreH14 (j + 1) ltac:(lia)) as Htarget_next.
      destruct Htarget_next as (Htarget_lo & Htarget_hi).
      Right. Exists counts_2.
      split_pure_spatial.
      * cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
        cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
        cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
        cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
        cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
        cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
        cancel (IntArray.full (&( "cnt" )) 26 counts_2).
      * split_pures; dump_pre_spatial;
          try assumption; try lia; try eauto;
          try (rewrite app_Znth1 by lia; reflexivity);
          try (rewrite His; rewrite app_Znth2 by lia;
               rewrite Z.sub_diag; apply Znth0_cons).
    + pose proof (PreH13 (i + 1) ltac:(lia)) as Hsource_next.
      pose proof (PreH14 (j + 1) ltac:(lia)) as Htarget_next.
      destruct Hsource_next as (Hsource_lo & Hsource_hi).
      destruct Htarget_next as (Htarget_lo & Htarget_hi).
      Left. Right. Exists counts_2.
      split_pure_spatial.
      * cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
        cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
        cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
        cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
        cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
        cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
        cancel (IntArray.full (&( "cnt" )) 26 counts_2).
      * split_pures; dump_pre_spatial;
          try assumption; try lia; try eauto;
          try (rewrite app_Znth1 by lia; reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchars : Znth i source 0 <> Znth j target 0).
  { rewrite <- PreH25, <- PreH21. exact PreH1. }
  pose proof
    (greedy_prefix_match_skip_step__greedy_match
       source target j i ltac:(lia) ltac:(lia) Hchars PreH28) as Hgreedy.
  destruct (Z.eq_dec (j + 1) (Zlength target)) as [Hjt | Hjt].
  - Left. Exists counts_2.
    split_pure_spatial.
    + cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
      cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
      cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
      cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
      cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
      cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
      cancel (IntArray.full (&( "cnt" )) 26 counts_2).
    + split_pures; dump_pre_spatial;
        try assumption; try lia; try eauto;
        try (rewrite Hjt; rewrite app_Znth2 by lia;
             rewrite Z.sub_diag; apply Znth0_cons).
  - pose proof (PreH14 (j + 1) ltac:(lia)) as Htarget_next.
    destruct Htarget_next as (Htarget_lo & Htarget_hi).
    Right. Exists counts_2.
    split_pure_spatial.
    + cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
      cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
      cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
      cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
      cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
      cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
      cancel (IntArray.full (&( "cnt" )) 26 counts_2).
    + split_pures; dump_pre_spatial;
        try assumption; try lia; try eauto;
        try (rewrite app_Znth1 by lia; reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (greedy_prefix_match_target_step_complete__greedy_match
       source target j i PreH21 ltac:(lia) PreH23) as Hgreedy.
  destruct (Z.eq_dec (j + 1) (Zlength target)) as [Hjt | Hjt].
  - Left. Exists counts_2.
    split_pure_spatial.
    + cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
      cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
      cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
      cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
      cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
      cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
      cancel (IntArray.full (&( "cnt" )) 26 counts_2).
    + split_pures; dump_pre_spatial;
        try assumption; try lia; try eauto;
        try (rewrite Hjt; rewrite app_Znth2 by lia;
             rewrite Z.sub_diag; apply Znth0_cons).
  - pose proof (PreH11 (j + 1) ltac:(lia)) as Htarget_next.
    destruct Htarget_next as (Htarget_lo & Htarget_hi).
    Right. Exists counts_2.
    split_pure_spatial.
    + cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
      cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
      cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
      cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
      cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
      cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
      cancel (IntArray.full (&( "cnt" )) 26 counts_2).
    + split_pures; dump_pre_spatial;
        try assumption; try lia; try eauto;
        try (rewrite app_Znth1 by lia; reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_1 : solver_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (greedy_prefix_match_complete_cases__greedy_match
       source target j i PreH23 PreH17) as (_ & Hno).
  apply Hno. exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (greedy_prefix_match_complete_cases__greedy_match
       source target j i PreH21 PreH17) as (Hyes & _).
  apply Hyes. exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH12. exact H.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_3 : solver_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11. exact H.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_4 : solver_entail_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH10. exact H.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Znth_app_left__source_pool_updates by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_3 : solver_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH8.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_4 : solver_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_16 : solver_entail_wit_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH3 in *.
  pose proof (proj1 PreH23) as Hcounts_len.
  pose proof
    (count_state_source_step__source_pool_updates
      source pool target counts_2 i ltac:(lia) ltac:(lia) PreH23)
    as Hcount_step.
  pose proof
    (nonnegative_counts_increment__source_pool_updates
      counts_2 (Znth i source 0 - 97)
      Hcounts_len ltac:(lia) PreH24)
    as Hnonnegative_step.
  destruct (Z.eq_dec (i + 1) (Zlength source)) as [Hend | Hcontinue].
  - Left.
    Exists (replace_Znth (Znth i source 0 - 97)
      (Znth (Znth i source 0 - 97) counts_2 0 + 1) counts_2).
    split_pure_spatial.
    + cancel.
      cancel.
      cancel.
      cancel.
      cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: try lia.
      rewrite Hend.
      rewrite Znth_app_last__source_pool_updates.
      reflexivity.
  - Right.
    Exists (replace_Znth (Znth i source 0 - 97)
      (Znth (Znth i source 0 - 97) counts_2 0 + 1) counts_2).
    split_pure_spatial.
    + cancel.
      cancel.
      cancel.
      cancel.
      cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: try lia.
      all: try (rewrite Znth_app_left__source_pool_updates by lia; reflexivity).
      all: apply PreH13; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_1 : solver_entail_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Znth_app_left__source_pool_updates by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_2 : solver_entail_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_3 : solver_entail_wit_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_4 : solver_entail_wit_17_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_17 : solver_entail_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_21 : solver_entail_wit_21.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH3 in *.
  pose proof (proj1 PreH23) as Hcounts_len.
  pose proof
    (count_state_pool_step__source_pool_updates
      source pool target counts_2 (Zlength source) i
      ltac:(lia) ltac:(lia) PreH23)
    as Hcount_step.
  pose proof
    (nonnegative_counts_increment__source_pool_updates
      counts_2 (Znth i pool 0 - 97)
      Hcounts_len ltac:(lia) PreH24)
    as Hnonnegative_step.
  destruct (Z.eq_dec (i + 1) (Zlength pool)) as [Hend | Hcontinue].
  - Left.
    Exists (replace_Znth (Znth i pool 0 - 97)
      (Znth (Znth i pool 0 - 97) counts_2 0 + 1) counts_2).
    split_pure_spatial.
    + cancel.
      cancel.
      cancel.
      cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: try lia.
      rewrite Hend.
      rewrite Znth_app_last__source_pool_updates.
      reflexivity.
  - Right.
    Exists (replace_Znth (Znth i pool 0 - 97)
      (Znth (Znth i pool 0 - 97) counts_2 0 + 1) counts_2).
    split_pure_spatial.
    + cancel.
      cancel.
      cancel.
      cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: try lia.
      all: try (rewrite Znth_app_left__source_pool_updates by lia; reflexivity).
      all: apply PreH15; lia.
Qed.

Lemma proof_of_solver_entail_wit_22_split_goal_1 : solver_entail_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply Znth_app_left__target_shortage.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_22_split_goal_2 : solver_entail_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH11 k_3 H).
Qed.

Lemma proof_of_solver_entail_wit_22_split_goal_3 : solver_entail_wit_22_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH10 k_2 H).
Qed.

Lemma proof_of_solver_entail_wit_22_split_goal_4 : solver_entail_wit_22_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH9 k H).
Qed.

Lemma proof_of_solver_entail_wit_22 : solver_entail_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_22_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_22_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_22_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_22_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_26_split_goal_1 : solver_entail_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply negative_target_cell_implies_shortage__target_shortage;
    eauto; try lia.
  rewrite <- PreH4.
  exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_26_split_goal_2 : solver_entail_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH4.
  eapply count_state_target_step__target_shortage; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_26 : solver_entail_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_26_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_26_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_27 : solver_entail_wit_27.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH4 in PreH1 |- *.
  assert (Hidx : 0 <= Znth i target 0 - 97 < 26) by lia.
  pose proof (proj1 PreH24) as Hlen.
  assert (Hnewstate :
      CountState source pool target (Zlength source) (Zlength pool) (i + 1)
        (replace_Znth (Znth i target 0 - 97)
          (Znth (Znth i target 0 - 97) counts_2 0 - 1) counts_2)).
  {
    eapply count_state_target_step__target_shortage; eauto; lia.
  }
  assert (Hnewnonnegative :
      NonnegativeCounts
        (replace_Znth (Znth i target 0 - 97)
          (Znth (Znth i target 0 - 97) counts_2 0 - 1) counts_2)).
  {
    eapply nonnegative_counts_decrement__target_shortage; eauto; lia.
  }
  destruct (Z.eq_dec (i + 1) (Zlength target)) as [Hend | Hinterior].
  - Left.
    Exists (replace_Znth (Znth i target 0 - 97)
      (Znth (Znth i target 0 - 97) counts_2 0 - 1) counts_2).
    split_pure_spatial.
    + cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
      cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
      cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
      cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
      cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
      cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
      cancel (IntArray.full &( "cnt") 26
        (replace_Znth (Znth i target 0 - 97)
          (Znth (Znth i target 0 - 97) counts_2 0 - 1) counts_2)).
    + repeat split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: try lia.
      rewrite Hend.
      apply Znth_app_last__target_shortage.
  - Right.
    Exists (replace_Znth (Znth i target 0 - 97)
      (Znth (Znth i target 0 - 97) counts_2 0 - 1) counts_2).
    split_pure_spatial.
    + cancel (CharArray.full s_pre (Zlength source + 1) (source +:: 0)).
      cancel (CharArray.undef_seg s_pre (Zlength source + 1) 105).
      cancel (CharArray.full t_pre (Zlength target + 1) (target +:: 0)).
      cancel (CharArray.undef_seg t_pre (Zlength target + 1) 105).
      cancel (CharArray.full p_pre (Zlength pool + 1) (pool +:: 0)).
      cancel (CharArray.undef_seg p_pre (Zlength pool + 1) 105).
      cancel (IntArray.full &( "cnt") 26
        (replace_Znth (Znth i target 0 - 97)
          (Znth (Znth i target 0 - 97) counts_2 0 - 1) counts_2)).
    + repeat split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: try lia.
      all: try (apply Znth_app_left__target_shortage; lia).
      all: try (apply PreH15; lia).
Qed.

Lemma proof_of_solver_entail_wit_28_split_goal_1 : solver_entail_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply complete_counts_to_can_insert__success_final; eauto.
  rewrite <- PreH15. exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_28 : solver_entail_wit_28.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_28_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  split.
  - right. reflexivity.
  - split; intros.
    + assumption.
    + reflexivity.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  split.
  - left. reflexivity.
  - split.
    + lia.
    + intro Hcan.
      exfalso.
      eapply supply_shortage_excludes_can_insert__failure_final; eauto.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  split.
  - left. reflexivity.
  - split.
    + lia.
    + intro Hcan.
      exfalso.
      apply PreH3.
      eapply can_insert_implies_subsequence__failure_final; eauto.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.
