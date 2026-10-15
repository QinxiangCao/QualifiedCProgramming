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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P045_959C_mahmoud_and_ehab_and_the_wrong_algorithm_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P045_959C_mahmoud_and_ehab_and_the_wrong_algorithm_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P045_959C_mahmoud_and_ehab_and_the_wrong_algorithm_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof seed_lists_properties__invariant_construction as Hseed.
  destruct Hseed as [Huslen [Hvslen Hseed]].
  Exists (2 :: 3 :: 4 :: 5 :: 6 :: nil)
         (1 :: 1 :: 1 :: 2 :: 2 :: nil).
  split_pure_spatial.
  - repeat rewrite IntArray.seg_unfold.
    repeat rewrite IntArray.seg_empty.
    simpl.
    rewrite Z.add_0_r.
    cancel.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; lia.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact Huslen.
    + dump_pre_spatial. exact Hvslen.
    + dump_pre_spatial. exact Hseed.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hv : v = n_pre + 1) by lia.
  assert (Hm : m = n_pre - 1) by lia.
  assert (Hcorrect_ex : exists e, CorrectTree n_pre e).
  { eexists. apply canonical_star_correct__final_semantics. lia. }
  destruct Hcorrect_ex as [star Hstar].
  destruct __default__Prod_Z_Z as [du dv].
  Exists vs_2 us_2 (combine us_2 vs_2)
    (Some (combine us_2 vs_2), Some star).
  split_pure_spatial.
  - rewrite Hm.
    rewrite (IntArray.undef_seg_empty eu_pre (n_pre - 1)).
    rewrite (IntArray.undef_seg_empty ev_pre (n_pre - 1)).
    sep_apply_l_atomic
      (IntArray.seg_to_full eu_pre 0 (n_pre - 1) us_2).
    sep_apply_l_atomic
      (IntArray.seg_to_full ev_pre 0 (n_pre - 1) vs_2).
    replace (eu_pre + 0 * sizeof(INT)) with eu_pre by lia.
    replace (ev_pre + 0 * sizeof(INT)) with ev_pre by lia.
    replace (n_pre - 1 - 0) with (n_pre - 1) by lia.
    cancel.
  - split_pures; dump_pre_spatial; simpl.
    + unfold Spec. simpl. split.
      * right. exists (combine us_2 vs_2). split; [reflexivity |].
        apply indexed_double_star_wrong__final_semantics; try lia.
        intros i Hi. apply PreH9. lia.
      * right. exists star. split; [reflexivity | exact Hstar].
    + reflexivity.
    + reflexivity.
    + rewrite Zlength_combine_eq__final_semantics by lia. lia.
    + lia.
    + lia.
    + intros i Hi.
      rewrite (combine_Znth_pair__final_semantics us_2 vs_2 i du dv)
        by lia.
      simpl.
      rewrite (Znth_indep us_2 i 0 du) by lia.
      rewrite (Znth_indep vs_2 i 0 dv) by lia.
      auto.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcorrect_ex : exists e, CorrectTree n_pre e).
  { eexists. apply canonical_star_correct__final_semantics. lia. }
  destruct Hcorrect_ex as [star Hstar].
  Exists (None, Some star).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; simpl.
    + unfold Spec. simpl. split.
      * left. split; [reflexivity |].
        apply no_wrong_tree_below_six__final_semantics. lia.
      * right.
        exists star. split; [reflexivity | exact Hstar].
    + reflexivity.
    + reflexivity.
Qed.
