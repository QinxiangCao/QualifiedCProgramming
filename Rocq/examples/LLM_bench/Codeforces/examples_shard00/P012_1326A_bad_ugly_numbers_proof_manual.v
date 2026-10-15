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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P012_1326A_bad_ugly_numbers_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P012_1326A_bad_ugly_numbers_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite CharArray.seg_single.
  Exists (50 :: nil).
  split_pure_spatial.
  - cancel (CharArray.seg out_pre 0 1 (50 :: nil)).
    cancel (CharArray.undef_seg out_pre 1 100001).
  - repeat split_pures.
    all: dump_pre_spatial; simpl.
    all: try reflexivity.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite app_Znth1.
  - exact PreH7.
  - rewrite PreH6.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app.
  rewrite PreH6.
  simpl.
  reflexivity.
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
  assert (i_2 = n_pre) by lia. subst i_2.
  Exists chars_2 (map (fun c => c - 48) chars_2).
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.seg_to_full out_pre 0 (Zlength chars_2 + 1)
                          (chars_2 +:: 0)).
    replace (out_pre + 0 * sizeof(CHAR)) with out_pre by lia.
    replace (Zlength chars_2 + 1 - 0) with (Zlength chars_2 + 1) by lia.
    cancel (CharArray.full out_pre (Zlength chars_2 + 1) (chars_2 +:: 0)).
    cancel (CharArray.undef_seg out_pre (Zlength chars_2 + 1) 100001).
  - split_pures.
    + dump_pre_spatial.
      unfold Spec. left.
      exists (map (fun c => c - 48) chars_2).
      split; [reflexivity |].
      apply two_then_threes_bad_ugly__spec_results.
      * lia.
      * rewrite Zlength_map_Z__spec_results. lia.
      * rewrite (Znth_map_inbounds_Z__spec_results
                   (fun c => c - 48) chars_2 0 0 0) by lia.
        lia.
      * intros k Hk.
        rewrite (Znth_map_inbounds_Z__spec_results
                   (fun c => c - 48) chars_2 k 0 0) by lia.
        specialize (PreH8 k ltac:(lia)). lia.
    + dump_pre_spatial. rewrite Zlength_map_Z__spec_results. reflexivity.
    + dump_pre_spatial. intros j Hj.
      rewrite (Znth_map_inbounds_Z__spec_results
                 (fun c => c - 48) chars_2 j 0 0) by
        (rewrite Zlength_map_Z__spec_results in Hj; lia).
      lia.
    + dump_pre_spatial. rewrite Zlength_map_Z__spec_results. lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Left.
  split_pure_spatial.
  - cancel (CharArray.undef_full out_pre 100001).
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      unfold Spec. right.
      split; [reflexivity |].
      intros digits Hbad.
      subst n_pre.
      apply (no_bad_ugly_length_one__spec_results digits).
      exact Hbad.
Qed.
