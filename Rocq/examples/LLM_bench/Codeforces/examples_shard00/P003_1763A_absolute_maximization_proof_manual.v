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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P003_1763A_absolute_maximization_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P003_1763A_absolute_maximization_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply bitwise_scan_state_zero__scan_core.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH4.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply bitwise_scan_state_succ__scan_core.
  - rewrite <- PreH2. lia.
  - exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH7 i ltac:(lia)) as Hi.
  pose proof (bounded_lor_land__scan_core all_and (Znth i input 0)
    ltac:(lia) ltac:(lia)) as Hbounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH7 i ltac:(lia)) as Hi.
  pose proof (bounded_lor_land__scan_core all_and (Znth i input 0)
    ltac:(lia) ltac:(lia)) as Hbounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_4 : solver_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH7 i ltac:(lia)) as Hi.
  pose proof (bounded_lor_land__scan_core all_or (Znth i input 0)
    ltac:(lia) ltac:(lia)) as Hbounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_5 : solver_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH7 i ltac:(lia)) as Hi.
  pose proof (bounded_lor_land__scan_core all_or (Znth i input 0)
    ltac:(lia) ltac:(lia)) as Hbounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_5.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  apply (bitwise_scan_final_implies_spec__final_result
    n_pre input all_or all_and).
  - lia.
  - lia.
  - intros k Hk. apply PreH7. lia.
  - lia.
  - lia.
  - exact PreH12.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
