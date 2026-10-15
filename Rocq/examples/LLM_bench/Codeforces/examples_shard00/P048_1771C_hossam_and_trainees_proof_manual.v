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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P048_1771C_hossam_and_trainees_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P048_1771C_hossam_and_trainees_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (complete_prime_table_index_bounds__safety_prime_bounds prime_data j
       PreH19 ltac:(lia)) as [_ Hprime_bounds].
  pose proof
    (bounded_prime_square_int64__safety_prime_bounds
       (Znth j prime_data 0) Hprime_bounds) as Hsquare.
  cancel.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (complete_prime_table_index_bounds__safety_prime_bounds prime_data j
       PreH20 ltac:(lia)) as [_ Hprime_bounds].
  cancel.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (factor_divide_state_current_prime__safety_prime_bounds
       a prime_data i j x factor_data PreH20) as [_ Hnonzero].
  cancel.
  dump_pre_spatial.
  exact Hnonzero.
Qed.

Lemma proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (factor_divide_state_current_prime__safety_prime_bounds
       a prime_data i j x factor_data PreH21) as [_ Hnonzero].
  cancel.
  dump_pre_spatial.
  exact Hnonzero.
Qed.

Lemma proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrimePrefixTable2.
  split; [lia |].
  split.
  - rewrite Zlength_correct. unfold repeat_Z. rewrite repeat_length. lia.
  - split; [constructor |].
    split; [constructor |].
    split; [simpl; exact I |].
    split.
    + intros p. simpl. split.
      * contradiction.
      * intros [[Hp2 Hlt] _]. lia.
    + intros k Hk. split.
      * intros _. unfold ProperMarkedBefore.
        intros [d [[Hd Hlt] _]]. lia.
      * intros _. unfold repeat_Z. apply Znth_repeat.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply PreH3; eauto.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply prime_prefix_table2_begin_mark__sieve_construction; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (prime_prefix_table2_capacity__sieve_construction
    i prime_data_2 composite_data_2 PreH14).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_4 : solver_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply PreH7; eauto.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply prime_mark_table2_replace_step__sieve_marking_exits; eauto.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth; assumption.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply prime_mark_table2_finish__sieve_marking_exits with (next := j); auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply prime_prefix_table2_advance_unmarked__sieve_construction; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (prime_prefix_table2_capacity__sieve_construction
    i prime_data_2 composite_data_2 PreH14).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_3 : solver_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply prime_prefix_table2_advance_marked__sieve_construction; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply prime_factor_bag_prefix_zero__sieve_marking_exits.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply prime_prefix_table2_complete__sieve_marking_exits with composite_data_2.
  replace i with 31624 in * by lia.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6; lia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold FactorAppendCapacity.
  intros.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_scan_state2_initial__factor_scan_divide.
  - exact PreH16.
  - lia.
  - apply (proj1 (PreH5 i ltac:(lia))).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply FactorScanState2_implies_FactorScanState.
  eapply factor_scan_state2_initial__factor_scan_divide.
  - exact PreH16.
  - lia.
  - apply (proj1 (PreH5 i ltac:(lia))).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_4 : solver_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5. exact H.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_scan_state2_append_divisor__factor_scan_divide.
  - exact PreH21.
  - exact PreH23.
  - lia.
  - eapply complete_prime_table_mod_zero_divides__factor_scan_divide;
      eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply FactorDivideState2_implies_FactorDivideState.
  eapply factor_scan_state2_append_divisor__factor_scan_divide.
  - exact PreH21.
  - exact PreH23.
  - lia.
  - eapply complete_prime_table_mod_zero_divides__factor_scan_divide;
      eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH24.
  split; [lia |].
  eapply complete_prime_table_mod_zero_divides__factor_scan_divide;
    eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_5 : solver_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7. exact H.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_divide_state2_reduce__factor_scan_divide.
  - exact PreH21.
  - eapply complete_prime_table_mod_zero_divides__factor_scan_divide;
      eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply FactorDivideState2_implies_FactorDivideState.
  eapply factor_divide_state2_reduce__factor_scan_divide.
  - exact PreH21.
  - eapply complete_prime_table_mod_zero_divides__factor_scan_divide;
      eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (factor_divide_state2_reduce__factor_scan_divide
      a prime_data_2 i j x factor_data_2 PreH21
      (complete_prime_table_mod_zero_divides__factor_scan_divide
        prime_data_2 j x PreH19 ltac:(lia) PreH1))
    as Hreduced.
  unfold FactorDivideState2 in Hreduced.
  destruct Hreduced as
    (done & picked & p & Hfactors & Hbag & Hindex & Htested & Hp & Hprime &
     Hpdiv & Hquotbounds & Hquotdiv & Hnodup & Hprimes & Hpicked & Hprior &
     Hcoverage).
  assert (Hdefault : Znth i a 0 = Znth i a 1).
  { apply Znth_indep. lia. }
  pose proof (proj2 (PreH5 i ltac:(lia))) as Hbound.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (factor_divide_state2_reduce__factor_scan_divide
      a prime_data_2 i j x factor_data_2 PreH21
      (complete_prime_table_mod_zero_divides__factor_scan_divide
        prime_data_2 j x PreH19 ltac:(lia) PreH1))
    as Hreduced.
  unfold FactorDivideState2 in Hreduced.
  destruct Hreduced as
    (done & picked & p & Hfactors & Hbag & Hindex & Htested & Hp & Hprime &
     Hpdiv & Hquotbounds & Hquotdiv & Hnodup & Hprimes & Hpicked & Hprior &
     Hcoverage).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Ha : Forall (fun y => 1 <= y <= 1000000000) a).
  { apply pointwise_bounds_Forall__factor_scan_advance. exact PreH5. }
  assert (Hnext :
      FactorScanState2 a prime_data_2 i (j + 1) x factor_data_2).
  { eapply factor_divide2_to_scan2_next__factor_scan_advance; eauto. }
  eapply factor_scan2_capacity_next__factor_scan_advance; eauto.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_2 : solver_entail_wit_9_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_divide2_to_scan2_next__factor_scan_advance; eauto.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_3 : solver_entail_wit_9_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply FactorScanState2_implies_FactorScanState.
  eapply factor_divide2_to_scan2_next__factor_scan_advance; eauto.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_4 : solver_entail_wit_9_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5. assumption.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Ha : Forall (fun y => 1 <= y <= 1000000000) a).
  { apply pointwise_bounds_Forall__factor_scan_advance. exact PreH7. }
  assert (Hnext :
      FactorScanState2 a prime_data_2 i (j + 1) x factor_data_2).
  { eapply factor_scan2_to_scan2_next__factor_scan_advance; eauto; lia. }
  eapply factor_scan2_capacity_next__factor_scan_advance; eauto.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_2 : solver_entail_wit_9_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_scan2_to_scan2_next__factor_scan_advance; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_3 : solver_entail_wit_9_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply FactorScanState2_implies_FactorScanState.
  eapply factor_scan2_to_scan2_next__factor_scan_advance; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_scan2_residual_complete__factor_item_finish.
  - exact PreH22.
  - eapply residual_prime_exhausted__factor_item_finish.
    + exact PreH20.
    + destruct PreH22 as
        (done & picked & Hfactors & Hbag & Hindex & Htested & Hrem_bounds &
         Hrem_divides & Hnodup & Hprimes & Hpicked & Hexcluded & Hcoverage).
      exact Htested.
    + destruct PreH22 as
        (done & picked & Hfactors & Hbag & Hindex & Htested & Hrem_bounds &
         Hrem_divides & Hnodup & Hprimes & Hpicked & Hexcluded & Hcoverage).
      exact Hexcluded.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_2 : solver_entail_wit_10_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_3 : solver_entail_wit_10_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6. exact H.
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_scan2_residual_complete__factor_item_finish.
  - exact PreH23.
  - eapply (residual_prime_square_cutoff__factor_item_finish
              prime_data_2 j x).
    + exact PreH21.
    + destruct PreH23 as
        (done & picked & Hfactors & Hbag & Hindex & Htested & Hrem_bounds &
         Hrem_divides & Hnodup & Hprimes & Hpicked & Hexcluded & Hcoverage).
      lia.
    + destruct PreH23 as
        (done & picked & Hfactors & Hbag & Hindex & Htested & Hrem_bounds &
         Hrem_divides & Hnodup & Hprimes & Hpicked & Hexcluded & Hcoverage).
      exact Hexcluded.
    + lia.
    + exact PreH2.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_2 : solver_entail_wit_10_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_3 : solver_entail_wit_10_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7. exact H.
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_10_3_split_goal_1 : solver_entail_wit_10_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_scan2_unit_complete__factor_item_finish.
  - exact PreH22.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_10_3_split_goal_2 : solver_entail_wit_10_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6. exact H.
Qed.

Lemma proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_4_split_goal_1 : solver_entail_wit_10_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_scan2_unit_complete__factor_item_finish.
  - exact PreH23.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_10_4_split_goal_2 : solver_entail_wit_10_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7. exact H.
Qed.

Lemma proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply duplicate_scan_loop_initial__duplicate_init_result; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply prime_factor_bag_prefix_permutation__duplicate_init_result; eauto.
  replace n_pre with i by lia.
  exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply (prime_factor_duplicate_spec__duplicate_init_result
            a sorted_2 count ok).
  - exact PreH13.
  - rewrite <- PreH2. exact PreH15.
  - apply (duplicate_scan_loop_exit__duplicate_init_result
             sorted_2 count i ok).
    + lia.
    + exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (duplicate_scan_loop_exit__duplicate_init_result
           sorted_2 count i ok).
  - lia.
  - exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_13_1_split_goal_1 : solver_entail_wit_13_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply duplicate_scan_equal_step__duplicate_loop; eauto.
Qed.

Lemma proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_13_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_2_split_goal_1 : solver_entail_wit_13_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply duplicate_scan_unequal_step__duplicate_loop; eauto.
Qed.

Lemma proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_13_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_spatial : solver_entail_wit_14_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.full_to_undef_full
                        (&( "primes" )) pc prime_data).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg
                        (&( "primes" )) pc).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full
                        (&( "primes" )) 0 pc 4000 ltac:(lia)).
  replace (&( "primes" ) + 0 * sizeof (INT))
    with (&( "primes" )) by lia.
  replace (4000 - 0) with 4000 by lia.
  sep_apply_l_atomic (UCharArray.full_to_undef_full
                        (&( "composite" )) 31624 composite_data).
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_14_split_goal_spatial.
Qed.
