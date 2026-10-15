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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P033_1454D_number_into_sequence_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P033_1454D_number_into_sequence_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P033_1454D_number_into_sequence_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (factor_search_profile_initial__search_initialization n_pre
      ltac:(lia)) as (Hstate & Hprofile).
  Exists (@nil Z) (@nil Z).
  split_pure_spatial.
  - cancel (Int64Array.undef_full out_pre 64).
  - split_pures; dump_pre_spatial; try lia; assumption.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (factor_extract_initial__search_initialization
      n_pre value p best_prime best_exp ps_2 es_2
      PreH1 ltac:(exact PreH2) PreH15)
    as (Hguard & Hstate & Horigin).
  Exists ps_2 es_2.
  split_pure_spatial.
  - cancel (Int64Array.undef_full out_pre 64).
  - split_pures; dump_pre_spatial; try lia; assumption.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmod : value mod p = 0).
  { rewrite <- Z.rem_mod_nonneg by lia. exact PreH1. }
  pose proof (Z.quot_div_nonneg value p ltac:(lia) ltac:(lia)) as Hquot.
  pose proof (factor_extract_core_step__search_initialization
    n_pre value p e best_prime best_exp ps_2 es_2
    Hmod PreH16 PreH17) as (Hstate_next & Horigin_next).
  pose proof (factor_extract_guard_step__search_initialization
    value p e PreH6 Hmod PreH8 PreH15) as Hguard_next.
  assert (Hguard_quot : FactorExtractGuard (value ÷ p) p (e + 1)).
  { rewrite Hquot. exact Hguard_next. }
  assert (Hstate_quot :
      FactorExtractState n_pre (value ÷ p) p (e + 1)
        best_prime best_exp).
  { rewrite Hquot. exact Hstate_next. }
  assert (Horigin_quot :
      FactorExtractOrigin n_pre (value ÷ p) p (e + 1)
        best_prime best_exp ps_2 es_2).
  { rewrite Hquot. exact Horigin_next. }
  pose proof Hstate_next as Hstate_data.
  unfold FactorExtractState in Hstate_data.
  destruct Hstate_data as
    (_ & Hvalue_next & _ & He_next & _ & _ & _ & _).
  Exists ps_2 es_2.
  split_pure_spatial.
  - cancel (Int64Array.undef_full out_pre 64).
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmod : value mod p <> 0).
  { rewrite <- Z.rem_mod_nonneg by lia. exact PreH1. }
  assert (Hzero : e = 0 -> value mod p = 0).
  { intros Heq. rewrite <- Z.rem_mod_nonneg by lia.
    apply PreH14. exact Heq. }
  pose proof (factor_extract_exit_positive__search_initialization
    value p e PreH8 Hzero Hmod) as He_positive.
  pose proof (factor_extract_successor_profiles__extraction_lifecycle
    n_pre value p e best_prime best_exp ps_2 es_2
    Hmod He_positive PreH15 PreH16 PreH17)
    as (Hsuccess_gt & Hsuccess_le).
  pose proof (factor_extract_profile_from_successors__search_initialization
    n_pre value p e best_prime best_exp ps_2 es_2
    Hmod He_positive PreH15 PreH16 PreH17 Hsuccess_gt Hsuccess_le)
    as Hprofile.
  Exists ps_2 es_2.
  split_pure_spatial.
  - cancel (Int64Array.undef_full out_pre 64).
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold FactorSearchProfile in PreH14.
  destruct PreH14 as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hterminal).
  apply Hterminal.
  nia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (ps_2 ++ p :: nil) (es_2 ++ e :: nil).
  unfold FactorExtractProfile in PreH18.
  destruct PreH18 as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hsuccess_gt & _).
  rewrite Z.rem_mod_nonneg in PreH14 by lia.
  specialize (Hsuccess_gt PreH14 PreH1).
  pose proof Hsuccess_gt as Hprofile.
  unfold FactorSearchProfile in Hsuccess_gt.
  destruct Hsuccess_gt as
    (Hstate & _ & _ & _ & _ & _ & _ & _ & Hnext & _).
  pose proof Hstate as Hstate_data.
  unfold FactorSearchState in Hstate_data.
  destruct Hstate_data as
    (Hn & Hvalue & Hp & Hsquare & Hexp & Hprime &
     Hvalue_div & Hbest_div & Hpast).
  split_pure_spatial.
  - cancel (Int64Array.undef_full out_pre 64).
  - split_pures; dump_pre_spatial; try assumption; try nia.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (ps_2 ++ p :: nil) (es_2 ++ e :: nil).
  unfold FactorExtractProfile in PreH18.
  destruct PreH18 as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsuccess_le).
  rewrite Z.rem_mod_nonneg in PreH14 by lia.
  specialize (Hsuccess_le PreH14 PreH1).
  pose proof Hsuccess_le as Hprofile.
  unfold FactorSearchProfile in Hsuccess_le.
  destruct Hsuccess_le as
    (Hstate & _ & _ & _ & _ & _ & _ & _ & Hnext & _).
  pose proof Hstate as Hstate_data.
  unfold FactorSearchState in Hstate_data.
  destruct Hstate_data as
    (Hn & Hvalue & Hp & Hsquare & Hexp & Hprime &
     Hvalue_div & Hbest_div & Hpast).
  split_pure_spatial.
  - cancel (Int64Array.undef_full out_pre 64).
  - split_pures; dump_pre_spatial; try assumption; try nia.
Qed.

Lemma proof_of_solver_entail_wit_6_3 : solver_entail_wit_6_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg in PreH1 by lia.
  pose proof
    (factor_search_profile_skip__search_transitions
       n_pre value p best_prime best_exp ps_2 es_2 PreH1 PreH2 PreH15)
    as Hprofile.
  assert (Hstate :
      FactorSearchState n_pre value (p + 1) best_prime best_exp).
  { exact (proj1 Hprofile). }
  Exists ps_2 es_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold OutputPrefixState.
  split; [exact PreH9 |].
  repeat split; try lia.
  all: try (intros j Hj; lia).
  all: try (rewrite Z.pow_0_r; ring).
  all: try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (output_prefix_step__output_construction
    n_pre best_prime best_exp i rest written_2 PreH1 PreH15) as Hstep.
  rewrite Z.quot_div_nonneg by lia.
  exact (proj1 Hstep).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (output_prefix_step__output_construction
    n_pre best_prime best_exp i rest written_2 PreH1 PreH15) as Hstep.
  rewrite Z.quot_div_nonneg by lia.
  exact (proj1 (proj2 Hstep)).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (output_prefix_step__output_construction
    n_pre best_prime best_exp i rest written_2 PreH1 PreH15) as Hstep.
  rewrite Z.quot_div_nonneg by lia.
  exact (proj2 (proj2 Hstep)).
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = best_exp - 1) by lia.
  subst i.
  Exists written_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (final_output_from_prefix__final_result
       n_pre best_prime best_exp rest written PreH11 PreH12)
    as [Hfinal Hspec].
  Exists (written ++ (rest :: nil)).
  split_pure_spatial.
  - replace (best_exp - 1 + 1) with best_exp by lia.
    sep_apply (Int64Array.seg_to_full out_pre 0 best_exp
      (written ++ (rest :: nil))).
    replace (out_pre + 0 * sizeof(INT64)) with out_pre by lia.
    replace (best_exp - 0) with best_exp by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold FinalOutputSequence in PreH7.
  destruct PreH7 as
    (_ & _ & Hresult_len & _ & _ & _ & _).
  symmetry.
  exact Hresult_len.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
