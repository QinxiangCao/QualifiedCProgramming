Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.longest_nondecreasing_subsequence Require Import longest_nondecreasing_subsequence_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_nondecreasing_subsequence.longest_nondecreasing_subsequence_lib.
Local Open Scope sac.

Lemma proof_of_lengthOfLNDS_safety_wit_4 : lengthOfLNDS_safety_wit_4.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    assert (Hquot_le : (right - left) ÷ 2 <= right - left) by
      (apply Z.quot_le_upper_bound; lia).
    lia.
  - dump_pre_spatial.
    assert (Hquot_nonneg : 0 <= (right - left) ÷ 2) by
      (apply Z.quot_pos; lia).
    lia.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_1 : lengthOfLNDS_entail_wit_1.
Proof.
  pre_process.
  Exists tails_l.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    unfold sublist; simpl.
    apply LNDTailsState_empty.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_3 : lengthOfLNDS_entail_wit_3.
Proof.
  pre_process.
  Exists tails_cur_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    match goal with
    | Htail : LNDTailsState _ _ _ _ |- _ =>
        unfold LNDTailsState in Htail;
        destruct Htail as [_ [_ [Hlen_sub [Hnd _]]]];
        apply UpperBoundSearch_full; auto; lia
    end.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_4 : lengthOfLNDS_entail_wit_4.
Proof.
  pre_process.
  Exists tails_cur_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    + assert (Hquot_nonneg : 0 <= (right - left) ÷ 2) by
        (apply Z.quot_pos; lia).
      lia.
    + assert (Hquot_lt : (right - left) ÷ 2 < right - left) by
        (apply Z.quot_lt_upper_bound; lia).
      lia.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_5_1 : lengthOfLNDS_entail_wit_5_1.
Proof.
  pre_process.
  Exists tails_cur_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    eapply UpperBoundSearch_right_preserve; eauto; try lia.
    rewrite Znth_sublist0; auto; lia.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_5_2 : lengthOfLNDS_entail_wit_5_2.
Proof.
  pre_process.
  Exists tails_cur_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    eapply UpperBoundSearch_left_preserve; eauto; try lia.
    rewrite Znth_sublist0; auto; lia.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_6 : lengthOfLNDS_entail_wit_6.
Proof.
  pre_process.
  Exists tails_cur_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    replace right with left in * by lia.
    assumption.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_7 : lengthOfLNDS_entail_wit_7.
Proof.
  pre_process.
  Exists tails_cur.
  split_pure_spatial.
  - replace (replace_Znth left x tails_cur) with
      (sublist 0 left tails_cur ++ x :: sublist (left + 1) numsSize_pre tails_cur).
    + entailer!.
    + rewrite replace_Znth_sublist; auto; try lia.
      rewrite PreH4. reflexivity.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_8_2 : lengthOfLNDS_entail_wit_8_2.
Proof.
  pre_process.
  Exists (sublist 0 left tails_old ++ x :: sublist (left + 1) numsSize_pre tails_old).
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    + rewrite Zlength_app, Zlength_sublist0, Zlength_cons, Zlength_sublist by lia.
      lia.
    + rewrite sublist_update_replace_prefix by lia.
      eapply LNDTailsState_replace; eauto; lia.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_8_1 : lengthOfLNDS_entail_wit_8_1.
Proof.
  pre_process.
  Exists (sublist 0 left tails_old ++ x :: sublist (left + 1) numsSize_pre tails_old).
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    + rewrite Zlength_app, Zlength_sublist0, Zlength_cons, Zlength_sublist by lia.
      lia.
    + replace left with len in * by lia.
      rewrite sublist_update_append_prefix by lia.
      eapply LNDTailsState_append; eauto; lia.
Qed. 

Lemma proof_of_lengthOfLNDS_entail_wit_10 : lengthOfLNDS_entail_wit_10.
Proof.
  pre_process.
  Exists tails_cur_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    unfold LNDSLength.
    replace (Zlength l) with i by lia.
    match goal with
    | Htail : LNDTailsState _ _ _ _ |- _ =>
        unfold LNDTailsState in Htail; tauto
    end.
Qed. 
