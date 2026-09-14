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
From SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse Require Import linear_modular_inverse_goal.
From SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse Require Import linear_modular_inverse_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_lib.
Local Open Scope sac.

Lemma proof_of_linear_modular_inverse_entail_wit_1 : linear_modular_inverse_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (1 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single inverse_pre 1 1).
    simpl Z.add.
    cancel (IntArray.seg inverse_pre 1 2 (1 :: nil)).
    cancel (IntArray.undef_seg inverse_pre 2 p_pre).
  - split_pures; dump_pre_spatial.
    + exact PreH1.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold ModularInversePrefix.
      split.
      * rewrite Zlength_cons, Zlength_nil.
        lia.
      * intros index Hindex.
        replace index with 1 by lia.
        unfold CanonicalModularInverse.
        change
          (1 <= 1 < p_pre /\
           0 < 1 < p_pre /\
           exists coefficient : Z,
             1 * 1 + p_pre * coefficient = 1).
        split; [lia |].
        split; [lia |].
        exists 0.
        lia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_1 : linear_modular_inverse_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg, Z.rem_mod_nonneg by lia.
  destruct (linear_inverse_division_facts__recurrence_core
              p_pre i PreH2 ltac:(lia))
    as [Hdiv [Hquot [[Hrem_pos Hrem_lt] [Hdiff_pos Hdiff_lt]]]].
  destruct PreH7 as [Hlen Hprefix].
  specialize (Hprefix (p_pre mod i) ltac:(lia)).
  destruct Hprefix as [_ [[Hvalue_pos Hvalue_lt] _]].
  apply (linear_inverse_product_bound__recurrence_core
           p_pre (p_pre - p_pre / i)
           (Znth (p_pre mod i - 1) values_2 0)).
  - lia.
  - lia.
  - lia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_2 : linear_modular_inverse_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg, Z.rem_mod_nonneg by lia.
  destruct (linear_inverse_division_facts__recurrence_core
              p_pre i PreH2 ltac:(lia))
    as [Hdiv [Hquot [[Hrem_pos Hrem_lt] [Hdiff_pos Hdiff_lt]]]].
  destruct PreH7 as [Hlen Hprefix].
  specialize (Hprefix (p_pre mod i) ltac:(lia)).
  destruct Hprefix as [_ [[Hvalue_pos Hvalue_lt] _]].
  nia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_3 : linear_modular_inverse_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  destruct (linear_inverse_division_facts__recurrence_core
              p_pre i PreH2 ltac:(lia))
    as [Hdiv [Hquot [[Hrem_pos Hrem_lt] Hdiff]]].
  destruct PreH7 as [Hlen Hprefix].
  specialize (Hprefix (p_pre mod i) ltac:(lia)).
  destruct Hprefix as [_ [[Hvalue_pos Hvalue_lt] _]].
  lia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_4 : linear_modular_inverse_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  destruct (linear_inverse_division_facts__recurrence_core
              p_pre i PreH2 ltac:(lia))
    as [Hdiv [Hquot [[Hrem_pos Hrem_lt] Hdiff]]].
  destruct PreH7 as [Hlen Hprefix].
  specialize (Hprefix (p_pre mod i) ltac:(lia)).
  destruct Hprefix as [_ [[Hvalue_pos Hvalue_lt] _]].
  lia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_5 : linear_modular_inverse_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  destruct (linear_inverse_division_facts__recurrence_core
              p_pre i PreH2 ltac:(lia))
    as [Hdiv [Hquot [Hrem [Hdiff_pos Hdiff_lt]]]].
  lia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_6 : linear_modular_inverse_entail_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  destruct (linear_inverse_division_facts__recurrence_core
              p_pre i PreH2 ltac:(lia))
    as [Hdiv [Hquot [Hrem [Hdiff_pos Hdiff_lt]]]].
  lia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_7 : linear_modular_inverse_entail_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  apply Z.mod_pos_bound.
  lia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_8 : linear_modular_inverse_entail_wit_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  destruct PreH2 as [Hp Hprime].
  pose proof (Z.mod_pos_bound p_pre i ltac:(lia)) as Hrem.
  specialize (Hprime i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_9 : linear_modular_inverse_entail_wit_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  destruct (linear_inverse_division_facts__recurrence_core
              p_pre i PreH2 ltac:(lia))
    as [Hdiv [Hquot [Hrem Hdiff]]].
  lia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2_split_goal_10 : linear_modular_inverse_entail_wit_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg, Z.rem_mod_nonneg by lia.
  pose proof (Z.div_mod p_pre i ltac:(lia)) as Hdiv.
  nia.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_2 : linear_modular_inverse_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_5.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_6.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_7.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_8.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_9.
  - Goal_apply proof_of_linear_modular_inverse_entail_wit_2_split_goal_10.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_3_split_goal_1 : linear_modular_inverse_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg in PreH6 by lia.
  rewrite Z.rem_mod_nonneg in PreH7 by lia.
  subst quotient remainder.
  rewrite <- PreH8.
  rewrite !Z.quot_div_nonneg by lia.
  rewrite (Z.rem_mod_nonneg p_pre i) by lia.
  rewrite Z.rem_mod_nonneg by nia.
  apply (linear_inverse_prefix_extend__recurrence_core
           p_pre i (p_pre / i) (p_pre mod i) values_2).
  - exact PreH1.
  - lia.
  - reflexivity.
  - reflexivity.
  - exact PreH18.
Qed.

Lemma proof_of_linear_modular_inverse_entail_wit_3 : linear_modular_inverse_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_linear_modular_inverse_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_linear_modular_inverse_return_wit_1 : linear_modular_inverse_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with p_pre in * by lia.
  Exists values_2.
  rewrite (IntArray.undef_seg_empty inverse_pre p_pre).
  split_pure_spatial.
  - cancel (IntArray.seg inverse_pre 1 p_pre values_2).
  - split_pures.
    dump_pre_spatial.
    exact PreH7.
Qed.
