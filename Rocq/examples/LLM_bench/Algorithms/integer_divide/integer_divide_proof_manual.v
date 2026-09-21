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
From SimpleC.EE.LLM_bench.Algorithms.integer_divide Require Import integer_divide_goal.
From SimpleC.EE.LLM_bench.Algorithms.integer_divide Require Import integer_divide_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_lib.
Local Open Scope sac.

Lemma proof_of_divide_entail_wit_1 : divide_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (@nil Z).
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.undef_full_split_to_undef_seg p_pre 1 original).
    + dump_pre_spatial. lia.
    + rewrite IntArray.seg_empty.
      cancel (IntArray.undef_seg p_pre 0 1).
      split_pure_spatial.
      * cancel.
        replace (1 + 0) with 1 by lia.
        cancel.
      * dump_pre_spatial. lia.
  - split_pures.
    all: dump_pre_spatial; try lia.
    all: try unfold FactorizationProgress;
         simpl;
         repeat split; try constructor; try lia.
    all: destruct n_pre; simpl in *; lia.
Qed. 

Lemma proof_of_divide_entail_wit_3_1 : divide_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exfalso.
  assert (Hmod : Z.rem 1 i = 1) by (apply Z.rem_small; lia).
  replace n with 1 in PreH1 by lia.
  rewrite Hmod in PreH1.
  lia.
Qed. 

Lemma proof_of_divide_entail_wit_3_2 : divide_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    rewrite <- PreH11.
    eapply factorization_progress_room__progress_transitions; eauto.
Qed. 

Lemma proof_of_divide_entail_wit_4_1 : divide_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exfalso.
  assert (Hmod : Z.rem 1 i = 1) by (apply Z.rem_small; lia).
  replace n with 1 in PreH6 by lia.
  rewrite Hmod in PreH6.
  lia.
Qed. 

Lemma proof_of_divide_entail_wit_4_2 : divide_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (factorization_progress_extract__progress_transitions
       original factors_2 n i PreH9 PreH11 PreH13 PreH6 PreH17)
    as [Hprogress Hquotient_cases].
  assert (i <> 0) as Hi_nonzero by lia.
  assert (n = i * Z.quot n i) as Hdivide_exact.
  { apply (proj2 (Z.quot_exact n i Hi_nonzero)). exact PreH6. }
  assert (1 <= Z.quot n i) as Hquotient_positive by (destruct Hquotient_cases; lia).
  assert (Z.quot n i <= original) as Hquotient_upper.
  { apply Z.quot_le_upper_bound; [lia |].
    transitivity original; [lia |].
    rewrite <- (Z.mul_1_l original) at 1.
    apply Z.mul_le_mono_nonneg_r; lia. }
  destruct Hquotient_cases as [Hquotient_one | Hquotient_large].
  - Left.
    Exists (factors_2 ++ (i :: nil)).
    split_pure_spatial.
    + replace (1 + (cnt + 1)) with ((1 + cnt) + 1) by lia.
      cancel.
      cancel (IntArray.seg p_pre 1 ((1 + cnt) + 1)
        (factors_2 ++ (i :: nil))).
    + split_pures.
      all: dump_pre_spatial; try lia; try assumption.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - Right.
    Exists (factors_2 ++ (i :: nil)).
    split_pure_spatial.
    + replace (1 + (cnt + 1)) with ((1 + cnt) + 1) by lia.
      cancel.
      cancel (IntArray.seg p_pre 1 ((1 + cnt) + 1)
        (factors_2 ++ (i :: nil))).
    + split_pures.
      all: dump_pre_spatial; try lia; try assumption.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed. 

Lemma proof_of_divide_entail_wit_5_split_goal_1 : divide_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i <> n) as Hi_n.
  { intros Heq. subst n.
    apply PreH8.
    apply Z.rem_same. lia. }
  lia.
Qed.

Lemma proof_of_divide_entail_wit_5 : divide_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_divide_entail_wit_5_split_goal_1.
Qed. 

Lemma proof_of_divide_entail_wit_6_split_goal_1 : divide_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply factorization_progress_advance__progress_transitions; eauto.
Qed.

Lemma proof_of_divide_entail_wit_6 : divide_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_divide_entail_wit_6_split_goal_1.
Qed. 

Lemma proof_of_divide_return_wit_1 : divide_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists factors_2.
  split_pure_spatial.
  - rewrite PreH11.
    repeat cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply (factorization_progress_complete__final_result
        original factors_2 n i).
      * exact PreH4.
      * right; lia.
      * exact PreH12.
Qed. 

Lemma proof_of_divide_return_wit_2 : divide_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists factors_2.
  split_pure_spatial.
  - rewrite PreH12.
    repeat cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply (factorization_progress_complete__final_result
        original factors_2 n i).
      * exact PreH5.
      * left; exact PreH1.
      * exact PreH13.
Qed. 

