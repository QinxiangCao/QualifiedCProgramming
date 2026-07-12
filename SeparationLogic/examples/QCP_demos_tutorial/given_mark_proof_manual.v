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
From SimpleC.SL Require Import Mem IntLib SeparationLogic.
From SimpleC.EE.QCP_demos_tutorial Require Import given_mark_goal.
From SimpleC.EE.QCP_demos_tutorial Require Import given_mark_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_bounded_power_of_two_return_wit_1 : bounded_power_of_two_return_wit_1.
Proof.
  pre_process.
  Exists 3.
  entailer!.
Qed.

Lemma proof_of_given_of_marked_call_entail_wit_2 : given_of_marked_call_entail_wit_2.
Proof.
  pre_process.
  Exists (t + 2).
  entailer!.
Qed.

Lemma proof_of_given_from_of_two_marked_calls_safety_wit_1 : given_from_of_two_marked_calls_safety_wit_1.
Proof.
  pre_process.
  - rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite !Z.mul_1_l.
    assert (Hfirst_nonneg : 0 <= first_t + 2) by lia.
    assert (Hsecond_nonneg : 0 <= second_t + 2) by lia.
    assert (Hfirst_bound : 2 ^ (first_t + 2) <= 2 ^ 11).
    { apply Z.pow_le_mono_r; lia. }
    assert (Hsecond_bound : 2 ^ (second_t + 2) <= 2 ^ 11).
    { apply Z.pow_le_mono_r; lia. }
    change (2 ^ 11) with 2048 in Hfirst_bound, Hsecond_bound.
    entailer!.
Qed. 
