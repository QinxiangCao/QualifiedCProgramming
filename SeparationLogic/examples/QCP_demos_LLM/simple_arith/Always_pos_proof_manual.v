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
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import Always_pos_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import Apos_lib.
Local Open Scope sac.

Lemma proof_of_Always_positive_simple_return_wit_4 : Always_positive_simple_return_wit_4.
Proof.
  pre_process.
  entailer!.
  unfold Always_pos. 
  subst. simpl. lia.
Qed.

Lemma proof_of_Always_positive_simple_return_wit_3 : Always_positive_simple_return_wit_3.
Proof.
  pre_process.
  entailer!.
  unfold Always_pos.
  destruct (Z.eq_dec a_pre 0) ; try lia.
  destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0) ; try nia.
  assert (b_pre * b_pre ÷ 4 < a_pre * c_pre).
  { apply Z.quot_lt_upper_bound ; nia. }
  nia.
Qed.

Lemma proof_of_Always_positive_simple_return_wit_2 : Always_positive_simple_return_wit_2.
Proof.
  pre_process.
  entailer!.
  unfold Always_pos.
  destruct (Z.eq_dec a_pre 0) ; try lia.
  destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0) ; try nia.
  - assert (a_pre * c_pre <= b_pre * b_pre ÷ 4).
    { apply Z.quot_le_lower_bound ; lia. }
    nia.
  - destruct (Z_gt_le_dec a_pre 0) ; try lia.
Qed.

Lemma proof_of_Always_positive_simple_return_wit_1 : Always_positive_simple_return_wit_1.
Proof.
  pre_process.
  entailer!.
  unfold Always_pos.
  destruct (Z.eq_dec a_pre 0) ; try lia.
  destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0) ; try nia.
  destruct (Z_gt_le_dec a_pre 0) ; try lia.
Qed. 

Lemma proof_of_Always_positive_entail_wit_2 : Always_positive_entail_wit_2.
Proof. 
  pre_process.
Qed.  

Lemma proof_of_Always_positive_return_wit_5 : Always_positive_return_wit_5.
Proof.
  pre_process.
  entailer!.
  unfold Always_pos.
  subst. simpl. lia.
Qed.  

Lemma proof_of_Always_positive_return_wit_4 : Always_positive_return_wit_4.
Proof.
  pre_process.
  entailer!.
  unfold Always_pos.
  destruct (Z.eq_dec a_pre 0) ; try lia.
  destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0) ; try nia.
Qed. 

Lemma proof_of_Always_positive_return_wit_3 : Always_positive_return_wit_3.
Proof.
  pre_process.
  entailer!. unfold Always_pos.
  subst.
  destruct (Z.eq_dec a_pre 0); try lia.
  destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0); try nia.
Qed.

Lemma proof_of_Always_positive_return_wit_2 : Always_positive_return_wit_2.
Proof.
  pre_process.
  entailer!. unfold Always_pos.
  subst.
  destruct (Z.eq_dec a_pre 0); try lia.
  destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0); try nia.
  destruct (Z_gt_le_dec a_pre 0); try lia.
Qed.  

Lemma proof_of_Always_positive_return_wit_1 : Always_positive_return_wit_1.
Proof.
  pre_process.
  entailer!. unfold Always_pos.
  subst.
  destruct (Z.eq_dec a_pre 0); try lia.
  destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0); try nia.
  destruct (Z_gt_le_dec a_pre 0); try lia.
Qed.