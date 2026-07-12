Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import test_prime_goal.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import test_prime_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib.
Local Open Scope sac.

Lemma proof_of_test_prime_entail_wit_1 : test_prime_entail_wit_1.
Proof.
  left.
  pre_process.
  entailer!.
  apply no_factor_between_empty; lia.
Qed.

Lemma proof_of_test_prime_entail_wit_2 : test_prime_entail_wit_2.
Proof.
  left.
  pre_process.
  entailer!.
  apply no_factor_between_snoc; try lia; auto.
Qed.

Lemma proof_of_test_prime_return_wit_1 : test_prime_return_wit_1.
Proof.
  pre_process.
  entailer!.
  apply prime_of_no_factor_from_2; try lia.
  replace d with x_pre in PreH6 by lia.
  exact PreH6.
Qed.

Lemma proof_of_test_prime_return_wit_2 : test_prime_return_wit_2.
Proof.
  pre_process.
  entailer!.
  apply not_prime_of_mod_factor with (d := d); lia.
Qed.

Lemma proof_of_test_prime_return_wit_3 : test_prime_return_wit_3.
Proof.
  pre_process.
  entailer!.
  apply not_prime_lt_2; lia.
Qed.

Lemma proof_of_test_prime_sqrt_entail_wit_1 : test_prime_sqrt_entail_wit_1.
Proof.
  left.
  pre_process.
  entailer!.
  apply no_factor_between_empty; lia.
Qed.

Lemma proof_of_test_prime_sqrt_entail_wit_2 : test_prime_sqrt_entail_wit_2.
Proof.
  left.
  pre_process.
  entailer!.
  apply no_factor_between_snoc; try lia; auto.
Qed.

Lemma proof_of_test_prime_sqrt_return_wit_1 : test_prime_sqrt_return_wit_1.
Proof.
  pre_process.
  entailer!.
  apply prime_of_no_factor_before_square with (d := d).
  - lia.
  - lia.
  - nia.
  - exact PreH6.
Qed.

Lemma proof_of_test_prime_sqrt_return_wit_2 : test_prime_sqrt_return_wit_2.
Proof.
  pre_process.
  entailer!.
  apply not_prime_of_mod_factor with (d := d); try lia.
  nia.
Qed.

Lemma proof_of_test_prime_sqrt_return_wit_3 : test_prime_sqrt_return_wit_3.
Proof.
  pre_process.
  entailer!.
  apply not_prime_lt_2; lia.
Qed.
