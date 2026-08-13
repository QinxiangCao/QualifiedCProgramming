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
From SimpleC.EE.QCP_demos_LLM Require Import sll_auto_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_shape_lib.
Local Open Scope sac.

Lemma proof_of_sll_copy_safety_wit_1 : sll_copy_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_copy_safety_wit_2 : sll_copy_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_sll_copy_entail_wit_1 : sll_copy_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_copy_entail_wit_2 : sll_copy_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_sll_copy_return_wit_1 : sll_copy_return_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_copy_return_wit_2 : sll_copy_return_wit_2.
Proof. Admitted. 

Lemma proof_of_sll_copy_partial_solve_wit_1 : sll_copy_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_copy_partial_solve_wit_2_pure : sll_copy_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_sll_copy_partial_solve_wit_2 : sll_copy_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_sll_copy_partial_solve_wit_3 : sll_copy_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_sll_copy_partial_solve_wit_4_pure : sll_copy_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_sll_copy_partial_solve_wit_4 : sll_copy_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_sll_free_entail_wit_1 : sll_free_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_free_entail_wit_2 : sll_free_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_sll_free_return_wit_1 : sll_free_return_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_free_partial_solve_wit_1 : sll_free_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_sll_free_partial_solve_wit_2 : sll_free_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Proof. Admitted. 

Lemma proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_append_safety_wit_1 : append_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_append_entail_wit_1 : append_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_append_entail_wit_2 : append_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_append_return_wit_1 : append_return_wit_1.
Proof. Admitted. 

Lemma proof_of_append_return_wit_2 : append_return_wit_2.
Proof. Admitted. 

Lemma proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_safety_wit_1 : merge_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_safety_wit_2 : merge_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_entail_wit_2 : merge_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_return_wit_1 : merge_return_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_return_wit_2 : merge_return_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_return_wit_3 : merge_return_wit_3.
Proof. Admitted. 

Lemma proof_of_merge_partial_solve_wit_1 : merge_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_partial_solve_wit_2 : merge_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_append_safety_wit_1 : multi_append_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_append_entail_wit_1 : multi_append_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_append_entail_wit_2 : multi_append_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_append_return_wit_1 : multi_append_return_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_append_return_wit_2 : multi_append_return_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_append_return_wit_3 : multi_append_return_wit_3.
Proof. Admitted. 

Lemma proof_of_multi_append_partial_solve_wit_1 : multi_append_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_append_partial_solve_wit_2 : multi_append_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_append_partial_solve_wit_3 : multi_append_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_multi_append_partial_solve_wit_4 : multi_append_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_multi_append_partial_solve_wit_5 : multi_append_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_multi_append_partial_solve_wit_6 : multi_append_partial_solve_wit_6.
Proof. Admitted. 

