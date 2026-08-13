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
From SimpleC.EE.QCP_demos_LLM Require Import dll_auto_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.dll_shape_lib.
Local Open Scope sac.

Lemma proof_of_dll_copy_safety_wit_1 : dll_copy_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_dll_copy_safety_wit_2 : dll_copy_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_dll_copy_entail_wit_1 : dll_copy_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dll_copy_entail_wit_2 : dll_copy_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_dll_copy_return_wit_1 : dll_copy_return_wit_1.
Proof. Admitted. 

Lemma proof_of_dll_copy_return_wit_2 : dll_copy_return_wit_2.
Proof. Admitted. 

Lemma proof_of_dll_copy_partial_solve_wit_1 : dll_copy_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_dll_copy_partial_solve_wit_2_pure : dll_copy_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_dll_copy_partial_solve_wit_2 : dll_copy_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_dll_copy_partial_solve_wit_3 : dll_copy_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_dll_copy_partial_solve_wit_4_pure : dll_copy_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_dll_copy_partial_solve_wit_4 : dll_copy_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_dll_free_entail_wit_1 : dll_free_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dll_free_entail_wit_2 : dll_free_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_dll_free_return_wit_1 : dll_free_return_wit_1.
Proof. Admitted. 

Lemma proof_of_dll_free_partial_solve_wit_1 : dll_free_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_dll_free_partial_solve_wit_2 : dll_free_partial_solve_wit_2.
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

Lemma proof_of_append_return_wit_3 : append_return_wit_3.
Proof. Admitted. 

Lemma proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_append_partial_solve_wit_3 : append_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_iter_entail_wit_1 : iter_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_entail_wit_2 : iter_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_iter_return_wit_1 : iter_return_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_partial_solve_wit_1 : iter_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_back_safety_wit_1 : iter_back_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_back_entail_wit_1 : iter_back_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_back_entail_wit_2 : iter_back_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_iter_back_return_wit_1 : iter_back_return_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_back_return_wit_2 : iter_back_return_wit_2.
Proof. Admitted. 

Lemma proof_of_iter_back_2_entail_wit_1 : iter_back_2_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_back_2_entail_wit_2 : iter_back_2_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_iter_back_2_return_wit_1 : iter_back_2_return_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_back_2_return_wit_2 : iter_back_2_return_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_merge_safety_wit_1 : multi_merge_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_merge_safety_wit_2 : multi_merge_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_merge_safety_wit_3 : multi_merge_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_multi_merge_safety_wit_4 : multi_merge_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_multi_merge_entail_wit_1 : multi_merge_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_merge_entail_wit_2_1 : multi_merge_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_multi_merge_entail_wit_2_2 : multi_merge_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_multi_merge_entail_wit_2_3 : multi_merge_entail_wit_2_3.
Proof. Admitted. 

Lemma proof_of_multi_merge_entail_wit_2_4 : multi_merge_entail_wit_2_4.
Proof. Admitted. 

Lemma proof_of_multi_merge_return_wit_1 : multi_merge_return_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_merge_return_wit_2 : multi_merge_return_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_merge_return_wit_3 : multi_merge_return_wit_3.
Proof. Admitted. 

Lemma proof_of_multi_merge_return_wit_4 : multi_merge_return_wit_4.
Proof. Admitted. 

Lemma proof_of_multi_merge_return_wit_5 : multi_merge_return_wit_5.
Proof. Admitted. 

Lemma proof_of_multi_merge_return_wit_6 : multi_merge_return_wit_6.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_1 : multi_merge_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_2 : multi_merge_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_3 : multi_merge_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_4 : multi_merge_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_5 : multi_merge_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_6 : multi_merge_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_7 : multi_merge_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_8 : multi_merge_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_9 : multi_merge_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_10 : multi_merge_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_11 : multi_merge_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_12 : multi_merge_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_13 : multi_merge_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_multi_merge_partial_solve_wit_14 : multi_merge_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_multi_rev_safety_wit_1 : multi_rev_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_rev_safety_wit_2 : multi_rev_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_rev_safety_wit_3 : multi_rev_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_multi_rev_entail_wit_1 : multi_rev_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_rev_entail_wit_2_1 : multi_rev_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_multi_rev_entail_wit_2_2 : multi_rev_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_multi_rev_return_wit_1 : multi_rev_return_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_rev_partial_solve_wit_1 : multi_rev_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_multi_rev_partial_solve_wit_2 : multi_rev_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_multi_rev_partial_solve_wit_3 : multi_rev_partial_solve_wit_3.
Proof. Admitted. 

