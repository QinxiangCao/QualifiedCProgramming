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
From SimpleC.EE.LLM_bench.Engineering.minisat Require Import vec_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import vec_lib.
Local Open Scope sac.

Lemma proof_of_veci_new_safety_wit_1 : veci_new_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_veci_new_safety_wit_2 : veci_new_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_veci_new_partial_solve_wit_1 : veci_new_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_veci_new_partial_solve_wit_2_pure : veci_new_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_veci_new_partial_solve_wit_2 : veci_new_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_veci_delete_partial_solve_wit_1 : veci_delete_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_veci_delete_partial_solve_wit_2_pure : veci_delete_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_veci_delete_partial_solve_wit_2 : veci_delete_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_veci_begin_partial_solve_wit_1 : veci_begin_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_veci_size_partial_solve_wit_1 : veci_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_veci_resize_partial_solve_wit_1 : veci_resize_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_veci_push_safety_wit_1 : veci_push_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_veci_push_safety_wit_2 : veci_push_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_veci_push_safety_wit_3 : veci_push_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_veci_push_safety_wit_4 : veci_push_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_veci_push_safety_wit_5 : veci_push_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_veci_push_entail_wit_1_1 : veci_push_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_veci_push_return_wit_1 : veci_push_return_wit_1.
Proof. Admitted. 

Lemma proof_of_veci_push_partial_solve_wit_1 : veci_push_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_veci_push_partial_solve_wit_2 : veci_push_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_veci_push_partial_solve_wit_3 : veci_push_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_veci_push_partial_solve_wit_4_pure : veci_push_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_veci_push_partial_solve_wit_4 : veci_push_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_vecp_new_safety_wit_1 : vecp_new_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_vecp_new_safety_wit_2 : vecp_new_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_vecp_new_partial_solve_wit_1 : vecp_new_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_vecp_new_partial_solve_wit_2_pure : vecp_new_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_vecp_new_partial_solve_wit_2 : vecp_new_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_vecp_delete_partial_solve_wit_1 : vecp_delete_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_vecp_delete_partial_solve_wit_2_pure : vecp_delete_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_vecp_delete_partial_solve_wit_2 : vecp_delete_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_vecp_begin_partial_solve_wit_1 : vecp_begin_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_vecp_size_partial_solve_wit_1 : vecp_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_vecp_resize_partial_solve_wit_1 : vecp_resize_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_vecp_push_safety_wit_1 : vecp_push_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_vecp_push_safety_wit_2 : vecp_push_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_vecp_push_safety_wit_3 : vecp_push_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_vecp_push_safety_wit_4 : vecp_push_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_vecp_push_safety_wit_5 : vecp_push_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_vecp_push_entail_wit_1_1 : vecp_push_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_vecp_push_return_wit_1 : vecp_push_return_wit_1.
Proof. Admitted. 

Lemma proof_of_vecp_push_partial_solve_wit_1 : vecp_push_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_vecp_push_partial_solve_wit_2 : vecp_push_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_vecp_push_partial_solve_wit_3 : vecp_push_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_vecp_push_partial_solve_wit_4_pure : vecp_push_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_vecp_push_partial_solve_wit_4 : vecp_push_partial_solve_wit_4.
Proof. Admitted. 

