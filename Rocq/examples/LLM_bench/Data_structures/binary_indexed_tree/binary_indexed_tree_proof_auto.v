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
From SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree Require Import binary_indexed_tree_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_lib.
Local Open Scope sac.

Lemma proof_of_lowbit_safety_wit_1 : lowbit_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_add_partial_solve_wit_1 : add_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_add_partial_solve_wit_2 : add_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_add_partial_solve_wit_3_pure : add_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_add_partial_solve_wit_3 : add_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_query_safety_wit_1 : query_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_query_safety_wit_2 : query_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_query_partial_solve_wit_1 : query_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_query_partial_solve_wit_2_pure : query_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_query_partial_solve_wit_2 : query_partial_solve_wit_2.
Proof. Admitted. 

