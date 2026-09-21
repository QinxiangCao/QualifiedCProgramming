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
From SimpleC.EE.LLM_bench.Algorithms.Kruskal Require Import kruskal_union_find_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope monad.
Require Import SimpleC.EE.LLM_bench.Algorithms.Kruskal.kruskal_union_find_lib.
Require Import ListLib.Base.Positional.
From SumLib Require Import ZRange.
Local Open Scope sac.

Lemma proof_of_swap_int_return_wit_1 : swap_int_return_wit_1.
Proof. Admitted. 

Lemma proof_of_swap_edge_partial_solve_wit_1 : swap_edge_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_swap_edge_partial_solve_wit_2 : swap_edge_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_swap_edge_partial_solve_wit_3 : swap_edge_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_swap_edge_partial_solve_wit_4 : swap_edge_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_swap_edge_partial_solve_wit_5 : swap_edge_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_swap_edge_partial_solve_wit_6 : swap_edge_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_partitionByWeight_safety_wit_1 : partitionByWeight_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_partitionByWeight_safety_wit_2 : partitionByWeight_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_partitionByWeight_safety_wit_3 : partitionByWeight_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_partitionByWeight_partial_solve_wit_1 : partitionByWeight_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_partitionByWeight_partial_solve_wit_2 : partitionByWeight_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_partitionByWeight_partial_solve_wit_3 : partitionByWeight_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_partitionByWeight_partial_solve_wit_4 : partitionByWeight_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_safety_wit_1 : quickByWeightRange_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_safety_wit_2 : quickByWeightRange_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_safety_wit_3 : quickByWeightRange_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_safety_wit_4 : quickByWeightRange_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_partial_solve_wit_1_pure : quickByWeightRange_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_partial_solve_wit_1 : quickByWeightRange_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_partial_solve_wit_2_pure : quickByWeightRange_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_partial_solve_wit_2 : quickByWeightRange_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_partial_solve_wit_3_pure : quickByWeightRange_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_quickByWeightRange_partial_solve_wit_3 : quickByWeightRange_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_quickByWeight_safety_wit_1 : quickByWeight_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_quickByWeight_safety_wit_2 : quickByWeight_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_quickByWeight_safety_wit_3 : quickByWeight_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_quickByWeight_safety_wit_4 : quickByWeight_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_quickByWeight_partial_solve_wit_1_pure : quickByWeight_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_quickByWeight_partial_solve_wit_1 : quickByWeight_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_1 : kruskal_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_2 : kruskal_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_3 : kruskal_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_4 : kruskal_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_5 : kruskal_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_6 : kruskal_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_7 : kruskal_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_8 : kruskal_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_9 : kruskal_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_10 : kruskal_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_11 : kruskal_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_kruskal_safety_wit_12 : kruskal_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_1_pure : kruskal_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_1 : kruskal_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_2_pure : kruskal_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_2 : kruskal_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_3_pure : kruskal_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_3 : kruskal_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_4_pure : kruskal_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_4 : kruskal_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_5_pure : kruskal_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_5 : kruskal_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_6 : kruskal_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_7 : kruskal_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_8 : kruskal_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_9 : kruskal_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_10 : kruskal_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_11 : kruskal_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_12 : kruskal_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_13 : kruskal_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_14_pure : kruskal_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_14 : kruskal_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_15 : kruskal_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_16 : kruskal_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_17 : kruskal_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_kruskal_partial_solve_wit_18 : kruskal_partial_solve_wit_18.
Proof. Admitted. 

