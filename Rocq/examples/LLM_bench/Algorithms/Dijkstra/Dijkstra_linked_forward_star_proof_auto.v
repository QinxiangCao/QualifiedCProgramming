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
From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Import Dijkstra_linked_forward_star_goal.
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
Require Import Algorithms.Dijkstra.Dijkstra.
Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_lib.
Import DijkstraGraph.
Import DijkstraLinkedForwardStar.
Local Open Scope sac.

Lemma proof_of_dijkstra_linked_forward_star_init_safety_wit_1 : dijkstra_linked_forward_star_init_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_init_safety_wit_2 : dijkstra_linked_forward_star_init_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_init_safety_wit_3 : dijkstra_linked_forward_star_init_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_init_safety_wit_4 : dijkstra_linked_forward_star_init_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_init_safety_wit_5 : dijkstra_linked_forward_star_init_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_init_partial_solve_wit_1 : dijkstra_linked_forward_star_init_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_init_partial_solve_wit_2 : dijkstra_linked_forward_star_init_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_1 : dijkstra_linked_forward_star_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_2 : dijkstra_linked_forward_star_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_3 : dijkstra_linked_forward_star_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_4 : dijkstra_linked_forward_star_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_5 : dijkstra_linked_forward_star_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_6 : dijkstra_linked_forward_star_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_7 : dijkstra_linked_forward_star_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_8 : dijkstra_linked_forward_star_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_9 : dijkstra_linked_forward_star_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_10 : dijkstra_linked_forward_star_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_11 : dijkstra_linked_forward_star_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_12 : dijkstra_linked_forward_star_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_13 : dijkstra_linked_forward_star_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_safety_wit_14 : dijkstra_linked_forward_star_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_1 : dijkstra_linked_forward_star_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_1 : dijkstra_linked_forward_star_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_2_pure : dijkstra_linked_forward_star_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_2 : dijkstra_linked_forward_star_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_3 : dijkstra_linked_forward_star_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_4_pure : dijkstra_linked_forward_star_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_4 : dijkstra_linked_forward_star_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_5 : dijkstra_linked_forward_star_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_6 : dijkstra_linked_forward_star_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_7 : dijkstra_linked_forward_star_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_8 : dijkstra_linked_forward_star_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_9 : dijkstra_linked_forward_star_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_10 : dijkstra_linked_forward_star_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_11 : dijkstra_linked_forward_star_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_12 : dijkstra_linked_forward_star_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_13 : dijkstra_linked_forward_star_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_14 : dijkstra_linked_forward_star_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_15 : dijkstra_linked_forward_star_partial_solve_wit_15.
Proof. Admitted. 

