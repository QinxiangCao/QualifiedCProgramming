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
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
Require Import Algorithms.Floyd.Floyd.
Require Import SimpleC.EE.LLM_bench.Algorithms.Floyd.Floyd_adjacency_matrix_lib.
Import FloydGraph.
Import FloydAdjacencyMatrix2Darray.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import graph_matrix_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import graph_matrix_strategy_proof.

(*----- Function floyd_adjacency_matrix_ptr -----*)

Definition floyd_adjacency_matrix_ptr_safety_wit_1 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist0_low_level_spec)) (FloydAdjacencyMatrix2Darray.floyd_indexed_program (g_low_level_spec) (n_pre)) X_low_level_spec )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (GraphMatrixPtr.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_low_level_spec)) dist_pre dist0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_2 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_3 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_i __default__List_Z) 0)) /\ ((Znth c (Znth r dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_4 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH19 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH20 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH21 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH22 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH23 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_5 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dik < 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH19 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH20 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH21 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH22 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH23 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_6 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dkj < 1000000000)) (PreH2 : (dik < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= k)) (PreH9 : (k < 10)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < 10)) (PreH14 : (0 <= j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= j)) (PreH17 : (j < 10)) (PreH18 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH19 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH20 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH22 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH23 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ ((dik + dkj ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (dik + dkj )) ”
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dkj < 1000000000)) (PreH2 : (dik < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= k)) (PreH9 : (k < 10)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < 10)) (PreH14 : (0 <= j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= j)) (PreH17 : (j < 10)) (PreH18 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH19 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH20 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH22 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH23 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ ((dik + dkj ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (dik + dkj )) ”
).

Definition floyd_adjacency_matrix_ptr_safety_wit_6_split_goal_1 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dkj < 1000000000)) (PreH2 : (dik < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= k)) (PreH9 : (k < 10)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < 10)) (PreH14 : (0 <= j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= j)) (PreH17 : (j < 10)) (PreH18 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH19 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH20 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH22 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH23 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ ((dik + dkj ) <= INT_MAX) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_6_split_goal_2 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dkj < 1000000000)) (PreH2 : (dik < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= k)) (PreH9 : (k < 10)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < 10)) (PreH14 : (0 <= j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= j)) (PreH17 : (j < 10)) (PreH18 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH19 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH20 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH22 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH23 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ ((INT_MIN) <= (dik + dkj )) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_7 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH19 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH20 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH21 : (dik < 1000000000)) (PreH22 : (dkj < 1000000000)) (PreH23 : ((dik + dkj ) < dij)) (PreH24 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_i_ptr dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ ((dik + dkj ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (dik + dkj )) ”
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH19 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH20 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH21 : (dik < 1000000000)) (PreH22 : (dkj < 1000000000)) (PreH23 : ((dik + dkj ) < dij)) (PreH24 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_i_ptr dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ ((dik + dkj ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (dik + dkj )) ”
).

Definition floyd_adjacency_matrix_ptr_safety_wit_7_split_goal_1 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH19 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH20 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH21 : (dik < 1000000000)) (PreH22 : (dkj < 1000000000)) (PreH23 : ((dik + dkj ) < dij)) (PreH24 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_i_ptr dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ ((dik + dkj ) <= INT_MAX) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_7_split_goal_2 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH19 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH20 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH21 : (dik < 1000000000)) (PreH22 : (dkj < 1000000000)) (PreH23 : ((dik + dkj ) < dij)) (PreH24 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_i_ptr dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ ((INT_MIN) <= (dik + dkj )) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_8 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH19 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH20 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH21 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH22 : (dik < 1000000000)) (PreH23 : (dkj < 1000000000)) (PreH24 : ((dik + dkj ) < dij)) (PreH25 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH26 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH28 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntPtrArray2.full dist_pre 10 (replace_Znth (i) ((replace_Znth (j) ((dik + dkj )) ((Znth i dist_j __default__List_Z)))) (dist_j)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_9 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dkj >= 1000000000)) (PreH2 : (dik < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= k)) (PreH9 : (k < 10)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < 10)) (PreH14 : (0 <= j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= j)) (PreH17 : (j < 10)) (PreH18 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH19 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH20 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH22 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH23 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_10 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dik >= 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH19 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH20 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH21 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH22 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH23 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_11 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : ((dik + dkj ) >= dij)) (PreH2 : (dkj < 1000000000)) (PreH3 : (dik < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= k)) (PreH10 : (k < 10)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < 10)) (PreH15 : (0 <= j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= j)) (PreH18 : (j < 10)) (PreH19 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH20 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH21 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH22 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH23 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH24 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_12 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition floyd_adjacency_matrix_ptr_safety_wit_13 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_i __default__List_Z) 0)) /\ ((Znth c (Znth r dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition floyd_adjacency_matrix_ptr_entail_wit_1 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list (@list Z))) (g_low_level_spec: G)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist0_low_level_spec)) (FloydAdjacencyMatrix2Darray.floyd_indexed_program (g_low_level_spec) (n_pre)) X_low_level_spec )) ,
  (GraphMatrixPtr.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_low_level_spec)) dist_pre dist0_low_level_spec )
|--
  EX (dist_k: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (0)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_k ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list (@list Z))) (g_low_level_spec: G)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist0_low_level_spec)) (FloydAdjacencyMatrix2Darray.floyd_indexed_program (g_low_level_spec) (n_pre)) X_low_level_spec )) ,
  (GraphMatrixPtr.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_low_level_spec)) dist_pre dist0_low_level_spec )
|--
  EX (dist_k: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (0)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_k ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
).

Definition floyd_adjacency_matrix_ptr_entail_wit_2 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_k __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
|--
  EX (dist_i: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_i __default__List_Z) 0)) /\ ((Znth c (Znth r dist_i __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (0)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_i ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_k __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (0)) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_ptr_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_k __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (0)) X_low_level_spec )
.

Definition floyd_adjacency_matrix_ptr_entail_wit_3 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (0)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (0)) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_ptr_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (0)) X_low_level_spec )
.

Definition floyd_adjacency_matrix_ptr_entail_wit_4 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z) (row_ptr: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = row_ptr)) (PreH2 : (j < n_pre)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH13 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre k row_ptr dist_j_2 )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth k dist_j __default__List_Z)))) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre k retval dist_j )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z) (row_ptr: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = row_ptr)) (PreH2 : (j < n_pre)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH13 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  TT && emp 
|--
  “ (j < (Zlength ((Znth k dist_j_2 __default__List_Z)))) ” 
  &&  “ ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10) ”
  &&  emp
).

Definition floyd_adjacency_matrix_ptr_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z) (row_ptr: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = row_ptr)) (PreH2 : (j < n_pre)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH13 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (j < (Zlength ((Znth k dist_j_2 __default__List_Z))))
.

Definition floyd_adjacency_matrix_ptr_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z) (row_ptr: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = row_ptr)) (PreH2 : (j < n_pre)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH13 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)
.

Definition floyd_adjacency_matrix_ptr_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z) (row_ptr: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = row_ptr)) (PreH2 : (j < n_pre)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH13 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)
.

Definition floyd_adjacency_matrix_ptr_entail_wit_5 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH19 : (0 <= j)) (PreH20 : (j < (Zlength ((Znth k dist_j __default__List_Z))))) (PreH21 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH22 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH23 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntPtrArray2.full dist_pre 10 (replace_Znth (k) ((replace_Znth (j) ((Znth (j) ((Znth k dist_j __default__List_Z)) (0))) ((Znth k dist_j __default__List_Z)))) (dist_j)) )
|--
  EX (dist_j_2: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < (Zlength ((Znth i dist_j_2 __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j_2 __default__List_Z)))) ” 
  &&  “ ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) = (Znth j (Znth k dist_j_2 __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j_2 )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH19 : (0 <= j)) (PreH20 : (j < (Zlength ((Znth k dist_j __default__List_Z))))) (PreH21 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH22 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH23 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntPtrArray2.full dist_pre 10 (replace_Znth (k) ((replace_Znth (j) ((Znth (j) ((Znth k dist_j __default__List_Z)) (0))) ((Znth k dist_j __default__List_Z)))) (dist_j)) )
|--
  EX (dist_j_2: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < (Zlength ((Znth i dist_j_2 __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j_2 __default__List_Z)))) ” 
  &&  “ ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) = (Znth j (Znth k dist_j_2 __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j_2 )
).

Definition floyd_adjacency_matrix_ptr_entail_wit_6 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (row_ptr: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = row_ptr)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH19 : (0 <= k)) (PreH20 : (k < (Zlength ((Znth i dist_j_2 __default__List_Z))))) (PreH21 : (0 <= j)) (PreH22 : (j < (Zlength ((Znth i dist_j_2 __default__List_Z))))) (PreH23 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH24 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_ptr dist_j_2 )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < (Zlength ((Znth i dist_j __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j __default__List_Z)))) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i retval dist_j )
.

Definition floyd_adjacency_matrix_ptr_entail_wit_7 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH19 : (0 <= k)) (PreH20 : (k < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH21 : (0 <= j)) (PreH22 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH23 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH24 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntPtrArray2.full dist_pre 10 (replace_Znth (i) ((replace_Znth (k) ((Znth (k) ((Znth i dist_j __default__List_Z)) (0))) ((Znth i dist_j __default__List_Z)))) (dist_j)) )
|--
  EX (dist_j_2: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j_2 __default__List_Z)))) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) = (Znth k (Znth i dist_j_2 __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j_2 )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH19 : (0 <= k)) (PreH20 : (k < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH21 : (0 <= j)) (PreH22 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH23 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH24 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntPtrArray2.full dist_pre 10 (replace_Znth (i) ((replace_Znth (k) ((Znth (k) ((Znth i dist_j __default__List_Z)) (0))) ((Znth i dist_j __default__List_Z)))) (dist_j)) )
|--
  EX (dist_j_2: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j_2 __default__List_Z)))) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) = (Znth k (Znth i dist_j_2 __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j_2 )
).

Definition floyd_adjacency_matrix_ptr_entail_wit_8 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (row_ptr: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = row_ptr)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH19 : (0 <= j)) (PreH20 : (j < (Zlength ((Znth i dist_j_2 __default__List_Z))))) (PreH21 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH22 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH23 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_ptr dist_j_2 )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j __default__List_Z)))) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j __default__List_Z) 0)) ” 
  &&  “ (dik = (Znth k (Znth i dist_j __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i retval dist_j )
.

Definition floyd_adjacency_matrix_ptr_entail_wit_9 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH19 : (0 <= j)) (PreH20 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH21 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH22 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH23 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntPtrArray2.full dist_pre 10 (replace_Znth (i) ((replace_Znth (j) ((Znth (j) ((Znth i dist_j __default__List_Z)) (0))) ((Znth i dist_j __default__List_Z)))) (dist_j)) )
|--
  EX (dist_j_2: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0)) ” 
  &&  “ (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth (j) ((Znth i dist_j __default__List_Z)) (0)) = (Znth j (Znth i dist_j_2 __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j_2 )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH19 : (0 <= j)) (PreH20 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH21 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH22 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH23 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntPtrArray2.full dist_pre 10 (replace_Znth (i) ((replace_Znth (j) ((Znth (j) ((Znth i dist_j __default__List_Z)) (0))) ((Znth i dist_j __default__List_Z)))) (dist_j)) )
|--
  EX (dist_j_2: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0)) ” 
  &&  “ (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth (j) ((Znth i dist_j __default__List_Z)) (0)) = (Znth j (Znth i dist_j_2 __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j_2 )
).

Definition floyd_adjacency_matrix_ptr_entail_wit_10 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z) (row_ptr: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = row_ptr)) (PreH2 : ((dik + dkj ) < dij)) (PreH3 : (dkj < 1000000000)) (PreH4 : (dik < 1000000000)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k < 10)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < 10)) (PreH16 : (0 <= j)) (PreH17 : (j < n_pre)) (PreH18 : (0 <= j)) (PreH19 : (j < 10)) (PreH20 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH21 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH22 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH23 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH24 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH25 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH26 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH28 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_ptr dist_j_2 )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j __default__List_Z) 0)) ” 
  &&  “ (dik = (Znth k (Znth i dist_j __default__List_Z) 0)) ” 
  &&  “ (dij = (Znth j (Znth i dist_j __default__List_Z) 0)) ” 
  &&  “ (dik < 1000000000) ” 
  &&  “ (dkj < 1000000000) ” 
  &&  “ ((dik + dkj ) < dij) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i retval dist_j )
.

Definition floyd_adjacency_matrix_ptr_entail_wit_11_1 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH19 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH20 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH21 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH22 : (dik < 1000000000)) (PreH23 : (dkj < 1000000000)) (PreH24 : ((dik + dkj ) < dij)) (PreH25 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH26 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH28 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntPtrArray2.full dist_pre 10 (replace_Znth (i) ((replace_Znth (j) ((dik + dkj )) ((Znth i dist_j_2 __default__List_Z)))) (dist_j_2)) )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH19 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH20 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH21 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH22 : (dik < 1000000000)) (PreH23 : (dkj < 1000000000)) (PreH24 : ((dik + dkj ) < dij)) (PreH25 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH26 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH28 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntPtrArray2.full dist_pre 10 (replace_Znth (i) ((replace_Znth (j) ((dik + dkj )) ((Znth i dist_j_2 __default__List_Z)))) (dist_j_2)) )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
).

Definition floyd_adjacency_matrix_ptr_entail_wit_11_2 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dkj >= 1000000000)) (PreH2 : (dik < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= k)) (PreH9 : (k < 10)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < 10)) (PreH14 : (0 <= j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= j)) (PreH17 : (j < 10)) (PreH18 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH19 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH20 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH22 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH23 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j_2 )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dkj >= 1000000000)) (PreH2 : (dik < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= k)) (PreH9 : (k < 10)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < 10)) (PreH14 : (0 <= j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= j)) (PreH17 : (j < 10)) (PreH18 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH19 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH20 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH22 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH23 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_ptr_entail_wit_11_2_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dkj >= 1000000000)) (PreH2 : (dik < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= k)) (PreH9 : (k < 10)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < 10)) (PreH14 : (0 <= j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= j)) (PreH17 : (j < 10)) (PreH18 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH19 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH20 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH22 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH23 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec )
.

Definition floyd_adjacency_matrix_ptr_entail_wit_11_3 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dik >= 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH19 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH20 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH21 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH22 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH23 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j_2 )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dik >= 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH19 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH20 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH21 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH22 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH23 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_ptr_entail_wit_11_3_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (dik >= 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k < 10)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < 10)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < 10)) (PreH17 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH18 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH19 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH20 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH21 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH22 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH23 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec )
.

Definition floyd_adjacency_matrix_ptr_entail_wit_11_4 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : ((dik + dkj ) >= dij)) (PreH2 : (dkj < 1000000000)) (PreH3 : (dik < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= k)) (PreH10 : (k < 10)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < 10)) (PreH15 : (0 <= j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= j)) (PreH18 : (j < 10)) (PreH19 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH20 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH21 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH22 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH23 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH24 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j_2 )
|--
  EX (dist_j: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : ((dik + dkj ) >= dij)) (PreH2 : (dkj < 1000000000)) (PreH3 : (dik < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= k)) (PreH10 : (k < 10)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < 10)) (PreH15 : (0 <= j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= j)) (PreH18 : (j < 10)) (PreH19 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH20 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH21 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH22 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH23 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH24 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_ptr_entail_wit_11_4_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : ((dik + dkj ) >= dij)) (PreH2 : (dkj < 1000000000)) (PreH3 : (dik < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= k)) (PreH10 : (k < 10)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < 10)) (PreH15 : (0 <= j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= j)) (PreH18 : (j < 10)) (PreH19 : ((Zlength ((Znth i dist_j_2 __default__List_Z))) = 10)) (PreH20 : ((Zlength ((Znth k dist_j_2 __default__List_Z))) = 10)) (PreH21 : (dkj = (Znth j (Znth k dist_j_2 __default__List_Z) 0))) (PreH22 : (dik = (Znth k (Znth i dist_j_2 __default__List_Z) 0))) (PreH23 : (dij = (Znth j (Znth i dist_j_2 __default__List_Z) 0))) (PreH24 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) ((j + 1 ))) X_low_level_spec )
.

Definition floyd_adjacency_matrix_ptr_entail_wit_12 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  EX (dist_i: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_i __default__List_Z) 0)) /\ ((Znth c (Znth r dist_i __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_i ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) ((i + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_ptr_entail_wit_12_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) ((i + 1 ))) X_low_level_spec )
.

Definition floyd_adjacency_matrix_ptr_entail_wit_13 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
|--
  EX (dist_k: (@list (@list Z))) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) ((k + 1 ))) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_k ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
  **  ((( &( "i" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) ((k + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_ptr_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) ((k + 1 ))) X_low_level_spec )
.

Definition floyd_adjacency_matrix_ptr_return_wit_1 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
|--
  EX (dist1: (@list (@list Z))) ,
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist1)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist1 )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_ptr_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (return (tt)) X_low_level_spec )
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_1_pure := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "dij" ) )) # Int  |->_)
  **  ((( &( "dik" ) )) # Int  |->_)
  **  ((( &( "dkj" ) )) # Int  |->_)
  **  ((( &( "row_i" ) )) # Ptr  |->_)
  **  ((( &( "row_k" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ (0 <= k) ” 
  &&  “ (k < 10) ”
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_1_aux := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_1 := floyd_adjacency_matrix_ptr_partial_solve_wit_1_pure -> floyd_adjacency_matrix_ptr_partial_solve_wit_1_aux.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_2 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (k: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (0 <= j)) (PreH19 : (j < (Zlength ((Znth k dist_j __default__List_Z))))) (PreH20 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH21 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH22 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH23 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre k row_k_ptr dist_j )
|--
  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth k dist_j __default__List_Z)))) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (((row_k_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth k dist_j __default__List_Z)) (0)))
  **  (IntPtrArray2.missing_i dist_pre 10 k row_k_ptr dist_j )
  **  (IntArray.missing_i row_k_ptr j 0 (Zlength ((Znth k dist_j __default__List_Z))) (Znth k dist_j __default__List_Z) )
  **  (((dist_pre + (k * sizeof(PTR)))) # Ptr  |-> row_k_ptr)
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_3_pure := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (0 <= k)) (PreH19 : (k < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH20 : (0 <= j)) (PreH21 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH22 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH23 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |->_)
  **  ((( &( "dik" ) )) # Int  |->_)
  **  ((( &( "dij" ) )) # Int  |->_)
|--
  “ (0 <= i) ” 
  &&  “ (i < 10) ”
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_3_aux := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (0 <= k)) (PreH19 : (k < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH20 : (0 <= j)) (PreH21 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH22 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH23 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < (Zlength ((Znth i dist_j __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j __default__List_Z)))) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_3 := floyd_adjacency_matrix_ptr_partial_solve_wit_3_pure -> floyd_adjacency_matrix_ptr_partial_solve_wit_3_aux.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_4 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (0 <= k)) (PreH19 : (k < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH20 : (0 <= j)) (PreH21 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH22 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH23 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH24 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_i_ptr dist_j )
|--
  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < (Zlength ((Znth i dist_j __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j __default__List_Z)))) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (((row_i_ptr + (k * sizeof(INT)))) # Int  |-> (Znth (k) ((Znth i dist_j __default__List_Z)) (0)))
  **  (IntPtrArray2.missing_i dist_pre 10 i row_i_ptr dist_j )
  **  (IntArray.missing_i row_i_ptr k 0 (Zlength ((Znth i dist_j __default__List_Z))) (Znth i dist_j __default__List_Z) )
  **  (((dist_pre + (i * sizeof(PTR)))) # Ptr  |-> row_i_ptr)
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_5_pure := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (0 <= j)) (PreH19 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH20 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH22 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH23 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
  **  ((( &( "dij" ) )) # Int  |->_)
|--
  “ (0 <= i) ” 
  &&  “ (i < 10) ”
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_5_aux := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (0 <= j)) (PreH19 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH20 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH22 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH23 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j __default__List_Z)))) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j __default__List_Z) 0)) ” 
  &&  “ (dik = (Znth k (Znth i dist_j __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_5 := floyd_adjacency_matrix_ptr_partial_solve_wit_5_pure -> floyd_adjacency_matrix_ptr_partial_solve_wit_5_aux.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_6 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (0 <= j)) (PreH19 : (j < (Zlength ((Znth i dist_j __default__List_Z))))) (PreH20 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH21 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH22 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH23 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH24 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH25 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_i_ptr dist_j )
|--
  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth i dist_j __default__List_Z)))) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j __default__List_Z) 0)) ” 
  &&  “ (dik = (Znth k (Znth i dist_j __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (((row_i_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))
  **  (IntPtrArray2.missing_i dist_pre 10 i row_i_ptr dist_j )
  **  (IntArray.missing_i row_i_ptr j 0 (Zlength ((Znth i dist_j __default__List_Z))) (Znth i dist_j __default__List_Z) )
  **  (((dist_pre + (i * sizeof(PTR)))) # Ptr  |-> row_i_ptr)
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_7_pure := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_k_ptr: Z) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : ((dik + dkj ) < dij)) (PreH2 : (dkj < 1000000000)) (PreH3 : (dik < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= k)) (PreH10 : (k < 10)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < 10)) (PreH15 : (0 <= j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= j)) (PreH18 : (j < 10)) (PreH19 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH20 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH21 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH22 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH23 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH24 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dkj" ) )) # Int  |-> dkj)
  **  ((( &( "dik" ) )) # Int  |-> dik)
  **  ((( &( "dij" ) )) # Int  |-> dij)
  **  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
  **  ((( &( "row_k" ) )) # Ptr  |-> row_k_ptr)
  **  ((( &( "row_i" ) )) # Ptr  |-> row_i_ptr)
|--
  “ (0 <= i) ” 
  &&  “ (i < 10) ”
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_7_aux := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : ((dik + dkj ) < dij)) (PreH2 : (dkj < 1000000000)) (PreH3 : (dik < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= k)) (PreH10 : (k < 10)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < 10)) (PreH15 : (0 <= j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= j)) (PreH18 : (j < 10)) (PreH19 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH20 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH21 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH22 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH23 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH24 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ ((dik + dkj ) < dij) ” 
  &&  “ (dkj < 1000000000) ” 
  &&  “ (dik < 1000000000) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j __default__List_Z) 0)) ” 
  &&  “ (dik = (Znth k (Znth i dist_j __default__List_Z) 0)) ” 
  &&  “ (dij = (Znth j (Znth i dist_j __default__List_Z) 0)) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_7 := floyd_adjacency_matrix_ptr_partial_solve_wit_7_pure -> floyd_adjacency_matrix_ptr_partial_solve_wit_7_aux.

Definition floyd_adjacency_matrix_ptr_partial_solve_wit_8 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (row_i_ptr: Z) (k: Z) (i: Z) (j: Z) (dkj: Z) (dik: Z) (dij: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (0 <= k)) (PreH5 : (k < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k < 10)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < 10)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < 10)) (PreH16 : ((Zlength ((Znth i dist_j __default__List_Z))) = 10)) (PreH17 : ((Zlength ((Znth k dist_j __default__List_Z))) = 10)) (PreH18 : (dkj = (Znth j (Znth k dist_j __default__List_Z) 0))) (PreH19 : (dik = (Znth k (Znth i dist_j __default__List_Z) 0))) (PreH20 : (dij = (Znth j (Znth i dist_j __default__List_Z) 0))) (PreH21 : (dik < 1000000000)) (PreH22 : (dkj < 1000000000)) (PreH23 : ((dik + dkj ) < dij)) (PreH24 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH25 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH26 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH27 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (GraphMatrixPtr.row_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre i row_i_ptr dist_j )
|--
  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ ((Zlength ((Znth i dist_j __default__List_Z))) = 10) ” 
  &&  “ ((Zlength ((Znth k dist_j __default__List_Z))) = 10) ” 
  &&  “ (dkj = (Znth j (Znth k dist_j __default__List_Z) 0)) ” 
  &&  “ (dik = (Znth k (Znth i dist_j __default__List_Z) 0)) ” 
  &&  “ (dij = (Znth j (Znth i dist_j __default__List_Z) 0)) ” 
  &&  “ (dik < 1000000000) ” 
  &&  “ (dkj < 1000000000) ” 
  &&  “ ((dik + dkj ) < dij) ” 
  &&  “ forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000))) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_shape dist_j ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j ) ”
  &&  (((row_i_ptr + (j * sizeof(INT)))) # Int  |->_)
  **  (IntPtrArray2.missing_i dist_pre 10 i row_i_ptr dist_j )
  **  (IntArray.missing_i row_i_ptr j 0 (Zlength ((Znth i dist_j __default__List_Z))) (Znth i dist_j __default__List_Z) )
  **  (((dist_pre + (i * sizeof(PTR)))) # Ptr  |-> row_i_ptr)
.

Definition floyd_adjacency_matrix_ptr_derive_high_level_spec_by_low_level_spec := 
forall (dist_pre: Z) (n_pre: Z) (dist0_high_level_spec: (@list (@list Z))) (g_high_level_spec: G) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_high_level_spec n_pre ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.floyd_init_matrix g_high_level_spec dist0_high_level_spec ) ”
  &&  (GraphMatrixPtr.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_high_level_spec)) dist_pre dist0_high_level_spec )
|--
EX (g_low_level_spec: G) (dist0_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (state -> Prop))) ,
  (“ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist0_low_level_spec)) (FloydAdjacencyMatrix2Darray.floyd_indexed_program (g_low_level_spec) (n_pre)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_low_level_spec)) dist_pre dist0_low_level_spec ))
  **
  ((EX dist1_2,
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist1_2)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist1_2 ))
  -*
  (EX dist1,
  “ (FloydAdjacencyMatrix2Darray.floyd_shortest_matrix g_high_level_spec dist1 ) ”
  &&  (GraphMatrixPtr.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist1 )))
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.
Include array2_Strategy_Correct.
Include int_array_Strategy_Correct.
Include int_ptr_array2_Strategy_Correct.
Include graph_matrix_Strategy_Correct.

Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_1 : floyd_adjacency_matrix_ptr_safety_wit_1.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_2 : floyd_adjacency_matrix_ptr_safety_wit_2.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_3 : floyd_adjacency_matrix_ptr_safety_wit_3.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_4 : floyd_adjacency_matrix_ptr_safety_wit_4.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_5 : floyd_adjacency_matrix_ptr_safety_wit_5.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_6 : floyd_adjacency_matrix_ptr_safety_wit_6.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_7 : floyd_adjacency_matrix_ptr_safety_wit_7.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_8 : floyd_adjacency_matrix_ptr_safety_wit_8.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_9 : floyd_adjacency_matrix_ptr_safety_wit_9.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_10 : floyd_adjacency_matrix_ptr_safety_wit_10.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_11 : floyd_adjacency_matrix_ptr_safety_wit_11.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_12 : floyd_adjacency_matrix_ptr_safety_wit_12.
Axiom proof_of_floyd_adjacency_matrix_ptr_safety_wit_13 : floyd_adjacency_matrix_ptr_safety_wit_13.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_1 : floyd_adjacency_matrix_ptr_entail_wit_1.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_2 : floyd_adjacency_matrix_ptr_entail_wit_2.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_3 : floyd_adjacency_matrix_ptr_entail_wit_3.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_4 : floyd_adjacency_matrix_ptr_entail_wit_4.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_5 : floyd_adjacency_matrix_ptr_entail_wit_5.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_6 : floyd_adjacency_matrix_ptr_entail_wit_6.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_7 : floyd_adjacency_matrix_ptr_entail_wit_7.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_8 : floyd_adjacency_matrix_ptr_entail_wit_8.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_9 : floyd_adjacency_matrix_ptr_entail_wit_9.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_10 : floyd_adjacency_matrix_ptr_entail_wit_10.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_11_1 : floyd_adjacency_matrix_ptr_entail_wit_11_1.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_11_2 : floyd_adjacency_matrix_ptr_entail_wit_11_2.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_11_3 : floyd_adjacency_matrix_ptr_entail_wit_11_3.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_11_4 : floyd_adjacency_matrix_ptr_entail_wit_11_4.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_12 : floyd_adjacency_matrix_ptr_entail_wit_12.
Axiom proof_of_floyd_adjacency_matrix_ptr_entail_wit_13 : floyd_adjacency_matrix_ptr_entail_wit_13.
Axiom proof_of_floyd_adjacency_matrix_ptr_return_wit_1 : floyd_adjacency_matrix_ptr_return_wit_1.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_1_pure : floyd_adjacency_matrix_ptr_partial_solve_wit_1_pure.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_1 : floyd_adjacency_matrix_ptr_partial_solve_wit_1.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_2 : floyd_adjacency_matrix_ptr_partial_solve_wit_2.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_3_pure : floyd_adjacency_matrix_ptr_partial_solve_wit_3_pure.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_3 : floyd_adjacency_matrix_ptr_partial_solve_wit_3.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_4 : floyd_adjacency_matrix_ptr_partial_solve_wit_4.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_5_pure : floyd_adjacency_matrix_ptr_partial_solve_wit_5_pure.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_5 : floyd_adjacency_matrix_ptr_partial_solve_wit_5.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_6 : floyd_adjacency_matrix_ptr_partial_solve_wit_6.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_7_pure : floyd_adjacency_matrix_ptr_partial_solve_wit_7_pure.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_7 : floyd_adjacency_matrix_ptr_partial_solve_wit_7.
Axiom proof_of_floyd_adjacency_matrix_ptr_partial_solve_wit_8 : floyd_adjacency_matrix_ptr_partial_solve_wit_8.
Axiom proof_of_floyd_adjacency_matrix_ptr_derive_high_level_spec_by_low_level_spec : floyd_adjacency_matrix_ptr_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
