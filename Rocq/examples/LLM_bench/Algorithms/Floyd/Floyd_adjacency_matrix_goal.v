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

(*----- Function floyd_adjacency_matrix -----*)

Definition floyd_adjacency_matrix_safety_wit_1 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist0_low_level_spec)) (FloydAdjacencyMatrix2Darray.floyd_indexed_program (g_low_level_spec) (n_pre)) X_low_level_spec )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (GraphMatrixFlat.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_low_level_spec)) dist_pre dist0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition floyd_adjacency_matrix_safety_wit_2 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition floyd_adjacency_matrix_safety_wit_3 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_i __default__List_Z) 0)) /\ ((Znth c (Znth r dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition floyd_adjacency_matrix_safety_wit_4 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ (((i * 10 ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 10 ) + k )) ”
.

Definition floyd_adjacency_matrix_safety_wit_5 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ ((i * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 10 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_6 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition floyd_adjacency_matrix_safety_wit_7 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH2 : (j < n_pre)) (PreH3 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH13 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition floyd_adjacency_matrix_safety_wit_8 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH3 : (j < n_pre)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH14 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((k * 10 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k * 10 ) + j )) ”
.

Definition floyd_adjacency_matrix_safety_wit_9 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH3 : (j < n_pre)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH14 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((k * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * 10 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_10 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH3 : (j < n_pre)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH14 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition floyd_adjacency_matrix_safety_wit_11 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH3 : (j < n_pre)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH14 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition floyd_adjacency_matrix_safety_wit_12 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((i * 10 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 10 ) + j )) ”
.

Definition floyd_adjacency_matrix_safety_wit_13 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 10 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_14 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) )) ”
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) )) ”
).

Definition floyd_adjacency_matrix_safety_wit_14_split_goal_1 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) <= INT_MAX) ”
.

Definition floyd_adjacency_matrix_safety_wit_14_split_goal_2 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((INT_MIN) <= ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) )) ”
.

Definition floyd_adjacency_matrix_safety_wit_15 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((k * 10 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k * 10 ) + j )) ”
.

Definition floyd_adjacency_matrix_safety_wit_16 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((k * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * 10 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_17 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((i * 10 ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 10 ) + k )) ”
.

Definition floyd_adjacency_matrix_safety_wit_18 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 10 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_19 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition floyd_adjacency_matrix_safety_wit_20 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition floyd_adjacency_matrix_safety_wit_21 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition floyd_adjacency_matrix_safety_wit_22 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((i * 10 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 10 ) + j )) ”
.

Definition floyd_adjacency_matrix_safety_wit_23 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 10 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_24 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition floyd_adjacency_matrix_safety_wit_25 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) )) ”
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) )) ”
).

Definition floyd_adjacency_matrix_safety_wit_25_split_goal_1 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) <= INT_MAX) ”
.

Definition floyd_adjacency_matrix_safety_wit_25_split_goal_2 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((INT_MIN) <= ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) )) ”
.

Definition floyd_adjacency_matrix_safety_wit_26 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((k * 10 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k * 10 ) + j )) ”
.

Definition floyd_adjacency_matrix_safety_wit_27 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((k * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * 10 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_28 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (((i * 10 ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 10 ) + k )) ”
.

Definition floyd_adjacency_matrix_safety_wit_29 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 10 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_30 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition floyd_adjacency_matrix_safety_wit_31 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition floyd_adjacency_matrix_safety_wit_32 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 (replace_Znth (i) ((replace_Znth (j) (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) )) ((Znth i dist_j __default__List_Z)))) (dist_j)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_33 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) >= 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_34 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) >= 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH3 : (j < n_pre)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH14 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_35 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) >= (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_36 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition floyd_adjacency_matrix_safety_wit_37 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_i __default__List_Z) 0)) /\ ((Znth c (Znth r dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition floyd_adjacency_matrix_entail_wit_1 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list (@list Z))) (g_low_level_spec: G)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist0_low_level_spec)) (FloydAdjacencyMatrix2Darray.floyd_indexed_program (g_low_level_spec) (n_pre)) X_low_level_spec )) ,
  (GraphMatrixFlat.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_low_level_spec)) dist_pre dist0_low_level_spec )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (dist0_low_level_spec: (@list (@list Z))) (g_low_level_spec: G)  __default__List_Z (PreH1 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH2 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist0_low_level_spec)) (FloydAdjacencyMatrix2Darray.floyd_indexed_program (g_low_level_spec) (n_pre)) X_low_level_spec )) ,
  (GraphMatrixFlat.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_low_level_spec)) dist_pre dist0_low_level_spec )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
).

Definition floyd_adjacency_matrix_entail_wit_2 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_k __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_k __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (0)) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_k __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (0)) X_low_level_spec )
.

Definition floyd_adjacency_matrix_entail_wit_3 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (0)) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (0)) X_low_level_spec )
.

Definition floyd_adjacency_matrix_entail_wit_4_1 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j_2 __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntArray2.full dist_pre 10 10 (replace_Znth (i) ((replace_Znth (j) (((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) )) ((Znth i dist_j_2 __default__List_Z)))) (dist_j_2)) )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j_2 __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntArray2.full dist_pre 10 10 (replace_Znth (i) ((replace_Znth (j) (((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) )) ((Znth i dist_j_2 __default__List_Z)))) (dist_j_2)) )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
).

Definition floyd_adjacency_matrix_entail_wit_4_2 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) >= 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntArray2.full dist_pre 10 10 dist_j_2 )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) >= 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntArray2.full dist_pre 10 10 dist_j_2 )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
).

Definition floyd_adjacency_matrix_entail_wit_4_3 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) >= 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH3 : (j < n_pre)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH14 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntArray2.full dist_pre 10 10 dist_j_2 )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) >= 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH3 : (j < n_pre)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH14 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntArray2.full dist_pre 10 10 dist_j_2 )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
).

Definition floyd_adjacency_matrix_entail_wit_4_4 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) ) >= (Znth (j) ((Znth i dist_j_2 __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntArray2.full dist_pre 10 10 dist_j_2 )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
) \/
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j_2: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) ) >= (Znth (j) ((Znth i dist_j_2 __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j_2 __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j_2 )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j_2 __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j_2 __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j_2)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j_2 )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j_2 )) ,
  (IntArray2.full dist_pre 10 10 dist_j_2 )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
).

Definition floyd_adjacency_matrix_entail_wit_5 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) ((i + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_j __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) ((i + 1 ))) X_low_level_spec )
.

Definition floyd_adjacency_matrix_entail_wit_6 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_i )
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
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
  **  ((( &( "i" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) ((k + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_i: (@list (@list Z))) (i: Z) (k: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (r_2: Z) , forall (c_2: Z) , (((((0 <= r_2) /\ (r_2 < 10)) /\ (0 <= c_2)) /\ (c_2 < 10)) -> ((0 <= (Znth c_2 (Znth r_2 dist_i __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_2 dist_i __default__List_Z) 0) <= 1000000000)))) (PreH10 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_i_k_from (g_low_level_spec) (n_pre) (k) (i)) X_low_level_spec )) (PreH11 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_i )) (PreH12 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_i )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_i)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) ((k + 1 ))) X_low_level_spec )
.

Definition floyd_adjacency_matrix_return_wit_1 := 
(
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_k )
|--
  EX (dist1: (@list (@list Z))) ,
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist1)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist1 )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  TT && emp 
|--
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition floyd_adjacency_matrix_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_k: (@list (@list Z))) (k: Z)  __default__List_Z (PreH1 : (k >= n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_k __default__List_Z) 0)) /\ ((Znth c (Znth r dist_k __default__List_Z) 0) <= 1000000000)))) (PreH8 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (FloydAdjacencyMatrix2Darray.floyd_k_from (g_low_level_spec) (n_pre) (k)) X_low_level_spec )) (PreH9 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_k )) (PreH10 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_k )) ,
  (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_k)) (return (tt)) X_low_level_spec )
.

Definition floyd_adjacency_matrix_partial_solve_wit_1 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (j < n_pre)) (PreH2 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 10)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= n_pre)) (PreH11 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH12 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH13 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH14 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist_j )
|--
  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
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
  &&  (((dist_pre + (((i * 10 ) + k ) * sizeof(INT)))) # Int  |-> (Znth (k) ((Znth i dist_j __default__List_Z)) (0)))
  **  (IntArray.missing_i (dist_pre + ((i * 10 ) * sizeof(INT))) k 0 10 (Znth i dist_j __default__List_Z) )
  **  (IntArray2.missing_i dist_pre i 0 10 10 dist_j )
.

Definition floyd_adjacency_matrix_partial_solve_wit_2 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH3 : (j < n_pre)) (PreH4 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= n_pre)) (PreH13 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH14 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH15 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
|--
  “ ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
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
  &&  (((dist_pre + (((k * 10 ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth k dist_j __default__List_Z)) (0)))
  **  (IntArray.missing_i (dist_pre + ((k * 10 ) * sizeof(INT))) j 0 10 (Znth k dist_j __default__List_Z) )
  **  (IntArray2.missing_i dist_pre k 0 10 10 dist_j )
.

Definition floyd_adjacency_matrix_partial_solve_wit_3 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
|--
  “ ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
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
  &&  (((dist_pre + (((i * 10 ) + k ) * sizeof(INT)))) # Int  |-> (Znth (k) ((Znth i dist_j __default__List_Z)) (0)))
  **  (IntArray.missing_i (dist_pre + ((i * 10 ) * sizeof(INT))) k 0 10 (Znth i dist_j __default__List_Z) )
  **  (IntArray2.missing_i dist_pre i 0 10 10 dist_j )
.

Definition floyd_adjacency_matrix_partial_solve_wit_4 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
|--
  “ ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
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
  &&  (((dist_pre + (((k * 10 ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth k dist_j __default__List_Z)) (0)))
  **  (IntArray.missing_i (dist_pre + ((k * 10 ) * sizeof(INT))) j 0 10 (Znth k dist_j __default__List_Z) )
  **  (IntArray2.missing_i dist_pre k 0 10 10 dist_j )
.

Definition floyd_adjacency_matrix_partial_solve_wit_5 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH2 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH4 : (j < n_pre)) (PreH5 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 10)) (PreH8 : (0 <= k)) (PreH9 : (k < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= n_pre)) (PreH14 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH15 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH16 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
|--
  “ ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
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
  &&  (((dist_pre + (((i * 10 ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))
  **  (IntArray.missing_i (dist_pre + ((i * 10 ) * sizeof(INT))) j 0 10 (Znth i dist_j __default__List_Z) )
  **  (IntArray2.missing_i dist_pre i 0 10 10 dist_j )
.

Definition floyd_adjacency_matrix_partial_solve_wit_6 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
|--
  “ (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
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
  &&  (((dist_pre + (((i * 10 ) + k ) * sizeof(INT)))) # Int  |-> (Znth (k) ((Znth i dist_j __default__List_Z)) (0)))
  **  (IntArray.missing_i (dist_pre + ((i * 10 ) * sizeof(INT))) k 0 10 (Znth i dist_j __default__List_Z) )
  **  (IntArray2.missing_i dist_pre i 0 10 10 dist_j )
.

Definition floyd_adjacency_matrix_partial_solve_wit_7 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
|--
  “ (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
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
  &&  (((dist_pre + (((k * 10 ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth k dist_j __default__List_Z)) (0)))
  **  (IntArray.missing_i (dist_pre + ((k * 10 ) * sizeof(INT))) j 0 10 (Znth k dist_j __default__List_Z) )
  **  (IntArray2.missing_i dist_pre k 0 10 10 dist_j )
.

Definition floyd_adjacency_matrix_partial_solve_wit_8 := 
forall (dist_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (state -> Prop))) (g_low_level_spec: G) (dist_j: (@list (@list Z))) (j: Z) (i: Z) (k: Z)  __default__List_Z (PreH1 : (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000)) (PreH3 : ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000)) (PreH4 : (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j )) (PreH5 : (j < n_pre)) (PreH6 : (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 10)) (PreH9 : (0 <= k)) (PreH10 : (k < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : forall (r: Z) , forall (c: Z) , (((((0 <= r) /\ (r < 10)) /\ (0 <= c)) /\ (c < 10)) -> ((0 <= (Znth c (Znth r dist_j __default__List_Z) 0)) /\ ((Znth c (Znth r dist_j __default__List_Z) 0) <= 1000000000)))) (PreH16 : (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist_j)) (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from (g_low_level_spec) (n_pre) (k) (i) (j)) X_low_level_spec )) (PreH17 : (FloydAdjacencyMatrix2Darray.matrix_shape dist_j )) (PreH18 : (FloydAdjacencyMatrix2Darray.matrix_values_safe dist_j )) ,
  (IntArray2.full dist_pre 10 10 dist_j )
|--
  “ (((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) + (Znth (j) ((Znth k dist_j __default__List_Z)) (0)) ) < (Znth (j) ((Znth i dist_j __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth k dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ ((Znth (k) ((Znth i dist_j __default__List_Z)) (0)) < 1000000000) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.matrix_rows_model dist_j ) ” 
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
  &&  (((dist_pre + (((i * 10 ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i (dist_pre + ((i * 10 ) * sizeof(INT))) j 0 10 (Znth i dist_j __default__List_Z) )
  **  (IntArray2.missing_i dist_pre i 0 10 10 dist_j )
.

Definition floyd_adjacency_matrix_derive_high_level_spec_by_low_level_spec := 
forall (dist_pre: Z) (n_pre: Z) (dist0_high_level_spec: (@list (@list Z))) (g_high_level_spec: G) ,
  “ (FloydAdjacencyMatrix2Darray.graph_has_size g_high_level_spec n_pre ) ” 
  &&  “ (FloydAdjacencyMatrix2Darray.floyd_init_matrix g_high_level_spec dist0_high_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_high_level_spec)) dist_pre dist0_high_level_spec )
|--
EX (g_low_level_spec: G) (dist0_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (state -> Prop))) ,
  (“ (FloydAdjacencyMatrix2Darray.graph_has_size g_low_level_spec n_pre ) ” 
  &&  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist0_low_level_spec)) (FloydAdjacencyMatrix2Darray.floyd_indexed_program (g_low_level_spec) (n_pre)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep 10 (FloydAdjacencyMatrix2Darray.graph_matrix_model (g_low_level_spec)) dist_pre dist0_low_level_spec ))
  **
  ((EX dist1_2,
  “ (safeExec (FloydAdjacencyMatrix2Darray.state_model (dist1_2)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist1_2 ))
  -*
  (EX dist1,
  “ (FloydAdjacencyMatrix2Darray.floyd_shortest_matrix g_high_level_spec dist1 ) ”
  &&  (GraphMatrixFlat.graph_rep 10 FloydAdjacencyMatrix2Darray.matrix_rows_model dist_pre dist1 )))
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.
Include array2_Strategy_Correct.
Include int_array_Strategy_Correct.
Include int_ptr_array2_Strategy_Correct.
Include graph_matrix_Strategy_Correct.

Axiom proof_of_floyd_adjacency_matrix_safety_wit_1 : floyd_adjacency_matrix_safety_wit_1.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_2 : floyd_adjacency_matrix_safety_wit_2.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_3 : floyd_adjacency_matrix_safety_wit_3.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_4 : floyd_adjacency_matrix_safety_wit_4.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_5 : floyd_adjacency_matrix_safety_wit_5.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_6 : floyd_adjacency_matrix_safety_wit_6.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_7 : floyd_adjacency_matrix_safety_wit_7.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_8 : floyd_adjacency_matrix_safety_wit_8.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_9 : floyd_adjacency_matrix_safety_wit_9.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_10 : floyd_adjacency_matrix_safety_wit_10.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_11 : floyd_adjacency_matrix_safety_wit_11.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_12 : floyd_adjacency_matrix_safety_wit_12.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_13 : floyd_adjacency_matrix_safety_wit_13.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_14 : floyd_adjacency_matrix_safety_wit_14.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_15 : floyd_adjacency_matrix_safety_wit_15.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_16 : floyd_adjacency_matrix_safety_wit_16.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_17 : floyd_adjacency_matrix_safety_wit_17.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_18 : floyd_adjacency_matrix_safety_wit_18.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_19 : floyd_adjacency_matrix_safety_wit_19.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_20 : floyd_adjacency_matrix_safety_wit_20.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_21 : floyd_adjacency_matrix_safety_wit_21.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_22 : floyd_adjacency_matrix_safety_wit_22.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_23 : floyd_adjacency_matrix_safety_wit_23.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_24 : floyd_adjacency_matrix_safety_wit_24.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_25 : floyd_adjacency_matrix_safety_wit_25.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_26 : floyd_adjacency_matrix_safety_wit_26.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_27 : floyd_adjacency_matrix_safety_wit_27.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_28 : floyd_adjacency_matrix_safety_wit_28.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_29 : floyd_adjacency_matrix_safety_wit_29.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_30 : floyd_adjacency_matrix_safety_wit_30.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_31 : floyd_adjacency_matrix_safety_wit_31.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_32 : floyd_adjacency_matrix_safety_wit_32.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_33 : floyd_adjacency_matrix_safety_wit_33.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_34 : floyd_adjacency_matrix_safety_wit_34.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_35 : floyd_adjacency_matrix_safety_wit_35.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_36 : floyd_adjacency_matrix_safety_wit_36.
Axiom proof_of_floyd_adjacency_matrix_safety_wit_37 : floyd_adjacency_matrix_safety_wit_37.
Axiom proof_of_floyd_adjacency_matrix_entail_wit_1 : floyd_adjacency_matrix_entail_wit_1.
Axiom proof_of_floyd_adjacency_matrix_entail_wit_2 : floyd_adjacency_matrix_entail_wit_2.
Axiom proof_of_floyd_adjacency_matrix_entail_wit_3 : floyd_adjacency_matrix_entail_wit_3.
Axiom proof_of_floyd_adjacency_matrix_entail_wit_4_1 : floyd_adjacency_matrix_entail_wit_4_1.
Axiom proof_of_floyd_adjacency_matrix_entail_wit_4_2 : floyd_adjacency_matrix_entail_wit_4_2.
Axiom proof_of_floyd_adjacency_matrix_entail_wit_4_3 : floyd_adjacency_matrix_entail_wit_4_3.
Axiom proof_of_floyd_adjacency_matrix_entail_wit_4_4 : floyd_adjacency_matrix_entail_wit_4_4.
Axiom proof_of_floyd_adjacency_matrix_entail_wit_5 : floyd_adjacency_matrix_entail_wit_5.
Axiom proof_of_floyd_adjacency_matrix_entail_wit_6 : floyd_adjacency_matrix_entail_wit_6.
Axiom proof_of_floyd_adjacency_matrix_return_wit_1 : floyd_adjacency_matrix_return_wit_1.
Axiom proof_of_floyd_adjacency_matrix_partial_solve_wit_1 : floyd_adjacency_matrix_partial_solve_wit_1.
Axiom proof_of_floyd_adjacency_matrix_partial_solve_wit_2 : floyd_adjacency_matrix_partial_solve_wit_2.
Axiom proof_of_floyd_adjacency_matrix_partial_solve_wit_3 : floyd_adjacency_matrix_partial_solve_wit_3.
Axiom proof_of_floyd_adjacency_matrix_partial_solve_wit_4 : floyd_adjacency_matrix_partial_solve_wit_4.
Axiom proof_of_floyd_adjacency_matrix_partial_solve_wit_5 : floyd_adjacency_matrix_partial_solve_wit_5.
Axiom proof_of_floyd_adjacency_matrix_partial_solve_wit_6 : floyd_adjacency_matrix_partial_solve_wit_6.
Axiom proof_of_floyd_adjacency_matrix_partial_solve_wit_7 : floyd_adjacency_matrix_partial_solve_wit_7.
Axiom proof_of_floyd_adjacency_matrix_partial_solve_wit_8 : floyd_adjacency_matrix_partial_solve_wit_8.
Axiom proof_of_floyd_adjacency_matrix_derive_high_level_spec_by_low_level_spec : floyd_adjacency_matrix_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
