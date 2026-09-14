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
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.LLM_bench.Algorithms.Prim.prim_adjacency_matrix_lib.
Require Import ListLib.Base.Positional.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import graph_matrix_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import graph_matrix_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_proof.

(*----- Function prim_adjacency_matrix -----*)

Definition prim_adjacency_matrix_safety_wit_1 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (retval: Z) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "visited" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_2 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (IntArray.undef_seg visited i n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_3 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg visited 0 (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg visited (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_4 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (retval: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.undef_full retval n_pre )
  **  ((( &( "lowcost" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_5 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (IntArray.undef_seg lowcost i n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_safety_wit_6 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg lowcost 0 (i + 1 ) (app ((repeat_Z (1000000000) (i))) ((cons (1000000000) ((@nil Z))))) )
  **  (IntArray.undef_seg lowcost (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_7 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (lowcost: Z) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> n_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_8 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (lowcost: Z) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> n_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_9 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (lowcost: Z) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  ((( &( "i" ) )) # Int  |-> n_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_10_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (prim_input_weight_bound n_pre 1000000000 )) (PreH7 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
|--
  “ False ”
.

Definition prim_adjacency_matrix_safety_wit_11_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (prim_input_weight_bound n_pre 1000000000 )) (PreH7 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition prim_adjacency_matrix_safety_wit_12_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (prim_input_weight_bound n_pre 1000000000 )) (PreH7 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_safety_wit_13_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (prim_input_weight_bound n_pre 1000000000 )) (PreH7 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "min" ) )) # Int  |->_)
  **  ((( &( "minIndex" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_safety_wit_14_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (prim_input_weight_bound n_pre 1000000000 )) (PreH7 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "min" ) )) # Int  |-> 1000000000)
  **  ((( &( "minIndex" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_15_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (i = 0)) (PreH14 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH15 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH16 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH17 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH18 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH19 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH20 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH21 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full visited n_pre l_visited )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_16_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (1 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH16 : (growing_subgraph_state g_low_level_spec s )) (PreH17 : (visited_matches_state g_low_level_spec s l_visited )) (PreH18 : ((state_vertex_count (s)) = i)) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH20 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH21 : (lowcost_sum_matches_state s l_lowcost )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH24 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH25 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH26 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH27 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full visited n_pre l_visited )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_17_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) < min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> (Znth j l_lowcost 0))
  **  ((( &( "minIndex" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_18_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) < min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s )) (PreH19 : (visited_matches_state g_low_level_spec s l_visited )) (PreH20 : ((state_vertex_count (s)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH22 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH23 : (lowcost_sum_matches_state s l_lowcost )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> (Znth j l_lowcost 0))
  **  ((( &( "minIndex" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_19_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s )) (PreH18 : (visited_matches_state g_low_level_spec s l_visited )) (PreH19 : ((state_vertex_count (s)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH21 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH22 : (lowcost_sum_matches_state s l_lowcost )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH24 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH25 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH26 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH27 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH28 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full visited n_pre l_visited )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_20_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH17 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH18 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full visited n_pre l_visited )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_21_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) >= min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_22_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) >= min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s )) (PreH19 : (visited_matches_state g_low_level_spec s l_visited )) (PreH20 : ((state_vertex_count (s)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH22 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH23 : (lowcost_sum_matches_state s l_lowcost )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_23_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (INT_MIN <= min)) (PreH11 : (min <= INT_MAX)) (PreH12 : (i = 0)) (PreH13 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH14 : (min = 0)) (PreH15 : (minIndex = 0)) (PreH16 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH18 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH19 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_24_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (INT_MIN <= min)) (PreH11 : (min <= INT_MAX)) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH15 : (growing_subgraph_state g_low_level_spec s )) (PreH16 : (visited_matches_state g_low_level_spec s l_visited )) (PreH17 : ((state_vertex_count (s)) = i)) (PreH18 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH19 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH20 : (lowcost_sum_matches_state s l_lowcost )) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH23 : (minIndex <> (-1))) (PreH24 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH25 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH26 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH27 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_25_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 > minIndex)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= minIndex)) (PreH5 : (minIndex < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (i = 0)) (PreH14 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH15 : (min = 0)) (PreH16 : (minIndex = 0)) (PreH17 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH18 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH19 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH20 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ False ”
.

Definition prim_adjacency_matrix_safety_wit_26_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 > minIndex)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= minIndex)) (PreH5 : (minIndex < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (1 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH16 : (growing_subgraph_state g_low_level_spec s )) (PreH17 : (visited_matches_state g_low_level_spec s l_visited )) (PreH18 : ((state_vertex_count (s)) = i)) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH20 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH21 : (lowcost_sum_matches_state s l_lowcost )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH24 : (minIndex <> (-1))) (PreH25 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH28 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ False ”
.

Definition prim_adjacency_matrix_safety_wit_27_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (minIndex >= n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s )) (PreH18 : (visited_matches_state g_low_level_spec s l_visited )) (PreH19 : ((state_vertex_count (s)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH21 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH22 : (lowcost_sum_matches_state s l_lowcost )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH24 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH25 : (minIndex <> (-1))) (PreH26 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH29 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ False ”
.

Definition prim_adjacency_matrix_safety_wit_28_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (minIndex >= n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : (min = 0)) (PreH17 : (minIndex = 0)) (PreH18 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH19 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH20 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH21 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ False ”
.

Definition prim_adjacency_matrix_safety_wit_29_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : (min = 0)) (PreH17 : (minIndex = 0)) (PreH18 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH19 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH20 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH21 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_safety_wit_30_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s )) (PreH18 : (visited_matches_state g_low_level_spec s l_visited )) (PreH19 : ((state_vertex_count (s)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH21 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH22 : (lowcost_sum_matches_state s l_lowcost )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH24 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH25 : (minIndex <> (-1))) (PreH26 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH29 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_safety_wit_31_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_edge_parent0: (@list E)) (s_after: St) (row_ptr: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (minIndex = 0)) (PreH16 : (min = 0)) (PreH17 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH18 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_after )) (PreH20 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH21 : ((state_vertex_count (s_after)) = 1)) (PreH22 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH24 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH25 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH26 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_32_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_edge_parent0: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (row_ptr: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH17 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s )) (PreH19 : (visited_matches_state g_low_level_spec s l_visited )) (PreH20 : ((state_vertex_count (s)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH22 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH23 : (lowcost_sum_matches_state s l_lowcost0 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH25 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH26 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH27 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH28 : (growing_subgraph_state g_low_level_spec s_after )) (PreH29 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH30 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH31 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH32 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH33 : (lowcost_values_in_range 1000000000 l_lowcost0 )) ,
  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "j" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_33_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= j)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < n_pre)) (PreH5 : (0 <= j)) (PreH6 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH12 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH13 : (0 <= minIndex)) (PreH14 : (minIndex < n_pre)) (PreH15 : (src_low_level_spec = 0)) (PreH16 : (0 < n_pre)) (PreH17 : (n_pre < INT_MAX)) (PreH18 : (2 <= n_pre)) (PreH19 : (n_pre < INT_MAX)) (PreH20 : (prim_input_weight_bound n_pre 1000000000 )) (PreH21 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH22 : (INT_MIN <= min)) (PreH23 : (min <= INT_MAX)) (PreH24 : (i = 0)) (PreH25 : (minIndex = 0)) (PreH26 : (min = 0)) (PreH27 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH28 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after )) (PreH30 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH31 : ((state_vertex_count (s_after)) = 1)) (PreH32 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH33 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH34 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH35 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH36 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH37 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH38 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "w" ) )) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_safety_wit_34_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= j)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < n_pre)) (PreH5 : (0 <= j)) (PreH6 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH12 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH13 : (0 <= minIndex)) (PreH14 : (minIndex < n_pre)) (PreH15 : (src_low_level_spec = 0)) (PreH16 : (0 < n_pre)) (PreH17 : (n_pre < INT_MAX)) (PreH18 : (2 <= n_pre)) (PreH19 : (n_pre < INT_MAX)) (PreH20 : (prim_input_weight_bound n_pre 1000000000 )) (PreH21 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH22 : (INT_MIN <= min)) (PreH23 : (min <= INT_MAX)) (PreH24 : (1 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH27 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH28 : (growing_subgraph_state g_low_level_spec s )) (PreH29 : (visited_matches_state g_low_level_spec s l_visited )) (PreH30 : ((state_vertex_count (s)) = i)) (PreH31 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH32 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH33 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH34 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH35 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH36 : (growing_subgraph_state g_low_level_spec s_after )) (PreH37 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH38 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH39 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH42 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH43 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH44 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "w" ) )) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_safety_wit_35_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH2 : (w <> 1000000000)) (PreH3 : (0 <= j)) (PreH4 : (j < n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (i = 0)) (PreH16 : (minIndex = 0)) (PreH17 : (min = 0)) (PreH18 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH19 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH20 : (growing_subgraph_state g_low_level_spec s_after )) (PreH21 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH22 : ((state_vertex_count (s_after)) = 1)) (PreH23 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH25 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH26 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH27 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH28 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH29 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH30 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> selected_row)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost) (0)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_36_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH2 : (w <> 1000000000)) (PreH3 : (0 <= j)) (PreH4 : (j < n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH18 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s )) (PreH20 : (visited_matches_state g_low_level_spec s l_visited )) (PreH21 : ((state_vertex_count (s)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH23 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH24 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH25 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH26 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH27 : (growing_subgraph_state g_low_level_spec s_after )) (PreH28 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH29 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH30 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH31 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH33 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH34 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> selected_row)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost) (0)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_37_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w < (Znth (j) (l_lowcost) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH20 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s )) (PreH22 : (visited_matches_state g_low_level_spec s l_visited )) (PreH23 : ((state_vertex_count (s)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH25 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after )) (PreH30 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH31 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH33 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> selected_row)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_38_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w < (Znth (j) (l_lowcost) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after )) (PreH23 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH24 : ((state_vertex_count (s_after)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH27 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH29 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH31 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> selected_row)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_39_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w >= (Znth (j) (l_lowcost) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH20 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s )) (PreH22 : (visited_matches_state g_low_level_spec s l_visited )) (PreH23 : ((state_vertex_count (s)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH25 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after )) (PreH30 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH31 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH33 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> selected_row)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost) (0)))
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_40_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w >= (Znth (j) (l_lowcost) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after )) (PreH23 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH24 : ((state_vertex_count (s_after)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH27 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH29 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH31 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> selected_row)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost) (0)))
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_41_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) <> 0)) (PreH2 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH3 : (w <> 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= minIndex)) (PreH9 : (minIndex < n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (i = 0)) (PreH17 : (minIndex = 0)) (PreH18 : (min = 0)) (PreH19 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH20 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s_after )) (PreH22 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH23 : ((state_vertex_count (s_after)) = 1)) (PreH24 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH26 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH27 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH28 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH29 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH30 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH31 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> selected_row)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost) (0)))
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_42_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) <> 0)) (PreH2 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH3 : (w <> 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= minIndex)) (PreH9 : (minIndex < n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH19 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH20 : (growing_subgraph_state g_low_level_spec s )) (PreH21 : (visited_matches_state g_low_level_spec s l_visited )) (PreH22 : ((state_vertex_count (s)) = i)) (PreH23 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH24 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH25 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH26 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH27 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH28 : (growing_subgraph_state g_low_level_spec s_after )) (PreH29 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH30 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH31 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH32 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH33 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH34 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH35 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH36 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> selected_row)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost) (0)))
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_43_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = 1000000000)) (PreH2 : (0 <= j)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= minIndex)) (PreH11 : (minIndex < n_pre)) (PreH12 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH13 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (src_low_level_spec = 0)) (PreH17 : (0 < n_pre)) (PreH18 : (n_pre < INT_MAX)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (INT_MIN <= min)) (PreH24 : (min <= INT_MAX)) (PreH25 : (i = 0)) (PreH26 : (minIndex = 0)) (PreH27 : (min = 0)) (PreH28 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH29 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after )) (PreH31 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH32 : ((state_vertex_count (s_after)) = 1)) (PreH33 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH35 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH36 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH37 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH38 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH39 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_44_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = 1000000000)) (PreH2 : (0 <= j)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= minIndex)) (PreH11 : (minIndex < n_pre)) (PreH12 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH13 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (src_low_level_spec = 0)) (PreH17 : (0 < n_pre)) (PreH18 : (n_pre < INT_MAX)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (INT_MIN <= min)) (PreH24 : (min <= INT_MAX)) (PreH25 : (1 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH28 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH29 : (growing_subgraph_state g_low_level_spec s )) (PreH30 : (visited_matches_state g_low_level_spec s l_visited )) (PreH31 : ((state_vertex_count (s)) = i)) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH33 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH34 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH35 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH36 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH37 : (growing_subgraph_state g_low_level_spec s_after )) (PreH38 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH39 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH40 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH41 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH43 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH44 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH45 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_45_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "min" ) )) # Int  |-> 1000000000)
  **  ((( &( "minIndex" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_46_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "min" ) )) # Int  |-> 1000000000)
  **  ((( &( "minIndex" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_47_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "min" ) )) # Int  |->_)
  **  ((( &( "minIndex" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_safety_wit_48_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "min" ) )) # Int  |->_)
  **  ((( &( "minIndex" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_safety_wit_49_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition prim_adjacency_matrix_safety_wit_50_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_safety_wit_51_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition prim_adjacency_matrix_safety_wit_52_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_safety_wit_53_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (growing_subgraph_state g_low_level_spec s_after )) (PreH15 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH16 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH17 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH18 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH19 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_54_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (i = 0)) (PreH6 : (minIndex = 0)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (growing_subgraph_state g_low_level_spec s_after )) (PreH15 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH16 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH17 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH18 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH19 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_safety_wit_55_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "ret" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_56_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "ret" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_57_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "ret" ) )) # Int64  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_58_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s )) (PreH10 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH11 : ((state_vertex_count (s)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH13 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH14 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "ret" ) )) # Int64  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_safety_wit_59_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (l_lowcost: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited )) (PreH12 : ((state_vertex_count (s)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH14 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH15 : (lowcost_sum_matches_state s l_lowcost )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH17 : (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int64  |-> ret)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ ((ret + (Znth i l_lowcost 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (ret + (Znth i l_lowcost 0) )) ”
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (l_lowcost: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited )) (PreH12 : ((state_vertex_count (s)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH14 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH15 : (lowcost_sum_matches_state s l_lowcost )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH17 : (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int64  |-> ret)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ ((ret + (Znth i l_lowcost 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (ret + (Znth i l_lowcost 0) )) ”
).

Definition prim_adjacency_matrix_safety_wit_59_running_split_goal_1 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (l_lowcost: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited )) (PreH12 : ((state_vertex_count (s)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH14 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH15 : (lowcost_sum_matches_state s l_lowcost )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH17 : (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int64  |-> ret)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ ((ret + (Znth i l_lowcost 0) ) <= INT64_MAX) ”
.

Definition prim_adjacency_matrix_safety_wit_59_running_split_goal_2 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (l_lowcost: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited )) (PreH12 : ((state_vertex_count (s)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH14 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH15 : (lowcost_sum_matches_state s l_lowcost )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH17 : (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int64  |-> ret)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ ((INT64_MIN) <= (ret + (Znth i l_lowcost 0) )) ”
.

Definition prim_adjacency_matrix_safety_wit_60_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (l_lowcost: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited )) (PreH12 : ((state_vertex_count (s)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH14 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH15 : (lowcost_sum_matches_state s l_lowcost )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH17 : (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int64  |-> (ret + (Znth i l_lowcost 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_entail_wit_1 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (retval: Z) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.undef_full retval n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.seg retval 0 0 (repeat_Z (0) (0)) )
  **  (IntArray.undef_seg retval 0 n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((repeat_Z (0) (0)) = (@nil Z)) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z (0) (0)) = (@nil Z))
.

Definition prim_adjacency_matrix_entail_wit_2 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg visited 0 (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg visited (i + 1 ) n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.seg visited 0 (i + 1 ) (repeat_Z (0) ((i + 1 ))) )
  **  (IntArray.undef_seg visited (i + 1 ) n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 ))))
.

Definition prim_adjacency_matrix_entail_wit_3 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (retval: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.undef_full retval n_pre )
  **  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg retval 0 0 (repeat_Z (1000000000) (0)) )
  **  (IntArray.undef_seg retval 0 n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((repeat_Z (1000000000) (0)) = (@nil Z)) ” 
  &&  “ ((repeat_Z (0) (i)) = (repeat_Z (0) (n_pre))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z (1000000000) (0)) = (@nil Z))
.

Definition prim_adjacency_matrix_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z (0) (i)) = (repeat_Z (0) (n_pre)))
.

Definition prim_adjacency_matrix_entail_wit_4 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg lowcost 0 (i + 1 ) (app ((repeat_Z (1000000000) (i))) ((cons (1000000000) ((@nil Z))))) )
  **  (IntArray.undef_seg lowcost (i + 1 ) n_pre )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg lowcost 0 (i + 1 ) (repeat_Z (1000000000) ((i + 1 ))) )
  **  (IntArray.undef_seg lowcost (i + 1 ) n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (1000000000) (i))) ((cons (1000000000) ((@nil Z))))) = (repeat_Z (1000000000) ((i + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((app ((repeat_Z (1000000000) (i))) ((cons (1000000000) ((@nil Z))))) = (repeat_Z (1000000000) ((i + 1 ))))
.

Definition prim_adjacency_matrix_entail_wit_5 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (IntArray.undef_seg lowcost i n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((repeat_Z (1000000000) (i)) = (repeat_Z (1000000000) (n_pre))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z (1000000000) (i)) = (repeat_Z (1000000000) (n_pre)))
.

Definition prim_adjacency_matrix_entail_wit_6_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (lowcost: Z) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
|--
  “ (0 = 0) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
.

Definition prim_adjacency_matrix_entail_wit_7_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (prim_input_weight_bound n_pre 1000000000 )) (PreH7 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
|--
  EX (l_visited: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= 1000000000) ” 
  &&  “ (1000000000 <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ” 
  &&  “ ((0 = 0) -> ((1000000000 = 1000000000) /\ ((-1) = (-1)))) ” 
  &&  “ ((1 <= 0) -> ((1000000000 = 0) /\ ((-1) = 0))) ” 
  &&  “ (((-1) <> (-1)) -> ((0 <= (-1)) /\ ((-1) < 0))) ” 
  &&  “ (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (l_edge_parent = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (prim_input_weight_bound n_pre 1000000000 )) (PreH7 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_7_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (prim_input_weight_bound n_pre 1000000000 )) (PreH7 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
.

Definition prim_adjacency_matrix_entail_wit_8_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  EX (l_visited: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= (Znth j l_lowcost_2 0)) ” 
  &&  “ ((Znth j l_lowcost_2 0) <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (((j + 1 ) = 0) -> (((Znth j l_lowcost_2 0) = 1000000000) /\ (j = (-1)))) ” 
  &&  “ ((1 <= (j + 1 )) -> (((Znth j l_lowcost_2 0) = 0) /\ (j = 0))) ” 
  &&  “ ((j <> (-1)) -> ((0 <= j) /\ (j < (j + 1 )))) ” 
  &&  “ (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (l_edge_parent = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  TT && emp 
|--
  “ ((1 <= (j + 1 )) -> (((Znth j l_lowcost_2 0) = 0) /\ (j = 0))) ” 
  &&  “ (INT_MIN <= (Znth j l_lowcost_2 0)) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_8_1_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  ((1 <= (j + 1 )) -> (((Znth j l_lowcost_2 0) = 0) /\ (j = 0)))
.

Definition prim_adjacency_matrix_entail_wit_8_1_boot_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (INT_MIN <= (Znth j l_lowcost_2 0))
.

Definition prim_adjacency_matrix_entail_wit_8_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH22 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH23 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= (Znth j l_lowcost_2 0)) ” 
  &&  “ ((Znth j l_lowcost_2 0) <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s (j + 1 ) 1000000000 j l_lowcost l_edge_parent ) ” 
  &&  “ ((j = (-1)) -> ((Znth j l_lowcost_2 0) = 1000000000)) ” 
  &&  “ ((j <> (-1)) -> ((Znth j l_lowcost_2 0) = (Znth (j) (l_lowcost) (0)))) ” 
  &&  “ ((j <> (-1)) -> ((0 <= j) /\ (j < (j + 1 )))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH22 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH23 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ ((state_vertex_count (s_2)) < n_pre) ” 
  &&  “ (INT_MIN <= (Znth j l_lowcost_2 0)) ” 
  &&  “ ((Znth j l_lowcost_2 0) <= INT_MAX) ” 
  &&  “ ((state_vertex_count (s_2)) < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((state_vertex_count (s_2)) - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s (j + 1 ) 1000000000 j l_lowcost_2 l_edge_parent ) ” 
  &&  “ ((j = (-1)) -> ((Znth j l_lowcost_2 0) = 1000000000)) ” 
  &&  “ ((j <> (-1)) -> ((Znth j l_lowcost_2 0) = (Znth (j) (l_lowcost_2) (0)))) ” 
  &&  “ ((j <> (-1)) -> ((0 <= j) /\ (j < (j + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_8_3_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH18 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH19 : ((state_vertex_count (s_2)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH21 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH22 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH24 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH25 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH26 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH27 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH28 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s (j + 1 ) 1000000000 minIndex l_lowcost l_edge_parent ) ” 
  &&  “ ((minIndex = (-1)) -> (min = 1000000000)) ” 
  &&  “ ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0)))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < (j + 1 )))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH18 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH19 : ((state_vertex_count (s_2)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH21 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH22 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH24 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH25 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH26 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH27 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH28 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ ((state_vertex_count (s_2)) < n_pre) ” 
  &&  “ ((state_vertex_count (s_2)) < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((state_vertex_count (s_2)) - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s (j + 1 ) 1000000000 minIndex l_lowcost_2 l_edge_parent ) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < (j + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_8_4_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH17 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH18 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH19 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH21 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_visited: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (((j + 1 ) = 0) -> ((min = 1000000000) /\ (minIndex = (-1)))) ” 
  &&  “ ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < (j + 1 )))) ” 
  &&  “ (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (l_edge_parent = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH17 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH18 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH19 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH21 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  TT && emp 
|--
  “ ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_8_4_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH17 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH18 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH19 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH21 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0)))
.

Definition prim_adjacency_matrix_entail_wit_8_5_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  EX (l_visited: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (((j + 1 ) = 0) -> ((min = 1000000000) /\ (minIndex = (-1)))) ” 
  &&  “ ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < (j + 1 )))) ” 
  &&  “ (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (l_edge_parent = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  TT && emp 
|--
  “ ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_8_5_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0)))
.

Definition prim_adjacency_matrix_entail_wit_8_6_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH22 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH23 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s (j + 1 ) 1000000000 minIndex l_lowcost l_edge_parent ) ” 
  &&  “ ((minIndex = (-1)) -> (min = 1000000000)) ” 
  &&  “ ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0)))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < (j + 1 )))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH22 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH23 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ ((state_vertex_count (s_2)) < n_pre) ” 
  &&  “ ((state_vertex_count (s_2)) < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((state_vertex_count (s_2)) - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s (j + 1 ) 1000000000 minIndex l_lowcost_2 l_edge_parent ) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < (j + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_9_1_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (i = 0)) (PreH14 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH15 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH16 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH17 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH18 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH19 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH20 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH21 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_visited: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (min = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (l_edge_parent = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  ((( &( "j" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
.

Definition prim_adjacency_matrix_entail_wit_9_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (1 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH16 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH17 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH18 : ((state_vertex_count (s_2)) = i)) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH20 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH21 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH23 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH24 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH25 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH26 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH27 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (u: Z)  (v: Z)  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (minIndex <> (-1)) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost) (0))) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v ) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent ) ”
  &&  ((( &( "j" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (1 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH16 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH17 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH18 : ((state_vertex_count (s_2)) = i)) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH20 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH21 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH23 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH24 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH25 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH26 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH27 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  TT && emp 
|--
  EX (u: Z)  (v: Z)  (l_edge_parent: (@list E))  (s: St) ,
  “ (j = n_pre) ” 
  &&  “ ((state_vertex_count (s_2)) < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((state_vertex_count (s_2)) < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((state_vertex_count (s_2)) - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (minIndex <> (-1)) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost_2) (0))) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v ) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost_2 l_edge_parent ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_10_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : (min = 0)) (PreH17 : (minIndex = 0)) (PreH18 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH19 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH20 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH21 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  EX (row_ptr: Z)  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (s_after = (initSt (g_low_level_spec) (src_low_level_spec))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = 1) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (l_edge_parent0 = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost0 )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) l_lowcost ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (0)))) = 1) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (0)) (replace_Znth (0) (1) (l_visited_2)) ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (0)) ) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (0)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ”
  &&  (IntArray.full row_ptr_2 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
).

Definition prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) l_lowcost ) ”
.

Definition prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ ((state_vertex_count ((initSt (g_low_level_spec) (0)))) = 1) ”
.

Definition prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_3 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (0)) (replace_Znth (0) (1) (l_visited_2)) ) ”
.

Definition prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_4 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (0)) ) ”
.

Definition prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_5 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (0)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ”
.

Definition prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_6 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ”
.

Definition prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_spatial := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  (IntArray.full row_ptr_2 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
.

Definition prim_adjacency_matrix_entail_wit_10_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_2: St) (u_2: Z) (v_2: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH18 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH19 : ((state_vertex_count (s_2)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent )) (PreH21 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost l_edge_parent 1000000000 )) (PreH22 : (lowcost_sum_matches_state s_2 l_lowcost )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH24 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost l_edge_parent 1000000000 )) (PreH25 : (minIndex <> (-1))) (PreH26 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent minIndex u_2 v_2 )) (PreH29 : (min_vertex_in_range g_low_level_spec s_2 n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  EX (row_ptr: Z)  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost0 )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_2: St) (u_2: Z) (v_2: Z) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent )) (PreH22 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost l_edge_parent 1000000000 )) (PreH23 : (lowcost_sum_matches_state s_2 l_lowcost )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH25 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost l_edge_parent 1000000000 )) (PreH26 : (minIndex <> (-1))) (PreH27 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH28 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent minIndex )) (PreH29 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent minIndex u_2 v_2 )) (PreH30 : (min_vertex_in_range g_low_level_spec s_2 n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  EX (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St) ,
  “ ((replace_Znth (minIndex) (1) (l_visited_2)) = (replace_Znth (minIndex) (1) (l_visited))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent0 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (IntArray.full row_ptr_2 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
).

Definition prim_adjacency_matrix_entail_wit_11_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_edge_parent0_2: (@list E)) (s_after_2: St) (row_ptr: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (minIndex = 0)) (PreH16 : (min = 0)) (PreH17 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH18 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH20 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH21 : ((state_vertex_count (s_after_2)) = 1)) (PreH22 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH24 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH25 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH26 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost0_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (s_after = (initSt (g_low_level_spec) (src_low_level_spec))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = 1) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (l_edge_parent0 = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex 0 l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_edge_parent0_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (minIndex = 0)) (PreH16 : (min = 0)) (PreH17 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH18 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH20 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH21 : ((state_vertex_count (s_after_2)) = 1)) (PreH22 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH24 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH25 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH26 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E)) ,
  “ ((replace_Znth (0) (1) ((repeat_Z (0) (n_pre)))) = (replace_Znth (0) (1) ((repeat_Z (0) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (0)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (0)) ) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (0)) (replace_Znth (0) (1) ((repeat_Z (0) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (0)))) = 1) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) (replace_Znth (0) (0) ((repeat_Z (1000000000) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) ) ” 
  &&  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 (initSt (g_low_level_spec) (0)) 0 0 (replace_Znth (0) (0) ((repeat_Z (1000000000) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) (default_edge_list ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_11_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_edge_parent0_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (row_ptr: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH17 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH22 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH23 : (lowcost_sum_matches_state s_2 l_lowcost0_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH25 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH26 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH27 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH28 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH29 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH30 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH31 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH32 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH33 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost0_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex 0 l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_edge_parent0_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH17 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH22 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH23 : (lowcost_sum_matches_state s_2 l_lowcost0_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH25 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH26 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH27 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH28 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH29 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH30 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH31 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH32 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH33 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((replace_Znth (minIndex) (1) (l_visited_2)) = (replace_Znth (minIndex) (1) (l_visited))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ ((state_vertex_count (s_2)) < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ ((state_vertex_count (s_2)) < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ ((Znth (minIndex) (l_lowcost0_2) (0)) = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) ((state_vertex_count (s_2)))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = ((state_vertex_count (s_2)) + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex 0 l_lowcost0 l_edge_parent0 l_lowcost0_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0_2 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_12_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH23 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH24 : ((state_vertex_count (s_after_2)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH27 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH29 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH31 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH33 : (0 <= j)) (PreH34 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (s_after = (initSt (g_low_level_spec) (src_low_level_spec))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = 1) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (l_edge_parent0 = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH23 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH24 : ((state_vertex_count (s_after_2)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH27 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH29 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH31 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH33 : (0 <= j)) (PreH34 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E)) ,
  “ ((replace_Znth (0) (1) ((repeat_Z (0) (n_pre)))) = (replace_Znth (0) (1) ((repeat_Z (0) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))))))) ” 
  &&  “ ((Znth (j) ((Znth (0) (matrix_low_level_spec) ((@nil Z)))) (0)) = (Znth j (Znth (0) (matrix_low_level_spec) ((@nil Z))) 0)) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ (0 < (Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (0)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (0)) ) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (0)) (replace_Znth (0) (1) ((repeat_Z (0) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (0)))) = 1) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) (replace_Znth (0) (0) ((repeat_Z (1000000000) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) ) ” 
  &&  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 (initSt (g_low_level_spec) (0)) 0 j (replace_Znth (0) (0) ((repeat_Z (1000000000) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) (default_edge_list ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))) l_lowcost_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) l_lowcost_2 ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_12_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u_2: Z) (v_2: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH20 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH22 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH23 : ((state_vertex_count (s_2)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH25 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH31 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH36 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH38 : (0 <= j)) (PreH39 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u_2: Z) (v_2: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH20 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH22 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH23 : ((state_vertex_count (s_2)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH25 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH31 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH36 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH38 : (0 <= j)) (PreH39 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((replace_Znth (minIndex) (1) (l_visited_2)) = (replace_Znth (minIndex) (1) (l_visited))) ” 
  &&  “ ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = (Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0)) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ ((state_vertex_count (s_2)) < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ (0 < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ ((state_vertex_count (s_2)) < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ ((Znth (minIndex) (l_lowcost0_2) (0)) = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) ((state_vertex_count (s_2)))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = ((state_vertex_count (s_2)) + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_13_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <> 1000000000)) (PreH2 : (0 <= j)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= minIndex)) (PreH11 : (minIndex < n_pre)) (PreH12 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH13 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (src_low_level_spec = 0)) (PreH17 : (0 < n_pre)) (PreH18 : (n_pre < INT_MAX)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (INT_MIN <= min)) (PreH24 : (min <= INT_MAX)) (PreH25 : (i = 0)) (PreH26 : (minIndex = 0)) (PreH27 : (min = 0)) (PreH28 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH29 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH32 : ((state_vertex_count (s_after_2)) = 1)) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH36 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH37 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH38 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH39 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <> 1000000000) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (s_after = (initSt (g_low_level_spec) (src_low_level_spec))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = 1) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (l_edge_parent0 = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost) (0)))
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (j: Z) (minIndex: Z) (i: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <> 1000000000)) (PreH2 : (0 <= j)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= minIndex)) (PreH11 : (minIndex < n_pre)) (PreH12 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH13 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (src_low_level_spec = 0)) (PreH17 : (0 < n_pre)) (PreH18 : (n_pre < INT_MAX)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (INT_MIN <= min)) (PreH24 : (min <= INT_MAX)) (PreH25 : (i = 0)) (PreH26 : (minIndex = 0)) (PreH27 : (min = 0)) (PreH28 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH29 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH32 : ((state_vertex_count (s_after_2)) = 1)) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH36 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH37 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH38 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH39 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E)) ,
  “ ((Znth (j) (l_lowcost) (0)) = (Znth j l_lowcost_2 0)) ” 
  &&  “ ((Znth (j) ((replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre))))) (0)) = (Znth j (replace_Znth (minIndex) (1) (l_visited_2)) 0)) ” 
  &&  “ ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <> 1000000000) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (src_low_level_spec)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) ) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (src_low_level_spec)))) = 1) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 (initSt (g_low_level_spec) (src_low_level_spec)) minIndex j (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) (default_edge_list (n_pre)) l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) )
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
).

Definition prim_adjacency_matrix_entail_wit_13_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <> 1000000000)) (PreH2 : (0 <= j)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= minIndex)) (PreH11 : (minIndex < n_pre)) (PreH12 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH13 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (src_low_level_spec = 0)) (PreH17 : (0 < n_pre)) (PreH18 : (n_pre < INT_MAX)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (INT_MIN <= min)) (PreH24 : (min <= INT_MAX)) (PreH25 : (1 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH28 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH29 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH31 : ((state_vertex_count (s_2)) = i)) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH33 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH34 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH35 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH36 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH37 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH38 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH39 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH40 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH43 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH44 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH45 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <> 1000000000) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost) (0)))
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <> 1000000000)) (PreH2 : (0 <= j)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= minIndex)) (PreH11 : (minIndex < n_pre)) (PreH12 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH13 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (src_low_level_spec = 0)) (PreH17 : (0 < n_pre)) (PreH18 : (n_pre < INT_MAX)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (INT_MIN <= min)) (PreH24 : (min <= INT_MAX)) (PreH25 : (1 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH28 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH29 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH31 : ((state_vertex_count (s_2)) = i)) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH33 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH34 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH35 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH36 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH37 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH38 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH39 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH40 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH43 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH44 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH45 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((Znth (j) (l_lowcost_2) (0)) = (Znth j l_lowcost_2 0)) ” 
  &&  “ ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = (Znth j (replace_Znth (minIndex) (1) (l_visited_2)) 0)) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((state_vertex_count (s_2)) < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) < INT_MAX) ” 
  &&  “ ((state_vertex_count (s_2)) < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ ((Znth (minIndex) (l_lowcost0_2) (0)) = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) ((state_vertex_count (s_2)))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited_2)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = ((state_vertex_count (s_2)) + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_14_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w < (Znth (j) (l_lowcost_2) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH20 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH22 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH23 : ((state_vertex_count (s_2)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH25 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH31 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH36 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w <= INT_MAX)) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH4 : (w >= INT_MIN)) (PreH5 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH7 : (w < (Znth (j) (l_lowcost_2) (0)))) (PreH8 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH9 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH10 : (w <> 1000000000)) (PreH11 : (0 <= j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= minIndex)) (PreH16 : (minIndex < n_pre)) (PreH17 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH18 : (src_low_level_spec = 0)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (1 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH26 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH27 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH28 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH29 : ((state_vertex_count (s_2)) = i)) (PreH30 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH31 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH32 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH33 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH34 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH35 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH36 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH37 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH38 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH39 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH41 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH42 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH43 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
).

Definition prim_adjacency_matrix_entail_wit_14_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w < (Znth (j) (l_lowcost_2) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH23 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH24 : ((state_vertex_count (s_after_2)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH27 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH29 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH31 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (s_after = (initSt (g_low_level_spec) (src_low_level_spec))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = 1) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (l_edge_parent0 = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w <= INT_MAX)) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH4 : (w >= INT_MIN)) (PreH5 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH7 : (w < (Znth (j) (l_lowcost_2) (0)))) (PreH8 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH9 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH10 : (w <> 1000000000)) (PreH11 : (0 <= j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= minIndex)) (PreH16 : (minIndex < n_pre)) (PreH17 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH18 : (src_low_level_spec = 0)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (i = 0)) (PreH24 : (minIndex = 0)) (PreH25 : (min = 0)) (PreH26 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH27 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH28 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH29 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH30 : ((state_vertex_count (s_after_2)) = 1)) (PreH31 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH33 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH34 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH35 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH37 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH38 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (src_low_level_spec)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) ) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (src_low_level_spec)))) = 1) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 (initSt (g_low_level_spec) (src_low_level_spec)) minIndex (j + 1 ) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) (default_edge_list (n_pre)) l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) )
  **  (IntArray.full lowcost n_pre l_lowcost )
).

Definition prim_adjacency_matrix_entail_wit_14_3_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w >= (Znth (j) (l_lowcost_2) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH20 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH22 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH23 : ((state_vertex_count (s_2)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH25 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH31 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH36 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) (l_lowcost_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) (l_lowcost_2) (0)) >= INT_MIN)) (PreH5 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH7 : (w >= (Znth (j) (l_lowcost_2) (0)))) (PreH8 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH9 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH10 : (w <> 1000000000)) (PreH11 : (0 <= j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= minIndex)) (PreH16 : (minIndex < n_pre)) (PreH17 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH18 : (src_low_level_spec = 0)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (1 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH26 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH27 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH28 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH29 : ((state_vertex_count (s_2)) = i)) (PreH30 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH31 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH32 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH33 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH34 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH35 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH36 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH37 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH38 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH39 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH41 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH42 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH43 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
).

Definition prim_adjacency_matrix_entail_wit_14_4_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : (w >= (Znth (j) (l_lowcost_2) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH23 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH24 : ((state_vertex_count (s_after_2)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH27 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH29 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH31 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (s_after = (initSt (g_low_level_spec) (src_low_level_spec))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = 1) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (l_edge_parent0 = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) (l_lowcost_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) (l_lowcost_2) (0)) >= INT_MIN)) (PreH5 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH7 : (w >= (Znth (j) (l_lowcost_2) (0)))) (PreH8 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH9 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH10 : (w <> 1000000000)) (PreH11 : (0 <= j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= minIndex)) (PreH16 : (minIndex < n_pre)) (PreH17 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH18 : (src_low_level_spec = 0)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (i = 0)) (PreH24 : (minIndex = 0)) (PreH25 : (min = 0)) (PreH26 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH27 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH28 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH29 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH30 : ((state_vertex_count (s_after_2)) = 1)) (PreH31 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH33 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH34 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH35 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH37 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH38 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (src_low_level_spec)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) ) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (src_low_level_spec)))) = 1) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 (initSt (g_low_level_spec) (src_low_level_spec)) minIndex (j + 1 ) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) (default_edge_list (n_pre)) l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) )
  **  (IntArray.full lowcost n_pre l_lowcost )
).

Definition prim_adjacency_matrix_entail_wit_14_5_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <> 0)) (PreH2 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH3 : (w <> 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= minIndex)) (PreH9 : (minIndex < n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (i = 0)) (PreH17 : (minIndex = 0)) (PreH18 : (min = 0)) (PreH19 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH20 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH22 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH23 : ((state_vertex_count (s_after_2)) = 1)) (PreH24 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH26 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH27 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH28 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH29 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH30 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH31 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (s_after = (initSt (g_low_level_spec) (src_low_level_spec))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = 1) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (l_edge_parent0 = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) (l_lowcost_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) (l_lowcost_2) (0)) >= INT_MIN)) (PreH5 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH7 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <> 0)) (PreH8 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH9 : (w <> 1000000000)) (PreH10 : (0 <= j)) (PreH11 : (j < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH17 : (src_low_level_spec = 0)) (PreH18 : (2 <= n_pre)) (PreH19 : (n_pre < INT_MAX)) (PreH20 : (prim_input_weight_bound n_pre 1000000000 )) (PreH21 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH22 : (i = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (min = 0)) (PreH25 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH26 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH27 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH28 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH29 : ((state_vertex_count (s_after_2)) = 1)) (PreH30 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH31 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH32 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH33 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH34 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH36 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (src_low_level_spec)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) ) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (src_low_level_spec)))) = 1) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 (initSt (g_low_level_spec) (src_low_level_spec)) minIndex (j + 1 ) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) (default_edge_list (n_pre)) l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) )
  **  (IntArray.full lowcost n_pre l_lowcost )
).

Definition prim_adjacency_matrix_entail_wit_14_6_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <> 0)) (PreH2 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH3 : (w <> 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= minIndex)) (PreH9 : (minIndex < n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH19 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH20 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH21 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH22 : ((state_vertex_count (s_2)) = i)) (PreH23 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH24 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH25 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH26 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH27 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH28 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH29 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH30 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH31 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH32 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH33 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH34 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH35 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH36 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) (l_lowcost_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) (l_lowcost_2) (0)) >= INT_MIN)) (PreH5 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH7 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <> 0)) (PreH8 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH9 : (w <> 1000000000)) (PreH10 : (0 <= j)) (PreH11 : (j < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH17 : (src_low_level_spec = 0)) (PreH18 : (2 <= n_pre)) (PreH19 : (n_pre < INT_MAX)) (PreH20 : (prim_input_weight_bound n_pre 1000000000 )) (PreH21 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH22 : (1 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH25 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH26 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH27 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH28 : ((state_vertex_count (s_2)) = i)) (PreH29 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH30 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH31 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH32 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH33 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH34 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH35 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH36 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH38 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH40 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
).

Definition prim_adjacency_matrix_entail_wit_14_7_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = 1000000000)) (PreH2 : (0 <= j)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= minIndex)) (PreH11 : (minIndex < n_pre)) (PreH12 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH13 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (src_low_level_spec = 0)) (PreH17 : (0 < n_pre)) (PreH18 : (n_pre < INT_MAX)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (INT_MIN <= min)) (PreH24 : (min <= INT_MAX)) (PreH25 : (i = 0)) (PreH26 : (minIndex = 0)) (PreH27 : (min = 0)) (PreH28 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH29 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH32 : ((state_vertex_count (s_after_2)) = 1)) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH36 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH37 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH38 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH39 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (s_after = (initSt (g_low_level_spec) (src_low_level_spec))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = 1) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (l_edge_parent0 = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= minIndex)) (PreH13 : (minIndex < n_pre)) (PreH14 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH15 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH16 : (0 <= minIndex)) (PreH17 : (minIndex < n_pre)) (PreH18 : (src_low_level_spec = 0)) (PreH19 : (0 < n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : (prim_input_weight_bound n_pre 1000000000 )) (PreH24 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH25 : (INT_MIN <= min)) (PreH26 : (min <= INT_MAX)) (PreH27 : (i = 0)) (PreH28 : (minIndex = 0)) (PreH29 : (min = 0)) (PreH30 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH31 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH32 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH33 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH34 : ((state_vertex_count (s_after_2)) = 1)) (PreH35 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH36 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH37 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH38 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH39 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH40 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
|--
  EX (l_edge_parent: (@list E)) ,
  “ ((replace_Znth (minIndex) (1) (l_visited_2)) = (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre))))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (min = 0) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (src_low_level_spec)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) ) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (src_low_level_spec)))) = 1) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 (initSt (g_low_level_spec) (src_low_level_spec)) minIndex (j + 1 ) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) (default_edge_list (n_pre)) l_lowcost_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) l_lowcost_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_2 ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
).

Definition prim_adjacency_matrix_entail_wit_14_8_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = 1000000000)) (PreH2 : (0 <= j)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= minIndex)) (PreH11 : (minIndex < n_pre)) (PreH12 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH13 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH14 : (0 <= minIndex)) (PreH15 : (minIndex < n_pre)) (PreH16 : (src_low_level_spec = 0)) (PreH17 : (0 < n_pre)) (PreH18 : (n_pre < INT_MAX)) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (prim_input_weight_bound n_pre 1000000000 )) (PreH22 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH23 : (INT_MIN <= min)) (PreH24 : (min <= INT_MAX)) (PreH25 : (1 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH28 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH29 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH31 : ((state_vertex_count (s_2)) = i)) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH33 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH34 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH35 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH36 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH37 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH38 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH39 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH40 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH43 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH44 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH45 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (row_ptr: Z) (j: Z) (minIndex: Z) (i: Z) (min: Z) (PreH1 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= j)) (PreH7 : (j < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= minIndex)) (PreH13 : (minIndex < n_pre)) (PreH14 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH15 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH16 : (0 <= minIndex)) (PreH17 : (minIndex < n_pre)) (PreH18 : (src_low_level_spec = 0)) (PreH19 : (0 < n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : (prim_input_weight_bound n_pre 1000000000 )) (PreH24 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH25 : (INT_MIN <= min)) (PreH26 : (min <= INT_MAX)) (PreH27 : (1 <= i)) (PreH28 : (i < n_pre)) (PreH29 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH30 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH31 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH32 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH33 : ((state_vertex_count (s_2)) = i)) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH35 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH36 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH37 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH38 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH39 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH40 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH41 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH42 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH43 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH44 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH45 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH46 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH47 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
|--
  EX (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((replace_Znth (minIndex) (1) (l_visited_2)) = (replace_Znth (minIndex) (1) (l_visited))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost0) (0))) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 ) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v ) ” 
  &&  “ (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0 ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_2 ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
).

Definition prim_adjacency_matrix_entail_wit_15_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH23 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH24 : ((state_vertex_count (s_after_2)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH27 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH29 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH31 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH33 : (0 <= j)) (PreH34 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_edge_parent0: (@list E))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ ((i = 0) -> (min = 0)) ” 
  &&  “ (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0)))) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "j" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (row_ptr: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH23 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH24 : ((state_vertex_count (s_after_2)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH27 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH29 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH31 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH33 : (0 <= j)) (PreH34 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
|--
  EX (l_edge_parent0: (@list E))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((replace_Znth (minIndex) (1) (l_visited_2)) = (replace_Znth (minIndex) (1) (l_visited))) ” 
  &&  “ (j = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ ((i = 0) -> (min = 0)) ” 
  &&  “ (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0)))) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_2 ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
).

Definition prim_adjacency_matrix_entail_wit_15_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u: Z) (v: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH20 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s )) (PreH22 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH23 : ((state_vertex_count (s)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0_2 )) (PreH25 : (lowcost_parent_match g_low_level_spec s l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0_2 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s l_edge_parent0_2 minIndex u v )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s s_after_2 l_edge_parent0_2 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH31 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH36 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH38 : (0 <= j)) (PreH39 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_edge_parent0: (@list E))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i = 0) -> (min = 0)) ” 
  &&  “ (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0)))) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "j" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (row_ptr: Z) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u: Z) (v: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : (prim_input_weight_bound n_pre 1000000000 )) (PreH14 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH20 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s )) (PreH22 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH23 : ((state_vertex_count (s)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0_2 )) (PreH25 : (lowcost_parent_match g_low_level_spec s l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0_2 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s l_edge_parent0_2 minIndex u v )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s s_after_2 l_edge_parent0_2 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH31 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH36 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH38 : (0 <= j)) (PreH39 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
|--
  EX (l_edge_parent0: (@list E))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((replace_Znth (minIndex) (1) (l_visited_2)) = (replace_Znth (minIndex) (1) (l_visited))) ” 
  &&  “ (j = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i = 0) -> (min = 0)) ” 
  &&  “ (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0)))) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_2 ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
).

Definition prim_adjacency_matrix_entail_wit_16_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (i = 0)) (PreH11 : (minIndex = 0)) (PreH12 : ((i = 0) -> (min = 0))) (PreH13 : (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0))))) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH17 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH18 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH20 : (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent_2 )) (PreH21 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH22 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH24 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (i = 0)) (PreH11 : (minIndex = 0)) (PreH12 : ((i = 0) -> (min = 0))) (PreH13 : (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0))))) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH17 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH18 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH20 : (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent_2 )) (PreH21 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH22 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH24 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s_after: St) ,
  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (0) (1) (l_visited_2)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (0 + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_16_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i = 0) -> (min = 0))) (PreH13 : (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0))))) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH17 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH18 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH20 : (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent_2 )) (PreH21 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH22 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH24 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i = 0) -> (min = 0))) (PreH13 : (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0))))) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH17 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH18 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH20 : (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent_2 )) (PreH21 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH22 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH24 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s_after: St) ,
  “ (i < n_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited_2)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_17_1_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i_2: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH10 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH11 : ((state_vertex_count (s_2)) = i)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH13 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH14 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH16 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i_2)) (PreH19 : (i_2 < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i_2)) (PreH23 : (i_2 < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH33 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= 1000000000) ” 
  &&  “ (1000000000 <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s 0 1000000000 (-1) l_lowcost l_edge_parent ) ” 
  &&  “ (((-1) = (-1)) -> (1000000000 = 1000000000)) ” 
  &&  “ (((-1) <> (-1)) -> (1000000000 = (Znth ((-1)) (l_lowcost) (0)))) ” 
  &&  “ (((-1) <> (-1)) -> ((0 <= (-1)) /\ ((-1) < 0))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i_2: Z) (minIndex: Z) (min: Z) (l_lowcost_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH10 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH11 : ((state_vertex_count (s_2)) = i)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH13 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH14 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH16 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i_2)) (PreH19 : (i_2 < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i_2)) (PreH23 : (i_2 < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH33 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= (state_vertex_count (s_2))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec 0 ) ” 
  &&  “ (INT_MIN <= 1000000000) ” 
  &&  “ (1000000000 <= INT_MAX) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((state_vertex_count (s_2)) - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_3 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_3 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s 0 1000000000 (-1) l_lowcost_3 l_edge_parent ) ” 
  &&  “ (((-1) = (-1)) -> (1000000000 = 1000000000)) ” 
  &&  “ (((-1) <> (-1)) -> (1000000000 = (Znth ((-1)) (l_lowcost_3) (0)))) ” 
  &&  “ (((-1) <> (-1)) -> ((0 <= (-1)) /\ ((-1) < 0))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_17_2_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i_2: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH10 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH11 : ((state_vertex_count (s_2)) = i)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH13 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH14 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH16 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i_2)) (PreH19 : (i_2 < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i_2 = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH33 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
|--
  EX (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= 1000000000) ” 
  &&  “ (1000000000 <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s 0 1000000000 (-1) l_lowcost l_edge_parent ) ” 
  &&  “ (((-1) = (-1)) -> (1000000000 = 1000000000)) ” 
  &&  “ (((-1) <> (-1)) -> (1000000000 = (Znth ((-1)) (l_lowcost) (0)))) ” 
  &&  “ (((-1) <> (-1)) -> ((0 <= (-1)) /\ ((-1) < 0))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i_2: Z) (minIndex: Z) (min: Z) (l_lowcost_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH10 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH11 : ((state_vertex_count (s_2)) = i)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH13 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH14 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH16 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i_2)) (PreH19 : (i_2 < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i_2 = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH33 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= (state_vertex_count (s_2))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec 0 ) ” 
  &&  “ (INT_MIN <= 1000000000) ” 
  &&  “ (1000000000 <= INT_MAX) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((state_vertex_count (s_2)) - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_3 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_3 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s 0 1000000000 (-1) l_lowcost_3 l_edge_parent ) ” 
  &&  “ (((-1) = (-1)) -> (1000000000 = 1000000000)) ” 
  &&  “ (((-1) <> (-1)) -> (1000000000 = (Znth ((-1)) (l_lowcost_3) (0)))) ” 
  &&  “ (((-1) <> (-1)) -> ((0 <= (-1)) /\ ((-1) < 0))) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_18_1_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (growing_subgraph_state g_low_level_spec s_after )) (PreH15 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH16 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH17 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH18 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH19 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  EX (l_lowcost_2: (@list Z))  (l_edge_parent_2: (@list E))  (l_visited_2: (@list Z))  (s: St) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_2 ) ” 
  &&  “ (((i + 1 ) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((i + 1 ) - 1 ))) X_low_level_spec ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (growing_subgraph_state g_low_level_spec s_after )) (PreH15 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH16 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH17 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH18 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH19 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent_2: (@list E))  (s: St) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent_2 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent_2 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (((i + 1 ) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent_2 1000000000 )) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((i + 1 ) - 1 ))) X_low_level_spec ) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i < n_pre) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_18_2_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i_2: Z) (minIndex_2: Z) (min_2: Z) (visited: Z) (lowcost: Z) (PreH1 : (0 <= i_2)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= minIndex_2)) (PreH4 : (minIndex_2 < n_pre)) (PreH5 : (i_2 = 0)) (PreH6 : (minIndex_2 = 0)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min_2)) (PreH13 : (min_2 <= INT_MAX)) (PreH14 : (growing_subgraph_state g_low_level_spec s_after )) (PreH15 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH16 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH17 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH18 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH19 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i_2)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  EX (l_lowcost_3: (@list Z))  (l_edge_parent_3: (@list E))  (l_visited_3: (@list Z))  (s_2: St) ,
  “ (1 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_2 ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_2 l_visited_3 ) ” 
  &&  “ ((state_vertex_count (s_2)) = (i_2 + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_2 l_lowcost_3 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_3 ) ” 
  &&  “ (((i_2 + 1 ) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) ” 
  &&  “ (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) (((i_2 + 1 ) - 1 ))) X_low_level_spec ) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ (0 <= minIndex_2) ” 
  &&  “ (minIndex_2 < n_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (minIndex_2 = 0) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min_2) ” 
  &&  “ (min_2 <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i_2 + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i_2: Z) (minIndex_2: Z) (min_2: Z) (PreH1 : (0 <= i_2)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= minIndex_2)) (PreH4 : (minIndex_2 < n_pre)) (PreH5 : (i_2 = 0)) (PreH6 : (minIndex_2 = 0)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min_2)) (PreH13 : (min_2 <= INT_MAX)) (PreH14 : (growing_subgraph_state g_low_level_spec s_after )) (PreH15 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH16 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH17 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH18 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH19 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i_2)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent_3: (@list E))  (s_2: St) ,
  “ (1 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_2 ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_2 l_visited ) ” 
  &&  “ ((state_vertex_count (s_2)) = (0 + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_2 l_edge_parent_3 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_2 l_lowcost l_edge_parent_3 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_2 l_lowcost ) ” 
  &&  “ (((0 + 1 ) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost l_edge_parent_3 1000000000 )) ” 
  &&  “ (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) (((0 + 1 ) - 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_19_1_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH10 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH11 : ((state_vertex_count (s_2)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH13 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH14 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
|--
  EX (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St)  (l_lowcost: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (lowcost_prefix_sum (0) (l_lowcost))) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = n_pre) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (l_lowcost_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH10 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH11 : ((state_vertex_count (s_2)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH13 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH14 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (lowcost_prefix_sum (0) (l_lowcost_3))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec 0 ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_3 ) ” 
  &&  “ ((state_vertex_count (s)) = n_pre) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_3 ) ” 
  &&  “ (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_19_2_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (lowcost: Z) (visited: Z) (l_lowcost_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH10 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH11 : ((state_vertex_count (s_2)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH13 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH14 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
|--
  EX (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St)  (l_lowcost: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (lowcost_prefix_sum (0) (l_lowcost))) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = n_pre) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (l_lowcost_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH10 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH11 : ((state_vertex_count (s_2)) = i_2)) (PreH12 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH13 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH14 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH15 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH16 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= minIndex)) (PreH21 : (minIndex < n_pre)) (PreH22 : (i = 0)) (PreH23 : (minIndex = 0)) (PreH24 : (src_low_level_spec = 0)) (PreH25 : (2 <= n_pre)) (PreH26 : (n_pre < INT_MAX)) (PreH27 : (prim_input_weight_bound n_pre 1000000000 )) (PreH28 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH29 : (INT_MIN <= min)) (PreH30 : (min <= INT_MAX)) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH35 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (lowcost_prefix_sum (0) (l_lowcost_3))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec 0 ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_3 ) ” 
  &&  “ ((state_vertex_count (s)) = n_pre) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_3 ) ” 
  &&  “ (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_20_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (l_lowcost_2: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost_2)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH11 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH12 : ((state_vertex_count (s_2)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH14 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH15 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH17 : (safeExec (prim_state_is (s_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
|--
  EX (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St)  (l_lowcost: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((ret + (Znth i l_lowcost_2 0) ) = (lowcost_prefix_sum ((i + 1 )) (l_lowcost))) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = n_pre) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (l_lowcost_2: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost_2)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH11 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH12 : ((state_vertex_count (s_2)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH14 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH15 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH17 : (safeExec (prim_state_is (s_2)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (state_vertex_count (s_2))) ” 
  &&  “ (((lowcost_prefix_sum (i) (l_lowcost_2)) + (Znth i l_lowcost_2 0) ) = (lowcost_prefix_sum ((i + 1 )) (l_lowcost_2))) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_entail_wit_21_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (l_lowcost_2: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost_2)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH11 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH12 : ((state_vertex_count (s_2)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH14 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH15 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH17 : (safeExec (prim_state_is (s_2)) (return (tt)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (rg: G)  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St)  (l_lowcost: (@list Z)) ,
  “ (ret = (lowcost_prefix_sum (n_pre) (l_lowcost))) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = n_pre) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (prim_state_graph_matches rg s ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_weight rg ret ) ” 
  &&  “ (prim_result_weight_in_int64_range rg ) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (l_lowcost_2: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost_2)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH11 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH12 : ((state_vertex_count (s_2)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH14 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH15 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH17 : (safeExec (prim_state_is (s_2)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (rg: G)  (l_edge_parent: (@list E))  (s: St) ,
  “ (i = (state_vertex_count (s_2))) ” 
  &&  “ ((lowcost_prefix_sum (i) (l_lowcost_2)) = (lowcost_prefix_sum ((state_vertex_count (s_2))) (l_lowcost_2))) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (prim_state_graph_matches rg s ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_weight rg (lowcost_prefix_sum (i) (l_lowcost_2)) ) ” 
  &&  “ (prim_result_weight_in_int64_range rg ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_wit_1_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_edge_parent: (@list E)) (s: St) (rg_2: G) (ret: Z) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (PreH1 : (ret = (lowcost_prefix_sum (n_pre) (l_lowcost)))) (PreH2 : (src_low_level_spec = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (growing_subgraph_state g_low_level_spec s )) (PreH8 : (visited_matches_state g_low_level_spec s l_visited )) (PreH9 : ((state_vertex_count (s)) = n_pre)) (PreH10 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH11 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH12 : (lowcost_sum_matches_state s l_lowcost )) (PreH13 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH14 : (prim_state_graph_matches rg_2 s )) (PreH15 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) (PreH16 : (prim_result_weight rg_2 ret )) (PreH17 : (prim_result_weight_in_int64_range rg_2 )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  EX (rg: G) ,
  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_weight rg ret ) ” 
  &&  “ (prim_result_weight_in_int64_range rg ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_edge_parent: (@list E)) (s: St) (rg_2: G) (ret: Z) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (PreH1 : (ret = (lowcost_prefix_sum (n_pre) (l_lowcost)))) (PreH2 : (src_low_level_spec = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (growing_subgraph_state g_low_level_spec s )) (PreH8 : (visited_matches_state g_low_level_spec s l_visited )) (PreH9 : ((state_vertex_count (s)) = n_pre)) (PreH10 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH11 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH12 : (lowcost_sum_matches_state s l_lowcost )) (PreH13 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH14 : (prim_state_graph_matches rg_2 s )) (PreH15 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) (PreH16 : (prim_result_weight rg_2 ret )) (PreH17 : (prim_result_weight_in_int64_range rg_2 )) ,
  TT && emp 
|--
  EX (rg: G) ,
  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_weight rg (lowcost_prefix_sum ((state_vertex_count (s))) (l_lowcost)) ) ” 
  &&  “ (prim_result_weight_in_int64_range rg ) ”
  &&  emp
).

Definition prim_adjacency_matrix_partial_solve_wit_1_pure := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "visited" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (n_pre > 0) ”
.

Definition prim_adjacency_matrix_partial_solve_wit_1_aux := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (n_pre > 0) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_partial_solve_wit_1 := prim_adjacency_matrix_partial_solve_wit_1_pure -> prim_adjacency_matrix_partial_solve_wit_1_aux.

Definition prim_adjacency_matrix_partial_solve_wit_2 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (IntArray.undef_seg visited i n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((visited + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg visited (i + 1 ) n_pre )
  **  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_partial_solve_wit_3_pure := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "lowcost" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (IntArray.undef_seg visited i n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (n_pre > 0) ”
.

Definition prim_adjacency_matrix_partial_solve_wit_3_aux := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (IntArray.undef_seg visited i n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (n_pre > 0) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_partial_solve_wit_3 := prim_adjacency_matrix_partial_solve_wit_3_pure -> prim_adjacency_matrix_partial_solve_wit_3_aux.

Definition prim_adjacency_matrix_partial_solve_wit_4 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (IntArray.undef_seg lowcost i n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((lowcost + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg lowcost (i + 1 ) n_pre )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_partial_solve_wit_5 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (lowcost: Z) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (prim_input_weight_bound n_pre 1000000000 )) (PreH5 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH6 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
|--
  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((lowcost + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i lowcost 0 0 n_pre (repeat_Z (1000000000) (n_pre)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
.

Definition prim_adjacency_matrix_partial_solve_wit_6_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (i = 0)) (PreH14 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH15 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH16 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH17 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH18 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH19 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH20 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH21 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ” 
  &&  “ ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1)))) ” 
  &&  “ ((1 <= j) -> ((min = 0) /\ (minIndex = 0))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j))) ” 
  &&  “ (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (l_edge_parent = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth j l_visited 0))
  **  (IntArray.missing_i visited j 0 n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
.

Definition prim_adjacency_matrix_partial_solve_wit_7_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (1 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH16 : (growing_subgraph_state g_low_level_spec s )) (PreH17 : (visited_matches_state g_low_level_spec s l_visited )) (PreH18 : ((state_vertex_count (s)) = i)) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH20 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH21 : (lowcost_sum_matches_state s l_lowcost )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH24 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH25 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH26 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH27 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent ) ” 
  &&  “ ((minIndex = (-1)) -> (min = 1000000000)) ” 
  &&  “ ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0)))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j))) ”
  &&  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth j l_visited 0))
  **  (IntArray.missing_i visited j 0 n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
.

Definition prim_adjacency_matrix_partial_solve_wit_8_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited 0) = 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s )) (PreH18 : (visited_matches_state g_low_level_spec s l_visited )) (PreH19 : ((state_vertex_count (s)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH21 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH22 : (lowcost_sum_matches_state s l_lowcost )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH24 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH25 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH26 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH27 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH28 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ ((Znth j l_visited 0) = 0) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent ) ” 
  &&  “ ((minIndex = (-1)) -> (min = 1000000000)) ” 
  &&  “ ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0)))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j))) ”
  &&  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth j l_lowcost 0))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_partial_solve_wit_9_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited 0) = 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH17 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH18 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ ((Znth j l_visited 0) = 0) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ” 
  &&  “ ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1)))) ” 
  &&  “ ((1 <= j) -> ((min = 0) /\ (minIndex = 0))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j))) ” 
  &&  “ (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (l_edge_parent = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth j l_lowcost 0))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_partial_solve_wit_10_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) < min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ ((Znth j l_lowcost 0) < min) ” 
  &&  “ ((Znth j l_visited 0) = 0) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ” 
  &&  “ ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1)))) ” 
  &&  “ ((1 <= j) -> ((min = 0) /\ (minIndex = 0))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j))) ” 
  &&  “ (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (l_edge_parent = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth j l_lowcost 0))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_partial_solve_wit_11_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) < min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s )) (PreH19 : (visited_matches_state g_low_level_spec s l_visited )) (PreH20 : ((state_vertex_count (s)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH22 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH23 : (lowcost_sum_matches_state s l_lowcost )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ ((Znth j l_lowcost 0) < min) ” 
  &&  “ ((Znth j l_visited 0) = 0) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent ) ” 
  &&  “ ((minIndex = (-1)) -> (min = 1000000000)) ” 
  &&  “ ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0)))) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j))) ”
  &&  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth j l_lowcost 0))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_partial_solve_wit_12_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : (min = 0)) (PreH17 : (minIndex = 0)) (PreH18 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH19 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH20 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH21 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (minIndex < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (min = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre))))) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (l_edge_parent = (default_edge_list (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (((visited + (minIndex * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i visited minIndex 0 n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
.

Definition prim_adjacency_matrix_partial_solve_wit_13_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s )) (PreH18 : (visited_matches_state g_low_level_spec s l_visited )) (PreH19 : ((state_vertex_count (s)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH21 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH22 : (lowcost_sum_matches_state s l_lowcost )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH24 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH25 : (minIndex <> (-1))) (PreH26 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH29 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (minIndex < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = i) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (minIndex <> (-1)) ” 
  &&  “ (min = (Znth (minIndex) (l_lowcost) (0))) ” 
  &&  “ (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex ) ” 
  &&  “ (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v ) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent ) ”
  &&  (((visited + (minIndex * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i visited minIndex 0 n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
.

Definition prim_adjacency_matrix_partial_solve_wit_14_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (l_lowcost: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (ret = (lowcost_prefix_sum (i) (l_lowcost)))) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited )) (PreH12 : ((state_vertex_count (s)) = n_pre)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH14 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH15 : (lowcost_sum_matches_state s l_lowcost )) (PreH16 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH17 : (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (ret = (lowcost_prefix_sum (i) (l_lowcost))) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = n_pre) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s)) (return (tt)) X_low_level_spec ) ”
  &&  (((lowcost + (i * sizeof(INT)))) # Int  |-> (Znth i l_lowcost 0))
  **  (IntArray.missing_i lowcost i 0 n_pre l_lowcost )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
.

Definition prim_adjacency_matrix_partial_solve_wit_15_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_edge_parent: (@list E)) (s: St) (rg: G) (ret: Z) (visited: Z) (lowcost: Z) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (PreH1 : (ret = (lowcost_prefix_sum (n_pre) (l_lowcost)))) (PreH2 : (src_low_level_spec = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (growing_subgraph_state g_low_level_spec s )) (PreH8 : (visited_matches_state g_low_level_spec s l_visited )) (PreH9 : ((state_vertex_count (s)) = n_pre)) (PreH10 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH11 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH12 : (lowcost_sum_matches_state s l_lowcost )) (PreH13 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH14 : (prim_state_graph_matches rg s )) (PreH15 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) (PreH16 : (prim_result_weight rg ret )) (PreH17 : (prim_result_weight_in_int64_range rg )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (ret = (lowcost_prefix_sum (n_pre) (l_lowcost))) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = n_pre) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (prim_state_graph_matches rg s ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_weight rg ret ) ” 
  &&  “ (prim_result_weight_in_int64_range rg ) ”
  &&  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
.

Definition prim_adjacency_matrix_partial_solve_wit_16_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_edge_parent: (@list E)) (s: St) (rg: G) (ret: Z) (lowcost: Z) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (PreH1 : (ret = (lowcost_prefix_sum (n_pre) (l_lowcost)))) (PreH2 : (src_low_level_spec = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (growing_subgraph_state g_low_level_spec s )) (PreH8 : (visited_matches_state g_low_level_spec s l_visited )) (PreH9 : ((state_vertex_count (s)) = n_pre)) (PreH10 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH11 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH12 : (lowcost_sum_matches_state s l_lowcost )) (PreH13 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH14 : (prim_state_graph_matches rg s )) (PreH15 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) (PreH16 : (prim_result_weight rg ret )) (PreH17 : (prim_result_weight_in_int64_range rg )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
|--
  “ (ret = (lowcost_prefix_sum (n_pre) (l_lowcost))) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = n_pre) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (prim_state_graph_matches rg s ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_weight rg ret ) ” 
  &&  “ (prim_result_weight_in_int64_range rg ) ”
  &&  (IntArray.full lowcost n_pre l_lowcost )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_derive_high_level_spec_by_low_level_spec := 
forall (graph_pre: Z) (n_pre: Z) (src_high_level_spec: Z) (g_high_level_spec: G) (matrix_high_level_spec: (@list (@list Z))) ,
  “ (src_high_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_high_level_spec src_high_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_high_level_spec) (1000000000)) graph_pre matrix_high_level_spec )
|--
EX (matrix_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (src_low_level_spec: Z) (X_low_level_spec: (unit -> (St -> Prop))) ,
  (“ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec ))
  **
  ((EX rg_2 retval_2,
  “ (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_weight rg_2 retval_2 ) ” 
  &&  “ (prim_result_weight_in_int64_range rg_2 ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec ))
  -*
  (EX rg retval,
  “ (return_is_mst g_high_level_spec rg ) ” 
  &&  “ (prim_result_weight rg retval ) ” 
  &&  “ (prim_result_weight_in_int64_range rg ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_high_level_spec) (1000000000)) graph_pre matrix_high_level_spec )))
.

Module Type VC_Correct.

Include int_ptr_array2_Strategy_Correct.
Include int_array_Strategy_Correct.
Include array2_Strategy_Correct.
Include graph_matrix_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_prim_adjacency_matrix_safety_wit_1 : prim_adjacency_matrix_safety_wit_1.
Axiom proof_of_prim_adjacency_matrix_safety_wit_2 : prim_adjacency_matrix_safety_wit_2.
Axiom proof_of_prim_adjacency_matrix_safety_wit_3 : prim_adjacency_matrix_safety_wit_3.
Axiom proof_of_prim_adjacency_matrix_safety_wit_4 : prim_adjacency_matrix_safety_wit_4.
Axiom proof_of_prim_adjacency_matrix_safety_wit_5 : prim_adjacency_matrix_safety_wit_5.
Axiom proof_of_prim_adjacency_matrix_safety_wit_6 : prim_adjacency_matrix_safety_wit_6.
Axiom proof_of_prim_adjacency_matrix_safety_wit_7 : prim_adjacency_matrix_safety_wit_7.
Axiom proof_of_prim_adjacency_matrix_safety_wit_8 : prim_adjacency_matrix_safety_wit_8.
Axiom proof_of_prim_adjacency_matrix_safety_wit_9 : prim_adjacency_matrix_safety_wit_9.
Axiom proof_of_prim_adjacency_matrix_safety_wit_10_boot : prim_adjacency_matrix_safety_wit_10_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_11_boot : prim_adjacency_matrix_safety_wit_11_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_12_boot : prim_adjacency_matrix_safety_wit_12_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_13_boot : prim_adjacency_matrix_safety_wit_13_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_14_boot : prim_adjacency_matrix_safety_wit_14_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_15_boot : prim_adjacency_matrix_safety_wit_15_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_16_boot : prim_adjacency_matrix_safety_wit_16_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_17_boot : prim_adjacency_matrix_safety_wit_17_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_18_boot : prim_adjacency_matrix_safety_wit_18_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_19_boot : prim_adjacency_matrix_safety_wit_19_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_20_boot : prim_adjacency_matrix_safety_wit_20_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_21_boot : prim_adjacency_matrix_safety_wit_21_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_22_boot : prim_adjacency_matrix_safety_wit_22_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_23_boot : prim_adjacency_matrix_safety_wit_23_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_24_boot : prim_adjacency_matrix_safety_wit_24_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_25_boot : prim_adjacency_matrix_safety_wit_25_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_26_boot : prim_adjacency_matrix_safety_wit_26_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_27_boot : prim_adjacency_matrix_safety_wit_27_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_28_boot : prim_adjacency_matrix_safety_wit_28_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_29_boot : prim_adjacency_matrix_safety_wit_29_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_30_boot : prim_adjacency_matrix_safety_wit_30_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_31_boot : prim_adjacency_matrix_safety_wit_31_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_32_boot : prim_adjacency_matrix_safety_wit_32_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_33_boot : prim_adjacency_matrix_safety_wit_33_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_34_boot : prim_adjacency_matrix_safety_wit_34_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_35_boot : prim_adjacency_matrix_safety_wit_35_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_36_boot : prim_adjacency_matrix_safety_wit_36_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_37_boot : prim_adjacency_matrix_safety_wit_37_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_38_boot : prim_adjacency_matrix_safety_wit_38_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_39_boot : prim_adjacency_matrix_safety_wit_39_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_40_boot : prim_adjacency_matrix_safety_wit_40_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_41_boot : prim_adjacency_matrix_safety_wit_41_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_42_boot : prim_adjacency_matrix_safety_wit_42_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_43_boot : prim_adjacency_matrix_safety_wit_43_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_44_boot : prim_adjacency_matrix_safety_wit_44_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_45_running : prim_adjacency_matrix_safety_wit_45_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_46_running : prim_adjacency_matrix_safety_wit_46_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_47_running : prim_adjacency_matrix_safety_wit_47_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_48_running : prim_adjacency_matrix_safety_wit_48_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_49_running : prim_adjacency_matrix_safety_wit_49_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_50_running : prim_adjacency_matrix_safety_wit_50_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_51_running : prim_adjacency_matrix_safety_wit_51_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_52_running : prim_adjacency_matrix_safety_wit_52_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_53_boot : prim_adjacency_matrix_safety_wit_53_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_54_boot : prim_adjacency_matrix_safety_wit_54_boot.
Axiom proof_of_prim_adjacency_matrix_safety_wit_55_running : prim_adjacency_matrix_safety_wit_55_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_56_running : prim_adjacency_matrix_safety_wit_56_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_57_running : prim_adjacency_matrix_safety_wit_57_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_58_running : prim_adjacency_matrix_safety_wit_58_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_59_running : prim_adjacency_matrix_safety_wit_59_running.
Axiom proof_of_prim_adjacency_matrix_safety_wit_60_running : prim_adjacency_matrix_safety_wit_60_running.
Axiom proof_of_prim_adjacency_matrix_entail_wit_1 : prim_adjacency_matrix_entail_wit_1.
Axiom proof_of_prim_adjacency_matrix_entail_wit_2 : prim_adjacency_matrix_entail_wit_2.
Axiom proof_of_prim_adjacency_matrix_entail_wit_3 : prim_adjacency_matrix_entail_wit_3.
Axiom proof_of_prim_adjacency_matrix_entail_wit_4 : prim_adjacency_matrix_entail_wit_4.
Axiom proof_of_prim_adjacency_matrix_entail_wit_5 : prim_adjacency_matrix_entail_wit_5.
Axiom proof_of_prim_adjacency_matrix_entail_wit_6_boot : prim_adjacency_matrix_entail_wit_6_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_7_boot : prim_adjacency_matrix_entail_wit_7_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_8_1_boot : prim_adjacency_matrix_entail_wit_8_1_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_8_2_boot : prim_adjacency_matrix_entail_wit_8_2_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_8_3_boot : prim_adjacency_matrix_entail_wit_8_3_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_8_4_boot : prim_adjacency_matrix_entail_wit_8_4_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_8_5_boot : prim_adjacency_matrix_entail_wit_8_5_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_8_6_boot : prim_adjacency_matrix_entail_wit_8_6_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_9_1_boot : prim_adjacency_matrix_entail_wit_9_1_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_9_2_boot : prim_adjacency_matrix_entail_wit_9_2_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_10_1_boot : prim_adjacency_matrix_entail_wit_10_1_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_10_2_boot : prim_adjacency_matrix_entail_wit_10_2_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_11_1_boot : prim_adjacency_matrix_entail_wit_11_1_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_11_2_boot : prim_adjacency_matrix_entail_wit_11_2_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_12_1_boot : prim_adjacency_matrix_entail_wit_12_1_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_12_2_boot : prim_adjacency_matrix_entail_wit_12_2_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_13_1_boot : prim_adjacency_matrix_entail_wit_13_1_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_13_2_boot : prim_adjacency_matrix_entail_wit_13_2_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_14_1_boot : prim_adjacency_matrix_entail_wit_14_1_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_14_2_boot : prim_adjacency_matrix_entail_wit_14_2_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_14_3_boot : prim_adjacency_matrix_entail_wit_14_3_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_14_4_boot : prim_adjacency_matrix_entail_wit_14_4_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_14_5_boot : prim_adjacency_matrix_entail_wit_14_5_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_14_6_boot : prim_adjacency_matrix_entail_wit_14_6_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_14_7_boot : prim_adjacency_matrix_entail_wit_14_7_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_14_8_boot : prim_adjacency_matrix_entail_wit_14_8_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_15_1_boot : prim_adjacency_matrix_entail_wit_15_1_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_15_2_boot : prim_adjacency_matrix_entail_wit_15_2_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_16_1_boot : prim_adjacency_matrix_entail_wit_16_1_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_16_2_boot : prim_adjacency_matrix_entail_wit_16_2_boot.
Axiom proof_of_prim_adjacency_matrix_entail_wit_17_1_running : prim_adjacency_matrix_entail_wit_17_1_running.
Axiom proof_of_prim_adjacency_matrix_entail_wit_17_2_running : prim_adjacency_matrix_entail_wit_17_2_running.
Axiom proof_of_prim_adjacency_matrix_entail_wit_18_1_running : prim_adjacency_matrix_entail_wit_18_1_running.
Axiom proof_of_prim_adjacency_matrix_entail_wit_18_2_running : prim_adjacency_matrix_entail_wit_18_2_running.
Axiom proof_of_prim_adjacency_matrix_entail_wit_19_1_running : prim_adjacency_matrix_entail_wit_19_1_running.
Axiom proof_of_prim_adjacency_matrix_entail_wit_19_2_running : prim_adjacency_matrix_entail_wit_19_2_running.
Axiom proof_of_prim_adjacency_matrix_entail_wit_20_running : prim_adjacency_matrix_entail_wit_20_running.
Axiom proof_of_prim_adjacency_matrix_entail_wit_21_running : prim_adjacency_matrix_entail_wit_21_running.
Axiom proof_of_prim_adjacency_matrix_return_wit_1_running : prim_adjacency_matrix_return_wit_1_running.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_1_pure : prim_adjacency_matrix_partial_solve_wit_1_pure.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_1 : prim_adjacency_matrix_partial_solve_wit_1.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_2 : prim_adjacency_matrix_partial_solve_wit_2.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_3_pure : prim_adjacency_matrix_partial_solve_wit_3_pure.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_3 : prim_adjacency_matrix_partial_solve_wit_3.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_4 : prim_adjacency_matrix_partial_solve_wit_4.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_5 : prim_adjacency_matrix_partial_solve_wit_5.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_6_boot : prim_adjacency_matrix_partial_solve_wit_6_boot.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_7_boot : prim_adjacency_matrix_partial_solve_wit_7_boot.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_8_boot : prim_adjacency_matrix_partial_solve_wit_8_boot.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_9_boot : prim_adjacency_matrix_partial_solve_wit_9_boot.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_10_boot : prim_adjacency_matrix_partial_solve_wit_10_boot.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_11_boot : prim_adjacency_matrix_partial_solve_wit_11_boot.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_12_boot : prim_adjacency_matrix_partial_solve_wit_12_boot.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_13_boot : prim_adjacency_matrix_partial_solve_wit_13_boot.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_14_running : prim_adjacency_matrix_partial_solve_wit_14_running.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_15_running : prim_adjacency_matrix_partial_solve_wit_15_running.
Axiom proof_of_prim_adjacency_matrix_partial_solve_wit_16_running : prim_adjacency_matrix_partial_solve_wit_16_running.
Axiom proof_of_prim_adjacency_matrix_derive_high_level_spec_by_low_level_spec : prim_adjacency_matrix_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
