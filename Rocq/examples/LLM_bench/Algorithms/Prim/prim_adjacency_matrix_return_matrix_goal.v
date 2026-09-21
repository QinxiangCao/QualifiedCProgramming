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

(*----- Function prim_adjacency_matrix_return_matrix -----*)

Definition prim_adjacency_matrix_return_matrix_safety_wit_1 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (retval: Z) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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

Definition prim_adjacency_matrix_return_matrix_safety_wit_2 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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

Definition prim_adjacency_matrix_return_matrix_safety_wit_3 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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

Definition prim_adjacency_matrix_return_matrix_safety_wit_4 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (retval: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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

Definition prim_adjacency_matrix_return_matrix_safety_wit_5 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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

Definition prim_adjacency_matrix_return_matrix_safety_wit_6 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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

Definition prim_adjacency_matrix_return_matrix_safety_wit_7 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (retval: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.undef_full retval n_pre )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_8 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg vertex_parent i n_pre )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_9 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg vertex_parent i n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_10 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg vertex_parent 0 (i + 1 ) (app ((repeat_Z ((-1)) (i))) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg vertex_parent (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_11 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg vertex_parent i n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_12 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg vertex_parent i n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_13 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_14_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (i: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (i_2 = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (i >= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre (repeat_Z ((-1)) (n_pre)) )
|--
  “ False ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_15_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (i: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (i_2 = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (i >= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre (repeat_Z ((-1)) (n_pre)) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_16_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (i: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (i_2 = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (i >= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre (repeat_Z ((-1)) (n_pre)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_17_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (i: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (i_2 = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (i >= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "min" ) )) # Int  |->_)
  **  ((( &( "minIndex" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre (repeat_Z ((-1)) (n_pre)) )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_18_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (i: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (i_2 = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (i >= n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "min" ) )) # Int  |-> 1000000000)
  **  ((( &( "minIndex" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre (repeat_Z ((-1)) (n_pre)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_19_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH17 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH18 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH23 : (l_visited = (repeat_Z (0) (n_pre)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_20_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s )) (PreH18 : (visited_matches_state g_low_level_spec s l_visited )) (PreH19 : ((state_vertex_count (s)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH21 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH22 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH23 : (lowcost_sum_matches_state s l_lowcost )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_21_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) < min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited = (repeat_Z (0) (n_pre)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_22_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) < min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s )) (PreH20 : (visited_matches_state g_low_level_spec s l_visited )) (PreH21 : ((state_vertex_count (s)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH23 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH24 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH25 : (lowcost_sum_matches_state s l_lowcost )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH27 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH28 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH29 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH30 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH31 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_23_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s )) (PreH19 : (visited_matches_state g_low_level_spec s l_visited )) (PreH20 : ((state_vertex_count (s)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH22 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH23 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH24 : (lowcost_sum_matches_state s l_lowcost )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH26 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH27 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH28 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH29 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH30 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_24_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited = (repeat_Z (0) (n_pre)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_25_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) >= min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited = (repeat_Z (0) (n_pre)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_26_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) >= min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s )) (PreH20 : (visited_matches_state g_low_level_spec s l_visited )) (PreH21 : ((state_vertex_count (s)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH23 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH24 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH25 : (lowcost_sum_matches_state s l_lowcost )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH27 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH28 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH29 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH30 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH31 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_27_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (i = 0)) (PreH14 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH15 : (min = 0)) (PreH16 : (minIndex = 0)) (PreH17 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH18 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH19 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH20 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH21 : (l_visited = (repeat_Z (0) (n_pre)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_28_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (INT_MIN <= min)) (PreH12 : (min <= INT_MAX)) (PreH13 : (1 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH16 : (growing_subgraph_state g_low_level_spec s )) (PreH17 : (visited_matches_state g_low_level_spec s l_visited )) (PreH18 : ((state_vertex_count (s)) = i)) (PreH19 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH20 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH21 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH22 : (lowcost_sum_matches_state s l_lowcost )) (PreH23 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH24 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH25 : (minIndex <> (-1))) (PreH26 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH29 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_29_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 > minIndex)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= minIndex)) (PreH5 : (minIndex < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : (min = 0)) (PreH17 : (minIndex = 0)) (PreH18 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH19 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH20 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH21 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH22 : (l_visited = (repeat_Z (0) (n_pre)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ False ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_30_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 > minIndex)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= minIndex)) (PreH5 : (minIndex < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s )) (PreH18 : (visited_matches_state g_low_level_spec s l_visited )) (PreH19 : ((state_vertex_count (s)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH21 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH22 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH23 : (lowcost_sum_matches_state s l_lowcost )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH25 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH26 : (minIndex <> (-1))) (PreH27 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH28 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH29 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH30 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ False ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_31_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex >= n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s )) (PreH19 : (visited_matches_state g_low_level_spec s l_visited )) (PreH20 : ((state_vertex_count (s)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH22 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH23 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH24 : (lowcost_sum_matches_state s l_lowcost )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH26 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH27 : (minIndex <> (-1))) (PreH28 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH29 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH30 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH31 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ False ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_32_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex >= n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH23 : (l_visited = (repeat_Z (0) (n_pre)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ False ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_33_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH23 : (l_visited = (repeat_Z (0) (n_pre)))) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_34_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s )) (PreH19 : (visited_matches_state g_low_level_spec s l_visited )) (PreH20 : ((state_vertex_count (s)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH22 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH23 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH24 : (lowcost_sum_matches_state s l_lowcost )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH26 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH27 : (minIndex <> (-1))) (PreH28 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH29 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH30 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH31 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_35_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (row_ptr: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH18 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s )) (PreH20 : (visited_matches_state g_low_level_spec s l_visited )) (PreH21 : ((state_vertex_count (s)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH23 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH24 : (lowcost_sum_matches_state s l_lowcost0 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after )) (PreH30 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH31 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH33 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH35 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent0 )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_36_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (s_after: St) (row_ptr: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (minIndex = 0)) (PreH17 : (min = 0)) (PreH18 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH19 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH20 : (growing_subgraph_state g_low_level_spec s_after )) (PreH21 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH22 : ((state_vertex_count (s_after)) = 1)) (PreH23 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH25 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH26 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH27 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH28 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH29 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent0 )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_37_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (u: Z) (v: Z) (l_edge_parent0: (@list E)) (l_visited: (@list Z)) (s: St) (s_after: St) (l_lowcost0: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (INT_MIN <= min)) (PreH17 : (min <= INT_MAX)) (PreH18 : (1 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s )) (PreH23 : (visited_matches_state g_low_level_spec s l_visited )) (PreH24 : ((state_vertex_count (s)) = i)) (PreH25 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH26 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH29 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after )) (PreH31 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH32 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH34 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH37 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH38 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH40 : (0 <= j)) (PreH41 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_38_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_edge_parent0: (@list E)) (l_lowcost0: (@list Z)) (l_visited: (@list Z)) (s_after: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (INT_MIN <= min)) (PreH17 : (min <= INT_MAX)) (PreH18 : (i = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (min = 0)) (PreH21 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH22 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_after )) (PreH24 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH25 : ((state_vertex_count (s_after)) = 1)) (PreH26 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH27 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH28 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH29 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH30 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH31 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH32 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH33 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH35 : (0 <= j)) (PreH36 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_39_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH2 : (w <> 1000000000)) (PreH3 : (0 <= j)) (PreH4 : (j < n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH19 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH20 : (growing_subgraph_state g_low_level_spec s )) (PreH21 : (visited_matches_state g_low_level_spec s l_visited )) (PreH22 : ((state_vertex_count (s)) = i)) (PreH23 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH24 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH25 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH26 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH27 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH28 : (growing_subgraph_state g_low_level_spec s_after )) (PreH29 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH30 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH31 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH32 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH33 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH34 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH35 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH36 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH37 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent) ((-1))))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_40_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH2 : (w <> 1000000000)) (PreH3 : (0 <= j)) (PreH4 : (j < n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (i = 0)) (PreH17 : (minIndex = 0)) (PreH18 : (min = 0)) (PreH19 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH20 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s_after )) (PreH22 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH23 : ((state_vertex_count (s_after)) = 1)) (PreH24 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH26 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH27 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH28 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH29 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH30 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH31 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH32 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent) ((-1))))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_41_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w < (Znth (j) (l_lowcost) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (i = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (min = 0)) (PreH21 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH22 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_after )) (PreH24 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH25 : ((state_vertex_count (s_after)) = 1)) (PreH26 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH27 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH28 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH29 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH30 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH31 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH32 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH33 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> minIndex)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_42_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w < (Znth (j) (l_lowcost) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (1 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s )) (PreH23 : (visited_matches_state g_low_level_spec s l_visited )) (PreH24 : ((state_vertex_count (s)) = i)) (PreH25 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH26 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH29 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after )) (PreH31 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH32 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH34 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH37 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH38 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> minIndex)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_43_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w >= (Znth (j) (l_lowcost) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (i = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (min = 0)) (PreH21 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH22 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_after )) (PreH24 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH25 : ((state_vertex_count (s_after)) = 1)) (PreH26 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH27 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH28 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH29 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH30 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH31 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH32 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH33 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent) ((-1))))
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_44_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w >= (Znth (j) (l_lowcost) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (1 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s )) (PreH23 : (visited_matches_state g_low_level_spec s l_visited )) (PreH24 : ((state_vertex_count (s)) = i)) (PreH25 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH26 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH29 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after )) (PreH31 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH32 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH34 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH37 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH38 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent) ((-1))))
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_45_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s: St) (s_after: St) (u: Z) (v: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) <> 0)) (PreH2 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH3 : (w <> 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= minIndex)) (PreH9 : (minIndex < n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH20 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s )) (PreH22 : (visited_matches_state g_low_level_spec s l_visited )) (PreH23 : ((state_vertex_count (s)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH25 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after )) (PreH30 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH31 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH33 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH36 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH37 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH38 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent) ((-1))))
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_46_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent: (@list E)) (s_after: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited))) (0)) <> 0)) (PreH2 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH3 : (w <> 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= minIndex)) (PreH9 : (minIndex < n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after )) (PreH23 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH24 : ((state_vertex_count (s_after)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH27 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH29 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH31 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH32 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH33 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent) ((-1))))
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_47_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (u: Z) (v: Z) (l_edge_parent0: (@list E)) (l_visited: (@list Z)) (s: St) (s_after: St) (l_lowcost0: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (1 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH22 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s )) (PreH24 : (visited_matches_state g_low_level_spec s l_visited )) (PreH25 : ((state_vertex_count (s)) = i)) (PreH26 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH27 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH28 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH29 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH30 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH31 : (growing_subgraph_state g_low_level_spec s_after )) (PreH32 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH33 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH35 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH36 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH37 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH41 : (0 <= j)) (PreH42 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_48_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_edge_parent0: (@list E)) (l_lowcost0: (@list Z)) (l_visited: (@list Z)) (s_after: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (i = 0)) (PreH20 : (minIndex = 0)) (PreH21 : (min = 0)) (PreH22 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH23 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH24 : (growing_subgraph_state g_low_level_spec s_after )) (PreH25 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH26 : ((state_vertex_count (s_after)) = 1)) (PreH27 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH28 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH29 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH30 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH31 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH32 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH33 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH34 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH36 : (0 <= j)) (PreH37 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minIndex" ) )) # Int  |-> minIndex)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "selected_row" ) )) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_49_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (1 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_50_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (i = 0)) (PreH25 : (minIndex = 0)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_51_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (1 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_52_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (i = 0)) (PreH25 : (minIndex = 0)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
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
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_53_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (1 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_54_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (1 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_55_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (i = 0)) (PreH25 : (minIndex = 0)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_56_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (i = 0)) (PreH25 : (minIndex = 0)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "minIndex" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_57_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (growing_subgraph_state g_low_level_spec s_after )) (PreH16 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH17 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH18 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH19 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH20 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH21 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_58_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (i = 0)) (PreH6 : (minIndex = 0)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (growing_subgraph_state g_low_level_spec s_after )) (PreH16 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH17 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH18 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH19 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH20 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH21 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_59_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (growing_subgraph_state g_low_level_spec s )) (PreH12 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH13 : ((state_vertex_count (s)) = i_2)) (PreH14 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH15 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH16 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH17 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH18 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH19 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH20 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= minIndex)) (PreH24 : (minIndex < n_pre)) (PreH25 : (1 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (src_low_level_spec = 0)) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre < INT_MAX)) (PreH30 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH31 : (prim_input_weight_bound n_pre 1000000000 )) (PreH32 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH33 : (INT_MIN <= min)) (PreH34 : (min <= INT_MAX)) (PreH35 : (growing_subgraph_state g_low_level_spec s_after )) (PreH36 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH37 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH38 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH39 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH40 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH41 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  (PtrArray.undef_full retval n_pre )
  **  ((( &( "mst" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_60_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (growing_subgraph_state g_low_level_spec s )) (PreH12 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH13 : ((state_vertex_count (s)) = i_2)) (PreH14 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH15 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH16 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH17 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH18 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH19 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH20 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= minIndex)) (PreH24 : (minIndex < n_pre)) (PreH25 : (i = 0)) (PreH26 : (minIndex = 0)) (PreH27 : (src_low_level_spec = 0)) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre < INT_MAX)) (PreH30 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH31 : (prim_input_weight_bound n_pre 1000000000 )) (PreH32 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH33 : (INT_MIN <= min)) (PreH34 : (min <= INT_MAX)) (PreH35 : (growing_subgraph_state g_low_level_spec s_after )) (PreH36 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH37 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH38 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH39 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH40 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH41 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  (PtrArray.undef_full retval n_pre )
  **  ((( &( "mst" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_61_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (mst: Z) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (retval: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix = (inf_matrix (i) (n_pre) (1000000000)))) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> retval)
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (IntPtrArray2.full mst i result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_62_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (row_ptr: Z) (mst: Z) (row_prefix: (@list Z)) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after )) (PreH13 : ((state_vertex_count (s_after)) = n_pre)) (PreH14 : (prim_state_graph_matches rg s_after )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH17 : (result_matrix = (inf_matrix (i) (n_pre) (1000000000)))) (PreH18 : (row_prefix = (repeat_Z (1000000000) (j)))) (PreH19 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (IntPtrArray2.full mst i result_matrix )
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.seg row_ptr 0 j row_prefix )
  **  (IntArray.undef_seg row_ptr j n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_63_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (row_ptr: Z) (mst: Z) (row_prefix: (@list Z)) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after )) (PreH13 : ((state_vertex_count (s_after)) = n_pre)) (PreH14 : (prim_state_graph_matches rg s_after )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH17 : (result_matrix = (inf_matrix (i) (n_pre) (1000000000)))) (PreH18 : (row_prefix = (repeat_Z (1000000000) (j)))) (PreH19 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (IntArray.seg row_ptr 0 (j + 1 ) (app (row_prefix) ((cons (1000000000) ((@nil Z))))) )
  **  (IntArray.undef_seg row_ptr (j + 1 ) n_pre )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (IntPtrArray2.full mst i result_matrix )
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_64_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (row_ptr: Z) (mst: Z) (row_prefix: (@list Z)) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after )) (PreH13 : ((state_vertex_count (s_after)) = n_pre)) (PreH14 : (prim_state_graph_matches rg s_after )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH17 : (result_matrix = (inf_matrix (i) (n_pre) (1000000000)))) (PreH18 : (row_prefix = (repeat_Z (1000000000) (j)))) (PreH19 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (IntPtrArray2.full mst i result_matrix )
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.seg row_ptr 0 j row_prefix )
  **  (IntArray.undef_seg row_ptr j n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_65_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (mst: Z) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix = (inf_matrix (i) (n_pre) (1000000000)))) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (PtrArray.undef_seg mst i n_pre )
  **  (IntPtrArray2.full mst i result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_66_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (mst: Z) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full vertex_parent n_pre l_vertex_parent )
  **  ((( &( "p" ) )) # Int  |-> (Znth i l_vertex_parent 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_67_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (rg: G) (i: Z) (p: Z) (w: Z) (mst: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))) (PreH6 : (p = (Znth i l_vertex_parent 0))) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after )) (PreH14 : ((state_vertex_count (s_after)) = n_pre)) (PreH15 : (prim_state_graph_matches rg s_after )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec (set_undirected_matrix_entry (result_matrix) (p) (i) (w)) l_vertex_parent l_edge_parent 1000000000 (i + 1 ) )) (PreH19 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (IntPtrArray2.full mst n_pre (set_undirected_matrix_entry (result_matrix) (p) (i) (w)) )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_68_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (mst: Z) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (PreH1 : (0 > (Znth i l_vertex_parent 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (growing_subgraph_state g_low_level_spec s_after )) (PreH12 : ((state_vertex_count (s_after)) = n_pre)) (PreH13 : (prim_state_graph_matches rg s_after )) (PreH14 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH15 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH16 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH17 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full vertex_parent n_pre l_vertex_parent )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_safety_wit_69_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (mst: Z) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (PreH1 : ((Znth i l_vertex_parent 0) >= n_pre)) (PreH2 : (0 <= (Znth i l_vertex_parent 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after )) (PreH13 : ((state_vertex_count (s_after)) = n_pre)) (PreH14 : (prim_state_graph_matches rg s_after )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH17 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH18 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full vertex_parent n_pre l_vertex_parent )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_1 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (retval: Z) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.undef_full retval n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.seg retval 0 0 (repeat_Z (0) (0)) )
  **  (IntArray.undef_seg retval 0 n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((repeat_Z (0) (0)) = (@nil Z)) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z (0) (0)) = (@nil Z))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_2 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg visited 0 (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg visited (i + 1 ) n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.seg visited 0 (i + 1 ) (repeat_Z (0) ((i + 1 ))) )
  **  (IntArray.undef_seg visited (i + 1 ) n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 ))))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_3 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (retval: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.undef_full retval n_pre )
  **  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg retval 0 0 (repeat_Z (1000000000) (0)) )
  **  (IntArray.undef_seg retval 0 n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((repeat_Z (1000000000) (0)) = (@nil Z)) ” 
  &&  “ ((repeat_Z (0) (i)) = (repeat_Z (0) (n_pre))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z (1000000000) (0)) = (@nil Z))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z (0) (i)) = (repeat_Z (0) (n_pre)))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_4 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg lowcost 0 (i + 1 ) (repeat_Z (1000000000) ((i + 1 ))) )
  **  (IntArray.undef_seg lowcost (i + 1 ) n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (1000000000) (i))) ((cons (1000000000) ((@nil Z))))) = (repeat_Z (1000000000) ((i + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((app ((repeat_Z (1000000000) (i))) ((cons (1000000000) ((@nil Z))))) = (repeat_Z (1000000000) ((i + 1 ))))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_5 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (retval: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.undef_full retval n_pre )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  (IntArray.seg retval 0 0 (repeat_Z ((-1)) (0)) )
  **  (IntArray.undef_seg retval 0 n_pre )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((repeat_Z ((-1)) (0)) = (@nil Z)) ” 
  &&  “ ((repeat_Z (1000000000) (i)) = (repeat_Z (1000000000) (n_pre))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z ((-1)) (0)) = (@nil Z))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z (1000000000) (i)) = (repeat_Z (1000000000) (n_pre)))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_6 := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg vertex_parent 0 (i + 1 ) (app ((repeat_Z ((-1)) (i))) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg vertex_parent (i + 1 ) n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  (IntArray.seg vertex_parent 0 (i + 1 ) (repeat_Z ((-1)) ((i + 1 ))) )
  **  (IntArray.undef_seg vertex_parent (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((app ((repeat_Z ((-1)) (i))) ((cons ((-1)) ((@nil Z))))) = (repeat_Z ((-1)) ((i + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((app ((repeat_Z ((-1)) (i))) ((cons ((-1)) ((@nil Z))))) = (repeat_Z ((-1)) ((i + 1 ))))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_7_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
|--
  “ (0 = 0) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  (IntArray.full vertex_parent n_pre (repeat_Z ((-1)) (n_pre)) )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((repeat_Z ((-1)) (i)) = (repeat_Z ((-1)) (n_pre))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_7_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((repeat_Z ((-1)) (i)) = (repeat_Z ((-1)) (n_pre)))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_8_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (i_2: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (i_2 >= n_pre)) (PreH10 : (0 <= i_2)) (PreH11 : (i_2 <= n_pre)) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
  **  (IntArray.full vertex_parent n_pre (repeat_Z ((-1)) (n_pre)) )
|--
  EX (l_visited: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i_2: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (i_2 >= n_pre)) (PreH10 : (0 <= i_2)) (PreH11 : (i_2 <= n_pre)) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_8_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (i_2: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (i = 0)) (PreH3 : (src_low_level_spec = 0)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH7 : (prim_input_weight_bound n_pre 1000000000 )) (PreH8 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH9 : (i_2 >= n_pre)) (PreH10 : (0 <= i_2)) (PreH11 : (i_2 <= n_pre)) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) )
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH23 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_visited: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH23 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  TT && emp 
|--
  “ ((1 <= (j + 1 )) -> (((Znth j l_lowcost_2 0) = 0) /\ (j = 0))) ” 
  &&  “ (INT_MIN <= (Znth j l_lowcost_2 0)) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_1_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH23 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  ((1 <= (j + 1 )) -> (((Znth j l_lowcost_2 0) = 0) /\ (j = 0)))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_1_boot_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH23 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (INT_MIN <= (Znth j l_lowcost_2 0))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH20 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH21 : ((state_vertex_count (s_2)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH23 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH24 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH25 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH27 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH28 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH29 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH30 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH31 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) < min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH20 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH21 : ((state_vertex_count (s_2)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH23 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH24 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH25 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH27 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH28 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH29 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH30 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH31 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s (j + 1 ) 1000000000 j l_lowcost_2 l_edge_parent ) ” 
  &&  “ ((j = (-1)) -> ((Znth j l_lowcost_2 0) = 1000000000)) ” 
  &&  “ ((j <> (-1)) -> ((Znth j l_lowcost_2 0) = (Znth (j) (l_lowcost_2) (0)))) ” 
  &&  “ ((j <> (-1)) -> ((0 <= j) /\ (j < (j + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_3_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH22 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH23 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH24 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH26 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH27 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH28 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH29 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH30 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH22 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH23 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH24 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH26 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH27 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH28 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH29 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH30 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s (j + 1 ) 1000000000 minIndex l_lowcost_2 l_edge_parent ) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < (j + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_4_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_visited: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  TT && emp 
|--
  “ ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_4_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited_2 0) <> 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH22 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0)))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_5_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH23 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_visited: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH23 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  TT && emp 
|--
  “ ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_5_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH23 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  ((1 <= (j + 1 )) -> ((min = 0) /\ (minIndex = 0)))
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_9_6_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH20 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH21 : ((state_vertex_count (s_2)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH23 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH24 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH25 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH27 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH28 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH29 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH30 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH31 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost_2 0) >= min)) (PreH2 : ((Znth j l_visited_2 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH20 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH21 : ((state_vertex_count (s_2)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH23 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH24 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH25 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH27 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH28 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH29 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH30 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH31 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s (j + 1 ) 1000000000 minIndex l_lowcost_2 l_edge_parent ) ” 
  &&  “ ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < (j + 1 )))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_lowcost_2: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH17 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH18 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH19 : (l_lowcost_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH21 : (l_edge_parent_2 = (default_edge_list (n_pre)))) (PreH22 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH23 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_visited: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_lowcost: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  ((( &( "j" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_10_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH18 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH19 : ((state_vertex_count (s_2)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH21 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH22 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH23 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (u: Z)  (v: Z)  (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (minIndex: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (min: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH18 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH19 : ((state_vertex_count (s_2)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 )) (PreH21 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH22 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH23 : (lowcost_sum_matches_state s_2 l_lowcost_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s_2 j 1000000000 minIndex l_lowcost_2 l_edge_parent_2 )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost_2) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
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

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH23 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (row_ptr: Z)  (l_vertex_parent: (@list Z))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent0 ) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost0 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : (min = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) l_lowcost ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (0)))) = 1) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (0)) (replace_Znth (0) (1) (l_visited_2)) ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (0)) ) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (0)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ”
  &&  (IntArray.full row_ptr_2 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : (min = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ”
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : (min = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) l_lowcost ) ”
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot_split_goal_3 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : (min = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ ((state_vertex_count ((initSt (g_low_level_spec) (0)))) = 1) ”
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot_split_goal_4 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : (min = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (0)) (replace_Znth (0) (1) (l_visited_2)) ) ”
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot_split_goal_5 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : (min = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (0)) ) ”
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot_split_goal_6 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : (min = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (0)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ”
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot_split_goal_7 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : (min = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  “ ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ”
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot_split_goal_spatial := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : (min = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited_2 = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth minIndex matrix_low_level_spec __default__List_Z))) (Znth minIndex matrix_low_level_spec __default__List_Z) )
|--
  (IntArray.full row_ptr_2 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
.

Definition prim_adjacency_matrix_return_matrix_entail_wit_11_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (s_2: St) (u_2: Z) (v_2: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH19 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH20 : ((state_vertex_count (s_2)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent )) (PreH22 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent )) (PreH23 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost l_edge_parent 1000000000 )) (PreH24 : (lowcost_sum_matches_state s_2 l_lowcost )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH26 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost l_edge_parent 1000000000 )) (PreH27 : (minIndex <> (-1))) (PreH28 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH29 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent minIndex )) (PreH30 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent minIndex u_2 v_2 )) (PreH31 : (min_vertex_in_range g_low_level_spec s_2 n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (row_ptr: Z)  (l_vertex_parent: (@list Z))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent0 ) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost0 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent: (@list E)) (s_2: St) (u_2: Z) (v_2: Z) (i: Z) (minIndex: Z) (min: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : (minIndex < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH20 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH21 : ((state_vertex_count (s_2)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent )) (PreH23 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent )) (PreH24 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost l_edge_parent 1000000000 )) (PreH25 : (lowcost_sum_matches_state s_2 l_lowcost )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH27 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost l_edge_parent 1000000000 )) (PreH28 : (minIndex <> (-1))) (PreH29 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH30 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent minIndex )) (PreH31 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent minIndex u_2 v_2 )) (PreH32 : (min_vertex_in_range g_low_level_spec s_2 n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent0 ) ”
  &&  (IntArray.full row_ptr_2 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (row_ptr: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH18 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH20 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH21 : ((state_vertex_count (s_2)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH23 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH24 : (lowcost_sum_matches_state s_2 l_lowcost0_2 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH31 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent0_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost0_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH18 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH20 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH21 : ((state_vertex_count (s_2)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH23 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH24 : (lowcost_sum_matches_state s_2 l_lowcost0_2 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH31 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent0_2 )) ,
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost0_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost0_2 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_12_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (s_after_2: St) (row_ptr: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (minIndex = 0)) (PreH17 : (min = 0)) (PreH18 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH19 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH20 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH21 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH22 : ((state_vertex_count (s_after_2)) = 1)) (PreH23 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH25 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH26 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH27 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH28 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH29 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent0_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost0_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH6 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (minIndex = 0)) (PreH17 : (min = 0)) (PreH18 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH19 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH20 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH21 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH22 : ((state_vertex_count (s_after_2)) = 1)) (PreH23 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH25 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH26 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH27 : (l_vertex_parent_2 = (repeat_Z ((-1)) (n_pre)))) (PreH28 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH29 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent0_2 )) ,
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 (repeat_Z ((-1)) (n_pre)) l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_13_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u_2: Z) (v_2: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) <> 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (1 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH22 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH24 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH25 : ((state_vertex_count (s_2)) = i)) (PreH26 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH27 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH28 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH29 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH30 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH31 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH32 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH33 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH35 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH36 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH37 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH39 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH41 : (0 <= j)) (PreH42 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) <> 1000000000) ” 
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent) ((-1))))
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u_2: Z) (v_2: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) <> 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (1 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH22 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH24 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH25 : ((state_vertex_count (s_2)) = i)) (PreH26 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH27 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH28 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH29 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH30 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH31 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH32 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH33 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH35 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH36 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH37 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH39 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH41 : (0 <= j)) (PreH42 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((Znth (j) (l_vertex_parent_2) ((-1))) = (Znth j l_vertex_parent_2 0)) ” 
  &&  “ ((Znth (j) (l_lowcost_2) (0)) = (Znth j l_lowcost_2 0)) ” 
  &&  “ ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = (Znth j (replace_Znth (minIndex) (1) (l_visited_2)) 0)) ” 
  &&  “ ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = (Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0)) ” 
  &&  “ ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((state_vertex_count (s_2)) < (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_13_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) <> 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (i = 0)) (PreH20 : (minIndex = 0)) (PreH21 : (min = 0)) (PreH22 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH23 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH24 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH25 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH26 : ((state_vertex_count (s_after_2)) = 1)) (PreH27 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH28 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH29 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH30 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH31 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH32 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH33 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH36 : (0 <= j)) (PreH37 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
  “ ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) <> 1000000000) ” 
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent) ((-1))))
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) <> 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (i = 0)) (PreH20 : (minIndex = 0)) (PreH21 : (min = 0)) (PreH22 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH23 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH24 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH25 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH26 : ((state_vertex_count (s_after_2)) = 1)) (PreH27 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH28 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH29 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH30 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH31 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH32 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH33 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH36 : (0 <= j)) (PreH37 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E)) ,
  “ ((Znth (j) (l_vertex_parent) ((-1))) = (Znth j l_vertex_parent_2 0)) ” 
  &&  “ ((Znth (j) (l_lowcost) (0)) = (Znth j l_lowcost_2 0)) ” 
  &&  “ ((Znth (j) ((replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre))))) (0)) = (Znth j (replace_Znth (minIndex) (1) (l_visited_2)) 0)) ” 
  &&  “ ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) = (Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0)) ” 
  &&  “ ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0))) ” 
  &&  “ ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) <> 1000000000) ” 
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) )
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_14_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w < (Znth (j) (l_lowcost_2) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (i = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (min = 0)) (PreH21 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH22 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH24 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH25 : ((state_vertex_count (s_after_2)) = 1)) (PreH26 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH27 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH28 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH29 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH30 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH31 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH32 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> minIndex)
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex <= INT_MAX)) (PreH2 : (w <= INT_MAX)) (PreH3 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH5 : (minIndex >= INT_MIN)) (PreH6 : (w >= INT_MIN)) (PreH7 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH8 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH9 : (w < (Znth (j) (l_lowcost_2) (0)))) (PreH10 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH11 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH12 : (w <> 1000000000)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= minIndex)) (PreH18 : (minIndex < n_pre)) (PreH19 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH20 : (src_low_level_spec = 0)) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH24 : (prim_input_weight_bound n_pre 1000000000 )) (PreH25 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH26 : (i = 0)) (PreH27 : (minIndex = 0)) (PreH28 : (min = 0)) (PreH29 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH30 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH31 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH32 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH33 : ((state_vertex_count (s_after_2)) = 1)) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH36 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH37 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH38 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH39 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH40 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> minIndex)
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_14_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w < (Znth (j) (l_lowcost_2) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (1 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH23 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH24 : ((state_vertex_count (s_2)) = i)) (PreH25 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH26 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH29 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH32 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH37 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH38 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> minIndex)
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex <= INT_MAX)) (PreH2 : (w <= INT_MAX)) (PreH3 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH5 : (minIndex >= INT_MIN)) (PreH6 : (w >= INT_MIN)) (PreH7 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH8 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH9 : (w < (Znth (j) (l_lowcost_2) (0)))) (PreH10 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH11 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH12 : (w <> 1000000000)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= minIndex)) (PreH18 : (minIndex < n_pre)) (PreH19 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH20 : (src_low_level_spec = 0)) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH24 : (prim_input_weight_bound n_pre 1000000000 )) (PreH25 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH26 : (1 <= i)) (PreH27 : (i < n_pre)) (PreH28 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH29 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH30 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH32 : ((state_vertex_count (s_2)) = i)) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH34 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH35 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH36 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH37 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH38 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH39 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH40 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH41 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH42 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH43 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH44 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH45 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH46 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH47 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> w)
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> minIndex)
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_14_3_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w >= (Znth (j) (l_lowcost_2) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (i = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (min = 0)) (PreH21 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH22 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH24 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH25 : ((state_vertex_count (s_after_2)) = 1)) (PreH26 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH27 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH28 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH29 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH30 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH31 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH32 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent_2) ((-1))))
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : ((Znth (j) (l_vertex_parent_2) ((-1))) <= INT_MAX)) (PreH2 : ((Znth (j) (l_lowcost_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (l_vertex_parent_2) ((-1))) >= INT_MIN)) (PreH6 : ((Znth (j) (l_lowcost_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH8 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH9 : (w >= (Znth (j) (l_lowcost_2) (0)))) (PreH10 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH11 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH12 : (w <> 1000000000)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= minIndex)) (PreH18 : (minIndex < n_pre)) (PreH19 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH20 : (src_low_level_spec = 0)) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH24 : (prim_input_weight_bound n_pre 1000000000 )) (PreH25 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH26 : (i = 0)) (PreH27 : (minIndex = 0)) (PreH28 : (min = 0)) (PreH29 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH30 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH31 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH32 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH33 : ((state_vertex_count (s_after_2)) = 1)) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH36 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH37 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH38 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH39 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH40 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent_2) ((-1))))
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_14_4_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (w >= (Znth (j) (l_lowcost_2) (0)))) (PreH2 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH3 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH4 : (w <> 1000000000)) (PreH5 : (0 <= j)) (PreH6 : (j < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= minIndex)) (PreH10 : (minIndex < n_pre)) (PreH11 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH12 : (src_low_level_spec = 0)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH16 : (prim_input_weight_bound n_pre 1000000000 )) (PreH17 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH18 : (1 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH23 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH24 : ((state_vertex_count (s_2)) = i)) (PreH25 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH26 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH29 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH32 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH37 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH38 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent_2) ((-1))))
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : ((Znth (j) (l_vertex_parent_2) ((-1))) <= INT_MAX)) (PreH2 : ((Znth (j) (l_lowcost_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (l_vertex_parent_2) ((-1))) >= INT_MIN)) (PreH6 : ((Znth (j) (l_lowcost_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH8 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH9 : (w >= (Znth (j) (l_lowcost_2) (0)))) (PreH10 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) = 0)) (PreH11 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH12 : (w <> 1000000000)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= minIndex)) (PreH18 : (minIndex < n_pre)) (PreH19 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH20 : (src_low_level_spec = 0)) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH24 : (prim_input_weight_bound n_pre 1000000000 )) (PreH25 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH26 : (1 <= i)) (PreH27 : (i < n_pre)) (PreH28 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH29 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH30 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH32 : ((state_vertex_count (s_2)) = i)) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH34 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH35 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH36 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH37 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH38 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH39 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH40 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH41 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH42 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH43 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH44 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH45 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH46 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH47 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent_2) ((-1))))
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_14_5_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <> 0)) (PreH2 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH3 : (w <> 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= minIndex)) (PreH9 : (minIndex < n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (1 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH20 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH21 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH22 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH23 : ((state_vertex_count (s_2)) = i)) (PreH24 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH25 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH26 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH27 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH28 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH29 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH31 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH36 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH37 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH38 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent_2) ((-1))))
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_2: St) (s_after_2: St) (u_2: Z) (v_2: Z) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : ((Znth (j) (l_vertex_parent_2) ((-1))) <= INT_MAX)) (PreH2 : ((Znth (j) (l_lowcost_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (l_vertex_parent_2) ((-1))) >= INT_MIN)) (PreH6 : ((Znth (j) (l_lowcost_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH8 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH9 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <> 0)) (PreH10 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH11 : (w <> 1000000000)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= minIndex)) (PreH17 : (minIndex < n_pre)) (PreH18 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH19 : (src_low_level_spec = 0)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH23 : (prim_input_weight_bound n_pre 1000000000 )) (PreH24 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH25 : (1 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH28 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH29 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH30 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH31 : ((state_vertex_count (s_2)) = i)) (PreH32 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH33 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH34 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH35 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH36 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH37 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH38 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH39 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH40 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH43 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH44 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH45 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH46 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent_2) ((-1))))
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_14_6_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <> 0)) (PreH2 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH3 : (w <> 1000000000)) (PreH4 : (0 <= j)) (PreH5 : (j < n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= minIndex)) (PreH9 : (minIndex < n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (i = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (min = 0)) (PreH20 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH23 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH24 : ((state_vertex_count (s_after_2)) = 1)) (PreH25 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH27 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH28 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH29 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH30 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH31 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH32 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH33 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent_2) ((-1))))
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex selected_row matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> selected_row)
  **  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0_2: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (w: Z) (minIndex: Z) (j: Z) (i: Z) (min: Z) (selected_row: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : ((Znth (j) (l_vertex_parent_2) ((-1))) <= INT_MAX)) (PreH2 : ((Znth (j) (l_lowcost_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (l_vertex_parent_2) ((-1))) >= INT_MIN)) (PreH6 : ((Znth (j) (l_lowcost_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) >= INT_MIN)) (PreH8 : ((Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)) >= INT_MIN)) (PreH9 : ((Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)) <> 0)) (PreH10 : (w = (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))) (PreH11 : (w <> 1000000000)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= minIndex)) (PreH17 : (minIndex < n_pre)) (PreH18 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH19 : (src_low_level_spec = 0)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH23 : (prim_input_weight_bound n_pre 1000000000 )) (PreH24 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH25 : (i = 0)) (PreH26 : (minIndex = 0)) (PreH27 : (min = 0)) (PreH28 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH29 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH32 : ((state_vertex_count (s_after_2)) = 1)) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH35 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH36 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH37 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH38 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH39 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH40 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (IntArray.missing_i selected_row j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (((selected_row + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))) (0)))
  **  (IntArray.missing_i visited j 0 n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((replace_Znth (minIndex) (1) (l_visited_2))) (0)))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost_2 )
  **  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_lowcost_2) (0)))
  **  (IntArray.missing_i vertex_parent j 0 n_pre l_vertex_parent_2 )
  **  (((vertex_parent + (j * sizeof(INT)))) # Int  |-> (Znth (j) (l_vertex_parent_2) ((-1))))
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (src_low_level_spec)) l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntArray.full selected_row (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) ((repeat_Z (0) (n_pre)))) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_14_7_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u_2: Z) (v_2: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (1 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH22 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH24 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH25 : ((state_vertex_count (s_2)) = i)) (PreH26 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH27 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH28 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH29 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH30 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH31 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH32 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH33 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH35 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH36 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH37 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH39 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH41 : (0 <= j)) (PreH42 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u_2: Z) (v_2: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s_2: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (1 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH22 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH24 : (visited_matches_state g_low_level_spec s_2 l_visited_2 )) (PreH25 : ((state_vertex_count (s_2)) = i)) (PreH26 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent0_2 )) (PreH27 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH28 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s_2 l_edge_parent0_2 minIndex )) (PreH29 : (selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2 minIndex u_2 v_2 )) (PreH30 : (selected_parent_add_to_mst g_low_level_spec s_2 s_after_2 l_edge_parent0_2 minIndex )) (PreH31 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH32 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH33 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH34 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH35 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH36 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH37 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH39 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH40 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH41 : (0 <= j)) (PreH42 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (u: Z)  (v: Z)  (l_edge_parent0: (@list E))  (l_visited: (@list Z))  (s: St)  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ ((replace_Znth (minIndex) (1) (l_visited_2)) = (replace_Znth (minIndex) (1) (l_visited))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ” 
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
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex (j + 1 ) l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_14_8_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (i = 0)) (PreH20 : (minIndex = 0)) (PreH21 : (min = 0)) (PreH22 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH23 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH24 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH25 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH26 : ((state_vertex_count (s_after_2)) = 1)) (PreH27 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH28 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH29 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH30 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH31 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH32 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH33 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH36 : (0 <= j)) (PreH37 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_vertex_parent: (@list Z))  (l_lowcost: (@list Z))  (l_edge_parent: (@list E))  (l_edge_parent0: (@list E))  (l_lowcost0: (@list Z))  (l_visited: (@list Z))  (s_after: St) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : ((Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0) = 1000000000)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= minIndex)) (PreH8 : (minIndex < n_pre)) (PreH9 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH10 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH11 : (src_low_level_spec = 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH15 : (prim_input_weight_bound n_pre 1000000000 )) (PreH16 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH17 : (INT_MIN <= min)) (PreH18 : (min <= INT_MAX)) (PreH19 : (i = 0)) (PreH20 : (minIndex = 0)) (PreH21 : (min = 0)) (PreH22 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH23 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH24 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH25 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH26 : ((state_vertex_count (s_after_2)) = 1)) (PreH27 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH28 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH29 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH30 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH31 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH32 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH33 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH36 : (0 <= j)) (PreH37 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E)) ,
  “ ((replace_Znth (0) (1) ((repeat_Z (0) (n_pre)))) = (replace_Znth (0) (1) ((repeat_Z (0) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))))))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))) ” 
  &&  “ (safeExec (prim_state_is ((initSt (g_low_level_spec) (0)))) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec (initSt (g_low_level_spec) (0)) ) ” 
  &&  “ (visited_matches_state g_low_level_spec (initSt (g_low_level_spec) (0)) (replace_Znth (0) (1) ((repeat_Z (0) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) ) ” 
  &&  “ ((state_vertex_count ((initSt (g_low_level_spec) (0)))) = 1) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) (replace_Znth (0) (0) ((repeat_Z (1000000000) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) ) ” 
  &&  “ (lowcost_values_in_range 1000000000 (replace_Znth (0) (0) ((repeat_Z (1000000000) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) ) ” 
  &&  “ (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 (initSt (g_low_level_spec) (0)) 0 (j + 1 ) (replace_Znth (0) (0) ((repeat_Z (1000000000) ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))))) (default_edge_list ((Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z))))))) l_lowcost_2 l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state (initSt (g_low_level_spec) (0)) l_lowcost_2 ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Zlength ((Znth (0) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_15_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u: Z) (v: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (INT_MIN <= min)) (PreH17 : (min <= INT_MAX)) (PreH18 : (1 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s )) (PreH23 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH24 : ((state_vertex_count (s)) = i)) (PreH25 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0_2 )) (PreH26 : (lowcost_parent_match g_low_level_spec s l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0_2 minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent0_2 minIndex u v )) (PreH29 : (selected_parent_add_to_mst g_low_level_spec s s_after_2 l_edge_parent0_2 minIndex )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH32 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH37 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH38 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH40 : (0 <= j)) (PreH41 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_edge_parent0: (@list E))  (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "j" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (row_ptr: Z) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (u: Z) (v: Z) (l_edge_parent0_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (s_after_2: St) (l_lowcost0_2: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (INT_MIN <= min)) (PreH17 : (min <= INT_MAX)) (PreH18 : (1 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (min = (Znth (minIndex) (l_lowcost0_2) (0)))) (PreH21 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s )) (PreH23 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH24 : ((state_vertex_count (s)) = i)) (PreH25 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0_2 )) (PreH26 : (lowcost_parent_match g_low_level_spec s l_lowcost0_2 l_edge_parent0_2 1000000000 )) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0_2 minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent0_2 minIndex u v )) (PreH29 : (selected_parent_add_to_mst g_low_level_spec s s_after_2 l_edge_parent0_2 minIndex )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH31 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH32 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent0_2 )) (PreH34 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH37 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH38 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH40 : (0 <= j)) (PreH41 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_2 ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_15_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (INT_MIN <= min)) (PreH17 : (min <= INT_MAX)) (PreH18 : (i = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (min = 0)) (PreH21 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH22 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH24 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH25 : ((state_vertex_count (s_after_2)) = 1)) (PreH26 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH27 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH28 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH29 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH30 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH31 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH32 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH35 : (0 <= j)) (PreH36 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_edge_parent0: (@list E))  (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St)  (l_lowcost0: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "j" ) )) # Int  |-> n_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (row_ptr: Z) (l_vertex_parent_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_edge_parent0_2: (@list E)) (l_lowcost0_2: (@list Z)) (l_visited_2: (@list Z)) (s_after_2: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (INT_MIN <= min)) (PreH17 : (min <= INT_MAX)) (PreH18 : (i = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (min = 0)) (PreH21 : (s_after_2 = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH22 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH24 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH25 : ((state_vertex_count (s_after_2)) = 1)) (PreH26 : (lowcost_sum_matches_state s_after_2 l_lowcost0_2 )) (PreH27 : (lowcost_values_in_range 1000000000 l_lowcost0_2 )) (PreH28 : (l_lowcost0_2 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH29 : (l_edge_parent0_2 = (default_edge_list (n_pre)))) (PreH30 : (l_visited_2 = (repeat_Z (0) (n_pre)))) (PreH31 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex j l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 )) (PreH32 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH33 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH35 : (0 <= j)) (PreH36 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_2 ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_16_1_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i = 0) -> (min = 0))) (PreH14 : (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0))))) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH18 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH19 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH21 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH22 : (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent_2 )) (PreH23 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH24 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH26 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i = 0) -> (min = 0))) (PreH14 : (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0))))) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH18 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH19 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH21 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH22 : (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent_2 )) (PreH23 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH24 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH26 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s_after: St) ,
  “ (i < n_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited_2)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_16_2_boot := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (i = 0)) (PreH12 : (minIndex = 0)) (PreH13 : ((i = 0) -> (min = 0))) (PreH14 : (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0))))) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH18 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH19 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH21 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH22 : (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent_2 )) (PreH23 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH24 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH26 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited_2)) )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost0: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent0: (@list E)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (i = 0)) (PreH12 : (minIndex = 0)) (PreH13 : ((i = 0) -> (min = 0))) (PreH14 : (((1 <= i) /\ (i < n_pre)) -> (min = (Znth (minIndex) (l_lowcost0) (0))))) (PreH15 : (INT_MIN <= min)) (PreH16 : (min <= INT_MAX)) (PreH17 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH18 : (visited_matches_state g_low_level_spec s_after_2 (replace_Znth (minIndex) (1) (l_visited_2)) )) (PreH19 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH21 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH22 : (scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec 1000000000 s_after_2 minIndex l_lowcost0 l_edge_parent0 l_lowcost_2 l_edge_parent_2 )) (PreH23 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH24 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH26 : (safeExec (prim_state_is (s_after_2)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s_after: St) ,
  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after (replace_Znth (0) (1) (l_visited_2)) ) ” 
  &&  “ ((state_vertex_count (s_after)) = (0 + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost_2 ) ” 
  &&  “ (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_17_1_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i_2: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_3: (@list Z)) (l_vertex_parent_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH11 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH12 : ((state_vertex_count (s_2)) = i)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent_3 )) (PreH15 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH16 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH18 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i_2)) (PreH21 : (i_2 < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (1 <= i_2)) (PreH25 : (i_2 < n_pre)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH36 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_3 )
|--
  EX (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i_2: Z) (minIndex: Z) (min: Z) (l_lowcost_3: (@list Z)) (l_vertex_parent_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH11 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH12 : ((state_vertex_count (s_2)) = i)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent_3 )) (PreH15 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH16 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH18 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i_2)) (PreH21 : (i_2 < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (1 <= i_2)) (PreH25 : (i_2 < n_pre)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH36 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= (state_vertex_count (s_2))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec 0 ) ” 
  &&  “ (INT_MIN <= 1000000000) ” 
  &&  “ (1000000000 <= INT_MAX) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((state_vertex_count (s_2)) - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_3 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_3 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_3 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s 0 1000000000 (-1) l_lowcost_3 l_edge_parent ) ” 
  &&  “ (((-1) = (-1)) -> (1000000000 = 1000000000)) ” 
  &&  “ (((-1) <> (-1)) -> (1000000000 = (Znth ((-1)) (l_lowcost_3) (0)))) ” 
  &&  “ (((-1) <> (-1)) -> ((0 <= (-1)) /\ ((-1) < 0))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_17_2_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i_2: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_3: (@list Z)) (l_vertex_parent_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH11 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH12 : ((state_vertex_count (s_2)) = i)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent_3 )) (PreH15 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH16 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH18 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i_2)) (PreH21 : (i_2 < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (i_2 = 0)) (PreH25 : (minIndex = 0)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH36 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_3 )
|--
  EX (l_lowcost: (@list Z))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (l_visited: (@list Z))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after: St) (i_2: Z) (minIndex: Z) (min: Z) (l_lowcost_3: (@list Z)) (l_vertex_parent_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s_2: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_2 )) (PreH11 : (visited_matches_state g_low_level_spec s_2 l_visited_3 )) (PreH12 : ((state_vertex_count (s_2)) = i)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent_3 )) (PreH15 : (lowcost_parent_match g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH16 : (lowcost_sum_matches_state s_2 l_lowcost_3 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH18 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i_2)) (PreH21 : (i_2 < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (i_2 = 0)) (PreH25 : (minIndex = 0)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited_2 )) (PreH36 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent_2 )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost_2 )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (s: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= (state_vertex_count (s_2))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec 0 ) ” 
  &&  “ (INT_MIN <= 1000000000) ” 
  &&  “ (1000000000 <= INT_MAX) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((state_vertex_count (s_2)) - 1 ))) X_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_3 ) ” 
  &&  “ ((state_vertex_count (s)) = (state_vertex_count (s_2))) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_3 l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_3 ) ” 
  &&  “ (((state_vertex_count (s_2)) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_3 l_edge_parent 1000000000 )) ” 
  &&  “ (min_vertex_in_range g_low_level_spec s 0 1000000000 (-1) l_lowcost_3 l_edge_parent ) ” 
  &&  “ (((-1) = (-1)) -> (1000000000 = 1000000000)) ” 
  &&  “ (((-1) <> (-1)) -> (1000000000 = (Znth ((-1)) (l_lowcost_3) (0)))) ” 
  &&  “ (((-1) <> (-1)) -> ((0 <= (-1)) /\ ((-1) < 0))) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_18_1_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (growing_subgraph_state g_low_level_spec s_after )) (PreH16 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH17 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH18 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH19 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH20 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH21 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  EX (l_lowcost_2: (@list Z))  (l_vertex_parent_2: (@list Z))  (l_edge_parent_2: (@list E))  (l_visited_2: (@list Z))  (s: St) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 ) ” 
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= minIndex)) (PreH4 : (minIndex < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (growing_subgraph_state g_low_level_spec s_after )) (PreH16 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH17 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH18 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH19 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH20 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH21 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent_2: (@list E))  (s: St) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited ) ” 
  &&  “ ((state_vertex_count (s)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s l_edge_parent_2 ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent l_edge_parent_2 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent_2 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost ) ” 
  &&  “ (((i + 1 ) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent_2 1000000000 )) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) (((i + 1 ) - 1 ))) X_low_level_spec ) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i < n_pre) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_18_2_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i_2: Z) (minIndex_2: Z) (min_2: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (0 <= i_2)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= minIndex_2)) (PreH4 : (minIndex_2 < n_pre)) (PreH5 : (i_2 = 0)) (PreH6 : (minIndex_2 = 0)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min_2)) (PreH14 : (min_2 <= INT_MAX)) (PreH15 : (growing_subgraph_state g_low_level_spec s_after )) (PreH16 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH17 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH18 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH19 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH20 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH21 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i_2)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  EX (l_lowcost_3: (@list Z))  (l_vertex_parent_3: (@list Z))  (l_edge_parent_3: (@list E))  (l_visited_3: (@list Z))  (s_2: St) ,
  “ (1 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_2 ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_2 l_visited_3 ) ” 
  &&  “ ((state_vertex_count (s_2)) = (i_2 + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_2 l_edge_parent_3 ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent_3 ) ” 
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min_2) ” 
  &&  “ (min_2 <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i_2 + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_3 )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i_2: Z) (minIndex_2: Z) (min_2: Z) (PreH1 : (0 <= i_2)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= minIndex_2)) (PreH4 : (minIndex_2 < n_pre)) (PreH5 : (i_2 = 0)) (PreH6 : (minIndex_2 = 0)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min_2)) (PreH14 : (min_2 <= INT_MAX)) (PreH15 : (growing_subgraph_state g_low_level_spec s_after )) (PreH16 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH17 : ((state_vertex_count (s_after)) = (i_2 + 1 ))) (PreH18 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH19 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH20 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH21 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i_2)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent_3: (@list E))  (s_2: St) ,
  “ (1 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_2 ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_2 l_visited ) ” 
  &&  “ ((state_vertex_count (s_2)) = (0 + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_2 l_edge_parent_3 ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent l_edge_parent_3 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_2 l_lowcost l_edge_parent_3 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_2 l_lowcost ) ” 
  &&  “ (((0 + 1 ) < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s_2 l_lowcost l_edge_parent_3 1000000000 )) ” 
  &&  “ (safeExec (prim_state_is (s_2)) (Prim2_loop (g_low_level_spec) (((0 + 1 ) - 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_19_1_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_3: (@list Z)) (l_vertex_parent_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s: St) (i_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (growing_subgraph_state g_low_level_spec s )) (PreH12 : (visited_matches_state g_low_level_spec s l_visited_3 )) (PreH13 : ((state_vertex_count (s)) = i_2)) (PreH14 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_3 )) (PreH15 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent_3 )) (PreH16 : (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH17 : (lowcost_sum_matches_state s l_lowcost_3 )) (PreH18 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH19 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH20 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= minIndex)) (PreH24 : (minIndex < n_pre)) (PreH25 : (1 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (src_low_level_spec = 0)) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre < INT_MAX)) (PreH30 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH31 : (prim_input_weight_bound n_pre 1000000000 )) (PreH32 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH33 : (INT_MIN <= min)) (PreH34 : (min <= INT_MAX)) (PreH35 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH36 : (visited_matches_state g_low_level_spec s_after_2 l_visited_2 )) (PreH37 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH38 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH39 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH40 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (PtrArray.undef_full retval n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_3 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (result_matrix: (@list (@list Z)))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix = (inf_matrix (0) (n_pre) (1000000000))) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (PtrArray.undef_seg retval 0 n_pre )
  **  (IntPtrArray2.full retval 0 result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (l_lowcost_3: (@list Z)) (l_vertex_parent_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s: St) (i_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (growing_subgraph_state g_low_level_spec s )) (PreH12 : (visited_matches_state g_low_level_spec s l_visited_3 )) (PreH13 : ((state_vertex_count (s)) = i_2)) (PreH14 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_3 )) (PreH15 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent_3 )) (PreH16 : (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH17 : (lowcost_sum_matches_state s l_lowcost_3 )) (PreH18 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH19 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH20 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= minIndex)) (PreH24 : (minIndex < n_pre)) (PreH25 : (1 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (src_low_level_spec = 0)) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre < INT_MAX)) (PreH30 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH31 : (prim_input_weight_bound n_pre 1000000000 )) (PreH32 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH33 : (INT_MIN <= min)) (PreH34 : (min <= INT_MAX)) (PreH35 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH36 : (visited_matches_state g_low_level_spec s_after_2 l_visited_2 )) (PreH37 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH38 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH39 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH40 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  EX (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntPtrArray2.full retval 0 (inf_matrix (0) (n_pre) (1000000000)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_19_2_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_3: (@list Z)) (l_vertex_parent_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s: St) (i_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (growing_subgraph_state g_low_level_spec s )) (PreH12 : (visited_matches_state g_low_level_spec s l_visited_3 )) (PreH13 : ((state_vertex_count (s)) = i_2)) (PreH14 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_3 )) (PreH15 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent_3 )) (PreH16 : (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH17 : (lowcost_sum_matches_state s l_lowcost_3 )) (PreH18 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH19 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH20 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= minIndex)) (PreH24 : (minIndex < n_pre)) (PreH25 : (i = 0)) (PreH26 : (minIndex = 0)) (PreH27 : (src_low_level_spec = 0)) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre < INT_MAX)) (PreH30 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH31 : (prim_input_weight_bound n_pre 1000000000 )) (PreH32 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH33 : (INT_MIN <= min)) (PreH34 : (min <= INT_MAX)) (PreH35 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH36 : (visited_matches_state g_low_level_spec s_after_2 l_visited_2 )) (PreH37 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH38 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH39 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH40 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (PtrArray.undef_full retval n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_3 )
  **  (IntArray.full lowcost n_pre l_lowcost_3 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_3 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (result_matrix: (@list (@list Z)))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix = (inf_matrix (0) (n_pre) (1000000000))) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (PtrArray.undef_seg retval 0 n_pre )
  **  (IntPtrArray2.full retval 0 result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (i: Z) (minIndex: Z) (min: Z) (l_lowcost_3: (@list Z)) (l_vertex_parent_3: (@list Z)) (l_edge_parent_3: (@list E)) (l_visited_3: (@list Z)) (s: St) (i_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i_2 >= n_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (growing_subgraph_state g_low_level_spec s )) (PreH12 : (visited_matches_state g_low_level_spec s l_visited_3 )) (PreH13 : ((state_vertex_count (s)) = i_2)) (PreH14 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_3 )) (PreH15 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent_3 )) (PreH16 : (lowcost_parent_match g_low_level_spec s l_lowcost_3 l_edge_parent_3 1000000000 )) (PreH17 : (lowcost_sum_matches_state s l_lowcost_3 )) (PreH18 : (lowcost_values_in_range 1000000000 l_lowcost_3 )) (PreH19 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_3 l_edge_parent_3 1000000000 ))) (PreH20 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= minIndex)) (PreH24 : (minIndex < n_pre)) (PreH25 : (i = 0)) (PreH26 : (minIndex = 0)) (PreH27 : (src_low_level_spec = 0)) (PreH28 : (2 <= n_pre)) (PreH29 : (n_pre < INT_MAX)) (PreH30 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH31 : (prim_input_weight_bound n_pre 1000000000 )) (PreH32 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH33 : (INT_MIN <= min)) (PreH34 : (min <= INT_MAX)) (PreH35 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH36 : (visited_matches_state g_low_level_spec s_after_2 l_visited_2 )) (PreH37 : ((state_vertex_count (s_after_2)) = (i + 1 ))) (PreH38 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH39 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH40 : (lowcost_parent_match g_low_level_spec s_after_2 l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH41 : (lowcost_sum_matches_state s_after_2 l_lowcost_2 )) (PreH42 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  EX (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_3 l_edge_parent ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntPtrArray2.full retval 0 (inf_matrix (0) (n_pre) (1000000000)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_20_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost_2: (@list Z)) (visited: Z) (l_visited_2: (@list Z)) (mst: Z) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (retval: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH11 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH12 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (result_matrix_2 = (inf_matrix (i) (n_pre) (1000000000)))) (PreH16 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (((mst + (i * sizeof(PTR)))) # Ptr  |-> retval)
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (IntArray.undef_full retval n_pre )
  **  (IntPtrArray2.full mst i result_matrix_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (row_ptr: Z)  (row_prefix: (@list Z))  (result_matrix: (@list (@list Z)))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix = (inf_matrix (i) (n_pre) (1000000000))) ” 
  &&  “ (row_prefix = (repeat_Z (1000000000) (0))) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntPtrArray2.full mst i result_matrix )
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.seg row_ptr 0 0 row_prefix )
  **  (IntArray.undef_seg row_ptr 0 n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH11 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH12 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (result_matrix_2 = (inf_matrix (i) (n_pre) (1000000000)))) (PreH16 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (state_vertex_count (s_after_2))) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = (state_vertex_count (s_after_2))) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ ((@nil Z) = (repeat_Z (1000000000) (0))) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_21_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost_2: (@list Z)) (visited: Z) (l_visited_2: (@list Z)) (row_ptr_2: Z) (mst: Z) (row_prefix_2: (@list Z)) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH13 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH14 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH17 : (result_matrix_2 = (inf_matrix (i) (n_pre) (1000000000)))) (PreH18 : (row_prefix_2 = (repeat_Z (1000000000) (j)))) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.seg row_ptr_2 0 (j + 1 ) (app (row_prefix_2) ((cons (1000000000) ((@nil Z))))) )
  **  (IntArray.undef_seg row_ptr_2 (j + 1 ) n_pre )
  **  (IntPtrArray2.full mst i result_matrix_2 )
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (row_ptr: Z)  (row_prefix: (@list Z))  (result_matrix: (@list (@list Z)))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix = (inf_matrix (i) (n_pre) (1000000000))) ” 
  &&  “ (row_prefix = (repeat_Z (1000000000) ((j + 1 )))) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntPtrArray2.full mst i result_matrix )
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.seg row_ptr 0 (j + 1 ) row_prefix )
  **  (IntArray.undef_seg row_ptr (j + 1 ) n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (row_prefix_2: (@list Z)) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH13 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH14 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH17 : (result_matrix_2 = (inf_matrix (i) (n_pre) (1000000000)))) (PreH18 : (row_prefix_2 = (repeat_Z (1000000000) (j)))) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ ((app ((repeat_Z (1000000000) (j))) ((cons (1000000000) ((@nil Z))))) = (repeat_Z (1000000000) ((j + 1 )))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (state_vertex_count (s_after_2))) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = (state_vertex_count (s_after_2))) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_22_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost_2: (@list Z)) (visited: Z) (l_visited_2: (@list Z)) (row_ptr: Z) (mst: Z) (row_prefix: (@list Z)) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH13 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH14 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH17 : (result_matrix_2 = (inf_matrix (i) (n_pre) (1000000000)))) (PreH18 : (row_prefix = (repeat_Z (1000000000) (j)))) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntPtrArray2.full mst i result_matrix_2 )
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.seg row_ptr 0 j row_prefix )
  **  (IntArray.undef_seg row_ptr j n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (result_matrix: (@list (@list Z)))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix = (inf_matrix ((i + 1 )) (n_pre) (1000000000))) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (IntPtrArray2.full mst (i + 1 ) result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (row_ptr: Z) (mst: Z) (row_prefix: (@list Z)) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH13 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH14 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH17 : (result_matrix_2 = (inf_matrix (i) (n_pre) (1000000000)))) (PreH18 : (row_prefix = (repeat_Z (1000000000) (j)))) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntPtrArray2.full mst i result_matrix_2 )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.seg row_ptr 0 j row_prefix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  EX (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntPtrArray2.full mst (i + 1 ) (inf_matrix ((i + 1 )) (n_pre) (1000000000)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_23_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost_2: (@list Z)) (visited: Z) (l_visited_2: (@list Z)) (mst: Z) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH11 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH12 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (result_matrix_2 = (inf_matrix (i) (n_pre) (1000000000)))) (PreH16 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (PtrArray.undef_seg mst i n_pre )
  **  (IntPtrArray2.full mst i result_matrix_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (result_matrix: (@list (@list Z)))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 0 ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (mst: Z) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH11 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH12 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (result_matrix_2 = (inf_matrix (i) (n_pre) (1000000000)))) (PreH16 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntPtrArray2.full mst i result_matrix_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  EX (result_matrix: (@list (@list Z)))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent_2 l_edge_parent 1000000000 0 ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_24_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost_2: (@list Z)) (visited: Z) (l_visited_2: (@list Z)) (mst: Z) (result_matrix_2: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z)  __default__List_Z (PreH1 : ((Znth i l_vertex_parent 0) < n_pre)) (PreH2 : (0 <= (Znth i l_vertex_parent 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH13 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH14 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent_2 )) (PreH17 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent l_edge_parent_2 1000000000 i )) (PreH18 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full vertex_parent n_pre l_vertex_parent )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (row_ptr: Z)  (result_matrix: (@list (@list Z)))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St)  (l_vertex_parent_2: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (Znth i l_vertex_parent 0)) ” 
  &&  “ ((Znth i l_vertex_parent 0) < n_pre) ” 
  &&  “ ((Znth i l_vertex_parent 0) = (Znth i l_vertex_parent_2 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent_2 l_edge_parent 1000000000 i ) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntPtrArray2.missing_i graph_pre n_pre (Znth i l_vertex_parent 0) row_ptr matrix_low_level_spec )
  **  (((graph_pre + ((Znth i l_vertex_parent 0) * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr n_pre (Znth (Znth i l_vertex_parent 0) matrix_low_level_spec __default__List_Z) )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH2 : ((Znth i l_vertex_parent 0) < n_pre)) (PreH3 : (0 <= (Znth i l_vertex_parent 0))) (PreH4 : (i < n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH14 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH15 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent_2 )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent l_edge_parent_2 1000000000 i )) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth (Znth i l_vertex_parent 0) matrix_low_level_spec __default__List_Z))) (Znth (Znth i l_vertex_parent 0) matrix_low_level_spec __default__List_Z) )
|--
  EX (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (Znth i l_vertex_parent 0)) ” 
  &&  “ ((Znth i l_vertex_parent 0) < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full row_ptr_2 n_pre (Znth (Znth i l_vertex_parent 0) matrix_low_level_spec __default__List_Z) )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_25_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (rg_2: G) (row_ptr: Z) (i: Z) (p: Z) (mst: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (p = (Znth i l_vertex_parent_2 0))) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH13 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH14 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH17 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH18 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full row_ptr n_pre (Znth p matrix_low_level_spec __default__List_Z) )
  **  (IntPtrArray2.missing_i graph_pre n_pre p row_ptr matrix_low_level_spec )
  **  (((graph_pre + (p * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.full mst n_pre result_matrix_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (mst_row: Z)  (result_matrix: (@list (@list Z)))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St)  (l_vertex_parent: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ ((Znth i (Znth p matrix_low_level_spec __default__List_Z) 0) = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0)) ” 
  &&  “ (p = (Znth i l_vertex_parent 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre p mst_row result_matrix )
  **  (((mst + (p * sizeof(PTR)))) # Ptr  |-> mst_row)
  **  (IntArray.full mst_row n_pre (Znth p result_matrix __default__List_Z) )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (rg_2: G) (row_ptr: Z) (i: Z) (p: Z) (mst: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (p = (Znth i l_vertex_parent_2 0))) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH13 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH14 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH17 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH18 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth p result_matrix_2 __default__List_Z))) (Znth p result_matrix_2 __default__List_Z) )
  **  (IntPtrArray2.missing_i mst n_pre p row_ptr_2 result_matrix_2 )
  **  (IntArray.full row_ptr n_pre (Znth p matrix_low_level_spec __default__List_Z) )
  **  (IntPtrArray2.missing_i graph_pre n_pre p row_ptr matrix_low_level_spec )
  **  (((graph_pre + (p * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  EX (result_matrix: (@list (@list Z)))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (p = (Znth i l_vertex_parent_2 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent_2 l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre p row_ptr_2 result_matrix )
  **  (IntArray.full row_ptr_2 n_pre (Znth p result_matrix __default__List_Z) )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_26_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (rg_2: G) (mst_row_2: Z) (i: Z) (p: Z) (w: Z) (mst: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))) (PreH6 : (p = (Znth i l_vertex_parent_2 0))) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH14 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH15 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full mst_row_2 n_pre (replace_Znth (i) (w) ((Znth p result_matrix_2 __default__List_Z))) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre p mst_row_2 result_matrix_2 )
  **  (((mst + (p * sizeof(PTR)))) # Ptr  |-> mst_row_2)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (mst_row: Z)  (result_matrix: (@list (@list Z)))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St)  (l_vertex_parent: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0)) ” 
  &&  “ (p = (Znth i l_vertex_parent 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre i mst_row (set_matrix_entry (result_matrix) (p) (i) (w)) )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> mst_row)
  **  (IntArray.full mst_row n_pre (Znth i (set_matrix_entry (result_matrix) (p) (i) (w)) __default__List_Z) )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (rg_2: G) (mst_row_2: Z) (i: Z) (p: Z) (w: Z) (mst: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))) (PreH6 : (p = (Znth i l_vertex_parent_2 0))) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH14 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH15 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full mst_row_2 n_pre (replace_Znth (i) (w) ((Znth p result_matrix_2 __default__List_Z))) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre p mst_row_2 result_matrix_2 )
  **  (((mst + (p * sizeof(PTR)))) # Ptr  |-> mst_row_2)
|--
  EX (mst_row: Z)  (result_matrix: (@list (@list Z)))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0)) ” 
  &&  “ (p = (Znth i l_vertex_parent_2 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent_2 l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre i mst_row (set_matrix_entry (result_matrix) (p) (i) (w)) )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> mst_row)
  **  (IntArray.full mst_row n_pre (Znth i (set_matrix_entry (result_matrix) (p) (i) (w)) __default__List_Z) )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_27_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (rg_2: G) (mst_row: Z) (i: Z) (p: Z) (w: Z) (mst: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))) (PreH6 : (p = (Znth i l_vertex_parent_2 0))) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH14 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH15 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full mst_row n_pre (replace_Znth (p) (w) ((Znth i (set_matrix_entry (result_matrix_2) (p) (i) (w)) __default__List_Z))) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre i mst_row (set_matrix_entry (result_matrix_2) (p) (i) (w)) )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> mst_row)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (result_matrix: (@list (@list Z)))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St)  (l_vertex_parent: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0)) ” 
  &&  “ (p = (Znth i l_vertex_parent 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec (set_undirected_matrix_entry (result_matrix) (p) (i) (w)) l_vertex_parent l_edge_parent 1000000000 (i + 1 ) ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre (set_undirected_matrix_entry (result_matrix) (p) (i) (w)) )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (rg_2: G) (mst_row: Z) (i: Z) (p: Z) (w: Z) (mst: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))) (PreH6 : (p = (Znth i l_vertex_parent_2 0))) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH14 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH15 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full mst_row n_pre (replace_Znth (p) (w) ((Znth i (set_matrix_entry (result_matrix_2) (p) (i) (w)) __default__List_Z))) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre i mst_row (set_matrix_entry (result_matrix_2) (p) (i) (w)) )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> mst_row)
|--
  EX (result_matrix: (@list (@list Z)))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0)) ” 
  &&  “ (p = (Znth i l_vertex_parent_2 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec (set_undirected_matrix_entry (result_matrix) (p) (i) (w)) l_vertex_parent_2 l_edge_parent 1000000000 (i + 1 ) ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre (set_undirected_matrix_entry (result_matrix) (p) (i) (w)) )
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_28_1_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_visited_2: (@list Z)) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (rg_2: G) (i: Z) (p: Z) (w: Z) (mst: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))) (PreH6 : (p = (Znth i l_vertex_parent_2 0))) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH14 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH15 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec (set_undirected_matrix_entry (result_matrix_2) (p) (i) (w)) l_vertex_parent_2 l_edge_parent_2 1000000000 (i + 1 ) )) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre (set_undirected_matrix_entry (result_matrix_2) (p) (i) (w)) )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (result_matrix: (@list (@list Z)))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 (i + 1 ) ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (s_after_2: St) (rg_2: G) (i: Z) (p: Z) (w: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))) (PreH6 : (p = (Znth i l_vertex_parent_2 0))) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH14 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH15 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec (set_undirected_matrix_entry (result_matrix_2) (p) (i) (w)) l_vertex_parent_2 l_edge_parent_2 1000000000 (i + 1 ) )) (PreH19 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (state_vertex_count (s_after_2))) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = (state_vertex_count (s_after_2))) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec 0 matrix_low_level_spec (set_undirected_matrix_entry (result_matrix_2) ((Znth i l_vertex_parent_2 0)) (i) ((Znth i (Znth (Znth i l_vertex_parent_2 0) matrix_low_level_spec __default__List_Z) 0))) l_vertex_parent_2 l_edge_parent 1000000000 (i + 1 ) ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_28_2_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost_2: (@list Z)) (visited: Z) (l_visited_2: (@list Z)) (mst: Z) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (PreH1 : (0 > (Znth i l_vertex_parent_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH12 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH13 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH14 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH15 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH16 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH17 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (result_matrix: (@list (@list Z)))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 (i + 1 ) ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (PreH1 : (0 > (Znth i l_vertex_parent_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (src_low_level_spec = 0)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH9 : (prim_input_weight_bound n_pre 1000000000 )) (PreH10 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH11 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH12 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH13 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH14 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH15 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH16 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH17 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (state_vertex_count (s_after_2))) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = (state_vertex_count (s_after_2))) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec 0 matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent 1000000000 (i + 1 ) ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_entail_wit_28_3_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost_2: (@list Z)) (visited: Z) (l_visited_2: (@list Z)) (mst: Z) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (PreH1 : ((Znth i l_vertex_parent_2 0) >= n_pre)) (PreH2 : (0 <= (Znth i l_vertex_parent_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH13 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH14 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH17 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH18 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix_2 )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
|--
  EX (l_lowcost: (@list Z))  (l_visited: (@list Z))  (result_matrix: (@list (@list Z)))  (l_vertex_parent: (@list Z))  (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 (i + 1 ) ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (rg_2: G) (s_after_2: St) (i: Z) (PreH1 : ((Znth i l_vertex_parent_2 0) >= n_pre)) (PreH2 : (0 <= (Znth i l_vertex_parent_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after_2 )) (PreH13 : ((state_vertex_count (s_after_2)) = n_pre)) (PreH14 : (prim_state_graph_matches rg_2 s_after_2 )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after_2 l_edge_parent_2 )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH17 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent_2 1000000000 i )) (PreH18 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (l_edge_parent: (@list E))  (rg: G)  (s_after: St) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (state_vertex_count (s_after_2))) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = (state_vertex_count (s_after_2))) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec 0 s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec 0 l_vertex_parent_2 l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec 0 matrix_low_level_spec result_matrix_2 l_vertex_parent_2 l_edge_parent 1000000000 (i + 1 ) ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_return_wit_1_running := 
(
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (mst: Z) (result_matrix_2: (@list (@list Z))) (l_edge_parent: (@list E)) (rg_2: G) (s_after: St) (i: Z) (l_vertex_parent: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg_2 s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent l_edge_parent 1000000000 i )) (PreH16 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix_2 )
|--
  EX (result_matrix: (@list (@list Z)))  (rg: G) ,
  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_matrix_matches result_matrix rg 1000000000 ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix_2: (@list (@list Z))) (l_edge_parent: (@list E)) (rg_2: G) (s_after: St) (i: Z) (l_vertex_parent: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg_2 s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix_2 l_vertex_parent l_edge_parent 1000000000 i )) (PreH16 : (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (rg: G) ,
  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_matrix_matches result_matrix_2 rg 1000000000 ) ”
  &&  emp
).

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_1_pure := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "visited" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (n_pre > 0) ”
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_1_aux := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (PreH1 : (src_low_level_spec = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH5 : (prim_input_weight_bound n_pre 1000000000 )) (PreH6 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH7 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (n_pre > 0) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_1 := prim_adjacency_matrix_return_matrix_partial_solve_wit_1_pure -> prim_adjacency_matrix_return_matrix_partial_solve_wit_1_aux.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_2 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((visited + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg visited (i + 1 ) n_pre )
  **  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_3_pure := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_3_aux := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.seg visited 0 i (repeat_Z (0) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_3 := prim_adjacency_matrix_return_matrix_partial_solve_wit_3_pure -> prim_adjacency_matrix_return_matrix_partial_solve_wit_3_aux.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_4 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((lowcost + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg lowcost (i + 1 ) n_pre )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_5_pure := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "vertex_parent" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (IntArray.undef_seg lowcost i n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (n_pre > 0) ”
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_5_aux := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (IntArray.undef_seg lowcost i n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
|--
  “ (n_pre > 0) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg lowcost 0 i (repeat_Z (1000000000) (i)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_5 := prim_adjacency_matrix_return_matrix_partial_solve_wit_5_pure -> prim_adjacency_matrix_return_matrix_partial_solve_wit_5_aux.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_6 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg vertex_parent i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((vertex_parent + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg vertex_parent (i + 1 ) n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_7 := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full lowcost n_pre (repeat_Z (1000000000) (n_pre)) )
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
  **  (IntArray.undef_seg vertex_parent i n_pre )
|--
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((lowcost + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i lowcost 0 0 n_pre (repeat_Z (1000000000) (n_pre)) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.seg vertex_parent 0 i (repeat_Z ((-1)) (i)) )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_8_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (i = 0)) (PreH15 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH16 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH17 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH18 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH23 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (((visited + (j * sizeof(INT)))) # Int  |-> (Znth j l_visited 0))
  **  (IntArray.missing_i visited j 0 n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_9_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (INT_MIN <= min)) (PreH13 : (min <= INT_MAX)) (PreH14 : (1 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH17 : (growing_subgraph_state g_low_level_spec s )) (PreH18 : (visited_matches_state g_low_level_spec s l_visited )) (PreH19 : ((state_vertex_count (s)) = i)) (PreH20 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH21 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH22 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH23 : (lowcost_sum_matches_state s l_lowcost )) (PreH24 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH25 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH26 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH27 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH28 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH29 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_10_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited 0) = 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s )) (PreH19 : (visited_matches_state g_low_level_spec s l_visited )) (PreH20 : ((state_vertex_count (s)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH22 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH23 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH24 : (lowcost_sum_matches_state s l_lowcost )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH26 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH27 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH28 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH29 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH30 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_11_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_visited 0) = 0)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH18 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH19 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH20 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH21 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH22 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH23 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH24 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth j l_lowcost 0))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_12_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_visited: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_lowcost: (@list Z)) (minIndex: Z) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) < min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (i = 0)) (PreH17 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH18 : ((j = 0) -> ((min = 1000000000) /\ (minIndex = (-1))))) (PreH19 : ((1 <= j) -> ((min = 0) /\ (minIndex = 0)))) (PreH20 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) (PreH21 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH22 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH23 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH24 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH25 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (((lowcost + (j * sizeof(INT)))) # Int  |-> (Znth j l_lowcost 0))
  **  (IntArray.missing_i lowcost j 0 n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_13_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (minIndex: Z) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (l_visited: (@list Z)) (s: St) (min: Z) (i: Z) (j: Z) (PreH1 : ((Znth j l_lowcost 0) < min)) (PreH2 : ((Znth j l_visited 0) = 0)) (PreH3 : (j < n_pre)) (PreH4 : (0 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (src_low_level_spec = 0)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH12 : (prim_input_weight_bound n_pre 1000000000 )) (PreH13 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH14 : (INT_MIN <= min)) (PreH15 : (min <= INT_MAX)) (PreH16 : (1 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH19 : (growing_subgraph_state g_low_level_spec s )) (PreH20 : (visited_matches_state g_low_level_spec s l_visited )) (PreH21 : ((state_vertex_count (s)) = i)) (PreH22 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH23 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH24 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH25 : (lowcost_sum_matches_state s l_lowcost )) (PreH26 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH27 : ((i < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 ))) (PreH28 : (min_vertex_in_range g_low_level_spec s j 1000000000 minIndex l_lowcost l_edge_parent )) (PreH29 : ((minIndex = (-1)) -> (min = 1000000000))) (PreH30 : ((minIndex <> (-1)) -> (min = (Znth (minIndex) (l_lowcost) (0))))) (PreH31 : ((minIndex <> (-1)) -> ((0 <= minIndex) /\ (minIndex < j)))) ,
  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_14_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (i = 0)) (PreH16 : (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec )) (PreH17 : (min = 0)) (PreH18 : (minIndex = 0)) (PreH19 : (l_lowcost = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH20 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH21 : (l_edge_parent = (default_edge_list (n_pre)))) (PreH22 : (l_vertex_parent = (repeat_Z ((-1)) (n_pre)))) (PreH23 : (l_visited = (repeat_Z (0) (n_pre)))) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (l_vertex_parent = (repeat_Z ((-1)) (n_pre))) ” 
  &&  “ (l_visited = (repeat_Z (0) (n_pre))) ”
  &&  (((visited + (minIndex * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i visited minIndex 0 n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_15_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s: St) (u: Z) (v: Z) (i: Z) (minIndex: Z) (min: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z) (PreH1 : (minIndex < n_pre)) (PreH2 : (0 <= minIndex)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= minIndex)) (PreH6 : (minIndex < n_pre)) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (INT_MIN <= min)) (PreH14 : (min <= INT_MAX)) (PreH15 : (1 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i - 1 ))) X_low_level_spec )) (PreH18 : (growing_subgraph_state g_low_level_spec s )) (PreH19 : (visited_matches_state g_low_level_spec s l_visited )) (PreH20 : ((state_vertex_count (s)) = i)) (PreH21 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent )) (PreH22 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH23 : (lowcost_parent_match g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH24 : (lowcost_sum_matches_state s l_lowcost )) (PreH25 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH26 : (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost l_edge_parent 1000000000 )) (PreH27 : (minIndex <> (-1))) (PreH28 : (min = (Znth (minIndex) (l_lowcost) (0)))) (PreH29 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent minIndex )) (PreH30 : (selected_parent_pair g_low_level_spec s l_edge_parent minIndex u v )) (PreH31 : (min_vertex_in_range g_low_level_spec s n_pre 1000000000 minIndex l_lowcost l_edge_parent )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
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
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
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
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_16_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (u: Z) (v: Z) (l_edge_parent0: (@list E)) (l_visited: (@list Z)) (s: St) (s_after: St) (l_lowcost0: (@list Z)) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (INT_MIN <= min)) (PreH17 : (min <= INT_MAX)) (PreH18 : (1 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (min = (Znth (minIndex) (l_lowcost0) (0)))) (PreH21 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (i)) X_low_level_spec )) (PreH22 : (growing_subgraph_state g_low_level_spec s )) (PreH23 : (visited_matches_state g_low_level_spec s l_visited )) (PreH24 : ((state_vertex_count (s)) = i)) (PreH25 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent0 )) (PreH26 : (lowcost_parent_match g_low_level_spec s l_lowcost0 l_edge_parent0 1000000000 )) (PreH27 : (selected_parent_edge_is_min_cut_edge g_low_level_spec s l_edge_parent0 minIndex )) (PreH28 : (selected_parent_pair g_low_level_spec s l_edge_parent0 minIndex u v )) (PreH29 : (selected_parent_add_to_mst g_low_level_spec s s_after l_edge_parent0 minIndex )) (PreH30 : (growing_subgraph_state g_low_level_spec s_after )) (PreH31 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH32 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH33 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent0 )) (PreH34 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH35 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH36 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH37 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH38 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH39 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH40 : (0 <= j)) (PreH41 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_17_boot := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (row_ptr: Z) (l_vertex_parent: (@list Z)) (l_lowcost: (@list Z)) (l_edge_parent: (@list E)) (l_edge_parent0: (@list E)) (l_lowcost0: (@list Z)) (l_visited: (@list Z)) (s_after: St) (min: Z) (minIndex: Z) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= minIndex)) (PreH7 : (minIndex < n_pre)) (PreH8 : ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre)) (PreH9 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH10 : (src_low_level_spec = 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) (PreH13 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH14 : (prim_input_weight_bound n_pre 1000000000 )) (PreH15 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH16 : (INT_MIN <= min)) (PreH17 : (min <= INT_MAX)) (PreH18 : (i = 0)) (PreH19 : (minIndex = 0)) (PreH20 : (min = 0)) (PreH21 : (s_after = (initSt (g_low_level_spec) (src_low_level_spec)))) (PreH22 : (safeExec (prim_state_is (s_after)) (Prim2_loop (g_low_level_spec) (0)) X_low_level_spec )) (PreH23 : (growing_subgraph_state g_low_level_spec s_after )) (PreH24 : (visited_matches_state g_low_level_spec s_after (replace_Znth (minIndex) (1) (l_visited)) )) (PreH25 : ((state_vertex_count (s_after)) = 1)) (PreH26 : (lowcost_sum_matches_state s_after l_lowcost0 )) (PreH27 : (lowcost_values_in_range 1000000000 l_lowcost0 )) (PreH28 : (l_lowcost0 = (replace_Znth (0) (0) ((repeat_Z (1000000000) (n_pre)))))) (PreH29 : (l_edge_parent0 = (default_edge_list (n_pre)))) (PreH30 : (l_visited = (repeat_Z (0) (n_pre)))) (PreH31 : (scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec 1000000000 s_after minIndex j l_lowcost0 l_edge_parent0 l_lowcost l_edge_parent )) (PreH32 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH33 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH34 : (lowcost_values_in_range 1000000000 l_lowcost )) (PreH35 : (0 <= j)) (PreH36 : (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))))) ,
  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ ((Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) = n_pre) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
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
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z)))))) ”
  &&  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth j (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (minIndex) (matrix_low_level_spec) ((@nil Z))))) (Znth (minIndex) (matrix_low_level_spec) ((@nil Z))) )
  **  (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr matrix_low_level_spec )
  **  (((graph_pre + (minIndex * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full visited n_pre (replace_Znth (minIndex) (1) (l_visited)) )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_18_running_pure := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (1 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "mst" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(PTR) * n_pre ) = (sizeof(PTR) * n_pre )) ”
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_18_running_aux := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (1 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(PTR) * n_pre ) = (sizeof(PTR) * n_pre )) ” 
  &&  “ (i_2 >= n_pre) ” 
  &&  “ (1 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = i_2) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_2 ) ” 
  &&  “ ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_18_running := prim_adjacency_matrix_return_matrix_partial_solve_wit_18_running_pure -> prim_adjacency_matrix_return_matrix_partial_solve_wit_18_running_aux.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_19_running_pure := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (i = 0)) (PreH25 : (minIndex = 0)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  ((( &( "mst" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited_2 )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(PTR) * n_pre ) = (sizeof(PTR) * n_pre )) ”
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_19_running_aux := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (i: Z) (minIndex: Z) (min: Z) (vertex_parent: Z) (lowcost: Z) (visited: Z) (l_lowcost_2: (@list Z)) (l_vertex_parent_2: (@list Z)) (l_edge_parent_2: (@list E)) (l_visited_2: (@list Z)) (s: St) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s )) (PreH11 : (visited_matches_state g_low_level_spec s l_visited_2 )) (PreH12 : ((state_vertex_count (s)) = i_2)) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 )) (PreH15 : (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) (PreH16 : (lowcost_sum_matches_state s l_lowcost_2 )) (PreH17 : (lowcost_values_in_range 1000000000 l_lowcost_2 )) (PreH18 : ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ))) (PreH19 : (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec )) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= minIndex)) (PreH23 : (minIndex < n_pre)) (PreH24 : (i = 0)) (PreH25 : (minIndex = 0)) (PreH26 : (src_low_level_spec = 0)) (PreH27 : (2 <= n_pre)) (PreH28 : (n_pre < INT_MAX)) (PreH29 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH30 : (prim_input_weight_bound n_pre 1000000000 )) (PreH31 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH32 : (INT_MIN <= min)) (PreH33 : (min <= INT_MAX)) (PreH34 : (growing_subgraph_state g_low_level_spec s_after )) (PreH35 : (visited_matches_state g_low_level_spec s_after l_visited )) (PreH36 : ((state_vertex_count (s_after)) = (i + 1 ))) (PreH37 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH38 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH39 : (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 )) (PreH40 : (lowcost_sum_matches_state s_after l_lowcost )) (PreH41 : (lowcost_values_in_range 1000000000 l_lowcost )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ ((sizeof(PTR) * n_pre ) = (sizeof(PTR) * n_pre )) ” 
  &&  “ (i_2 >= n_pre) ” 
  &&  “ (1 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s ) ” 
  &&  “ (visited_matches_state g_low_level_spec s l_visited_2 ) ” 
  &&  “ ((state_vertex_count (s)) = i_2) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s l_edge_parent_2 ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent_2 l_edge_parent_2 ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s l_lowcost_2 ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost_2 ) ” 
  &&  “ ((i_2 < n_pre) -> (candidate_vertex_exists_in_range n_pre g_low_level_spec s l_lowcost_2 l_edge_parent_2 1000000000 )) ” 
  &&  “ (safeExec (prim_state_is (s)) (Prim2_loop (g_low_level_spec) ((i_2 - 1 ))) X_low_level_spec ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= minIndex) ” 
  &&  “ (minIndex < n_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (minIndex = 0) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (INT_MIN <= min) ” 
  &&  “ (min <= INT_MAX) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ (visited_matches_state g_low_level_spec s_after l_visited ) ” 
  &&  “ ((state_vertex_count (s_after)) = (i + 1 )) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (lowcost_parent_match g_low_level_spec s_after l_lowcost l_edge_parent 1000000000 ) ” 
  &&  “ (lowcost_sum_matches_state s_after l_lowcost ) ” 
  &&  “ (lowcost_values_in_range 1000000000 l_lowcost ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited_2 )
  **  (IntArray.full lowcost n_pre l_lowcost_2 )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent_2 )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_19_running := prim_adjacency_matrix_return_matrix_partial_solve_wit_19_running_pure -> prim_adjacency_matrix_return_matrix_partial_solve_wit_19_running_aux.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_20_running_pure := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (mst: Z) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix = (inf_matrix (i) (n_pre) (1000000000)))) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "graph" ) )) # Ptr  |-> graph_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mst" ) )) # Ptr  |-> mst)
  **  (PtrArray.undef_seg mst i n_pre )
  **  (IntPtrArray2.full mst i result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  ((( &( "visited" ) )) # Ptr  |-> visited)
  **  (IntArray.full visited n_pre l_visited )
  **  ((( &( "lowcost" ) )) # Ptr  |-> lowcost)
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  ((( &( "vertex_parent" ) )) # Ptr  |-> vertex_parent)
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (n_pre > 0) ”
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_20_running_aux := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (mst: Z) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix = (inf_matrix (i) (n_pre) (1000000000)))) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (PtrArray.undef_seg mst i n_pre )
  **  (IntPtrArray2.full mst i result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (n_pre > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix = (inf_matrix (i) (n_pre) (1000000000))) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (PtrArray.undef_seg mst i n_pre )
  **  (IntPtrArray2.full mst i result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_20_running := prim_adjacency_matrix_return_matrix_partial_solve_wit_20_running_pure -> prim_adjacency_matrix_return_matrix_partial_solve_wit_20_running_aux.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_21_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (mst: Z) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (retval: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix = (inf_matrix (i) (n_pre) (1000000000)))) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (IntArray.undef_full retval n_pre )
  **  (PtrArray.undef_seg mst i n_pre )
  **  (IntPtrArray2.full mst i result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix = (inf_matrix (i) (n_pre) (1000000000))) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (((mst + (i * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (IntArray.undef_full retval n_pre )
  **  (IntPtrArray2.full mst i result_matrix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_22_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (row_ptr: Z) (mst: Z) (row_prefix: (@list Z)) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after )) (PreH13 : ((state_vertex_count (s_after)) = n_pre)) (PreH14 : (prim_state_graph_matches rg s_after )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH17 : (result_matrix = (inf_matrix (i) (n_pre) (1000000000)))) (PreH18 : (row_prefix = (repeat_Z (1000000000) (j)))) (PreH19 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (IntPtrArray2.full mst i result_matrix )
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.seg row_ptr 0 j row_prefix )
  **  (IntArray.undef_seg row_ptr j n_pre )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix = (inf_matrix (i) (n_pre) (1000000000))) ” 
  &&  “ (row_prefix = (repeat_Z (1000000000) (j))) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (((row_ptr + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg row_ptr (j + 1 ) n_pre )
  **  (IntPtrArray2.full mst i result_matrix )
  **  (PtrArray.undef_seg mst (i + 1 ) n_pre )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.seg row_ptr 0 j row_prefix )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_23_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (l_lowcost: (@list Z)) (visited: Z) (l_visited: (@list Z)) (mst: Z) (result_matrix: (@list (@list Z))) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (((vertex_parent + (i * sizeof(INT)))) # Int  |-> (Znth i l_vertex_parent 0))
  **  (IntArray.missing_i vertex_parent i 0 n_pre l_vertex_parent )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_24_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (rg: G) (row_ptr: Z) (i: Z) (p: Z) (mst: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (p = (Znth i l_vertex_parent 0))) (PreH6 : (src_low_level_spec = 0)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH10 : (prim_input_weight_bound n_pre 1000000000 )) (PreH11 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH12 : (growing_subgraph_state g_low_level_spec s_after )) (PreH13 : ((state_vertex_count (s_after)) = n_pre)) (PreH14 : (prim_state_graph_matches rg s_after )) (PreH15 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH16 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH17 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH18 : (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec )) (PreH19 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (IntPtrArray2.missing_i graph_pre n_pre p row_ptr matrix_low_level_spec )
  **  (((graph_pre + (p * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr n_pre (Znth p matrix_low_level_spec __default__List_Z) )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (p = (Znth i l_vertex_parent 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000 matrix_low_level_spec ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (((row_ptr + (i * sizeof(INT)))) # Int  |-> (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))
  **  (IntArray.missing_i row_ptr i 0 n_pre (Znth p matrix_low_level_spec __default__List_Z) )
  **  (IntPtrArray2.missing_i graph_pre n_pre p row_ptr matrix_low_level_spec )
  **  (((graph_pre + (p * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_25_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (rg: G) (mst_row: Z) (i: Z) (p: Z) (w: Z) (mst: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))) (PreH6 : (p = (Znth i l_vertex_parent 0))) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after )) (PreH14 : ((state_vertex_count (s_after)) = n_pre)) (PreH15 : (prim_state_graph_matches rg s_after )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH19 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre p mst_row result_matrix )
  **  (((mst + (p * sizeof(PTR)))) # Ptr  |-> mst_row)
  **  (IntArray.full mst_row n_pre (Znth p result_matrix __default__List_Z) )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0)) ” 
  &&  “ (p = (Znth i l_vertex_parent 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (((mst_row + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i mst_row i 0 n_pre (Znth p result_matrix __default__List_Z) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre p mst_row result_matrix )
  **  (((mst + (p * sizeof(PTR)))) # Ptr  |-> mst_row)
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_26_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (result_matrix: (@list (@list Z))) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (l_edge_parent: (@list E)) (s_after: St) (rg: G) (mst_row: Z) (i: Z) (p: Z) (w: Z) (mst: Z) (visited: Z) (lowcost: Z) (vertex_parent: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= p)) (PreH4 : (p < n_pre)) (PreH5 : (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0))) (PreH6 : (p = (Znth i l_vertex_parent 0))) (PreH7 : (src_low_level_spec = 0)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH11 : (prim_input_weight_bound n_pre 1000000000 )) (PreH12 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH13 : (growing_subgraph_state g_low_level_spec s_after )) (PreH14 : ((state_vertex_count (s_after)) = n_pre)) (PreH15 : (prim_state_graph_matches rg s_after )) (PreH16 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH17 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH18 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH19 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre i mst_row (set_matrix_entry (result_matrix) (p) (i) (w)) )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> mst_row)
  **  (IntArray.full mst_row n_pre (Znth i (set_matrix_entry (result_matrix) (p) (i) (w)) __default__List_Z) )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (w = (Znth i (Znth p matrix_low_level_spec __default__List_Z) 0)) ” 
  &&  “ (p = (Znth i l_vertex_parent 0)) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (((mst_row + (p * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i mst_row p 0 n_pre (Znth i (set_matrix_entry (result_matrix) (p) (i) (w)) __default__List_Z) )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.missing_i mst n_pre i mst_row (set_matrix_entry (result_matrix) (p) (i) (w)) )
  **  (((mst + (i * sizeof(PTR)))) # Ptr  |-> mst_row)
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_27_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (visited: Z) (mst: Z) (result_matrix: (@list (@list Z))) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (l_visited: (@list Z)) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full visited n_pre l_visited )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full visited n_pre l_visited )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_28_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (lowcost: Z) (mst: Z) (result_matrix: (@list (@list Z))) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (l_lowcost: (@list Z)) (l_vertex_parent: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full lowcost n_pre l_lowcost )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full lowcost n_pre l_lowcost )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
.

Definition prim_adjacency_matrix_return_matrix_partial_solve_wit_29_running := 
forall (graph_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (src_low_level_spec: Z) (g_low_level_spec: G) (matrix_low_level_spec: (@list (@list Z))) (vertex_parent: Z) (mst: Z) (result_matrix: (@list (@list Z))) (l_edge_parent: (@list E)) (rg: G) (s_after: St) (i: Z) (l_vertex_parent: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (src_low_level_spec = 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((n_pre * sizeof(PTR) ) <= UINT_MAX)) (PreH8 : (prim_input_weight_bound n_pre 1000000000 )) (PreH9 : (PrimEnv g_low_level_spec src_low_level_spec )) (PreH10 : (growing_subgraph_state g_low_level_spec s_after )) (PreH11 : ((state_vertex_count (s_after)) = n_pre)) (PreH12 : (prim_state_graph_matches rg s_after )) (PreH13 : (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent )) (PreH14 : (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent )) (PreH15 : (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i )) (PreH16 : (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec )) ,
  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
  **  (IntArray.full vertex_parent n_pre l_vertex_parent )
|--
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (growing_subgraph_state g_low_level_spec s_after ) ” 
  &&  “ ((state_vertex_count (s_after)) = n_pre) ” 
  &&  “ (prim_state_graph_matches rg s_after ) ” 
  &&  “ (selected_edges_match_state g_low_level_spec src_low_level_spec s_after l_edge_parent ) ” 
  &&  “ (vertex_parent_matches_edge_parent g_low_level_spec src_low_level_spec l_vertex_parent l_edge_parent ) ” 
  &&  “ (result_matrix_parent_prefix g_low_level_spec src_low_level_spec matrix_low_level_spec result_matrix l_vertex_parent l_edge_parent 1000000000 i ) ” 
  &&  “ (safeExec (prim_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full vertex_parent n_pre l_vertex_parent )
  **  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full mst n_pre result_matrix )
.

Definition prim_adjacency_matrix_return_matrix_derive_high_level_spec_by_low_level_spec := 
forall (graph_pre: Z) (n_pre: Z) (src_high_level_spec: Z) (g_high_level_spec: G) (matrix_high_level_spec: (@list (@list Z))) ,
  “ (src_high_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_high_level_spec src_high_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_high_level_spec) (1000000000)) graph_pre matrix_high_level_spec )
|--
EX (matrix_low_level_spec: (@list (@list Z))) (g_low_level_spec: G) (src_low_level_spec: Z) (X_low_level_spec: (unit -> (St -> Prop))) ,
  (“ (src_low_level_spec = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((n_pre * sizeof(PTR) ) <= UINT_MAX) ” 
  &&  “ (prim_input_weight_bound n_pre 1000000000 ) ” 
  &&  “ (PrimEnv g_low_level_spec src_low_level_spec ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec) (src_low_level_spec)) (Prim2 (g_low_level_spec)) X_low_level_spec ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec ))
  **
  ((EX result_matrix_2 rg_2 retval_2,
  “ (safeExec (prim_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (prim_result_matrix_matches result_matrix_2 rg_2 1000000000 ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_low_level_spec) (1000000000)) graph_pre matrix_low_level_spec )
  **  (IntPtrArray2.full retval_2 n_pre result_matrix_2 ))
  -*
  (EX result_matrix rg retval,
  “ (return_is_mst g_high_level_spec rg ) ” 
  &&  “ (prim_result_matrix_matches result_matrix rg 1000000000 ) ”
  &&  (GraphMatrixPtr.store_graph n_pre (prim_adjacency_matrix_graph_model (n_pre) (g_high_level_spec) (1000000000)) graph_pre matrix_high_level_spec )
  **  (IntPtrArray2.full retval n_pre result_matrix )))
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

Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_1 : prim_adjacency_matrix_return_matrix_safety_wit_1.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_2 : prim_adjacency_matrix_return_matrix_safety_wit_2.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_3 : prim_adjacency_matrix_return_matrix_safety_wit_3.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_4 : prim_adjacency_matrix_return_matrix_safety_wit_4.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_5 : prim_adjacency_matrix_return_matrix_safety_wit_5.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_6 : prim_adjacency_matrix_return_matrix_safety_wit_6.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_7 : prim_adjacency_matrix_return_matrix_safety_wit_7.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_8 : prim_adjacency_matrix_return_matrix_safety_wit_8.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_9 : prim_adjacency_matrix_return_matrix_safety_wit_9.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_10 : prim_adjacency_matrix_return_matrix_safety_wit_10.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_11 : prim_adjacency_matrix_return_matrix_safety_wit_11.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_12 : prim_adjacency_matrix_return_matrix_safety_wit_12.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_13 : prim_adjacency_matrix_return_matrix_safety_wit_13.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_14_boot : prim_adjacency_matrix_return_matrix_safety_wit_14_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_15_boot : prim_adjacency_matrix_return_matrix_safety_wit_15_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_16_boot : prim_adjacency_matrix_return_matrix_safety_wit_16_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_17_boot : prim_adjacency_matrix_return_matrix_safety_wit_17_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_18_boot : prim_adjacency_matrix_return_matrix_safety_wit_18_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_19_boot : prim_adjacency_matrix_return_matrix_safety_wit_19_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_20_boot : prim_adjacency_matrix_return_matrix_safety_wit_20_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_21_boot : prim_adjacency_matrix_return_matrix_safety_wit_21_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_22_boot : prim_adjacency_matrix_return_matrix_safety_wit_22_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_23_boot : prim_adjacency_matrix_return_matrix_safety_wit_23_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_24_boot : prim_adjacency_matrix_return_matrix_safety_wit_24_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_25_boot : prim_adjacency_matrix_return_matrix_safety_wit_25_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_26_boot : prim_adjacency_matrix_return_matrix_safety_wit_26_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_27_boot : prim_adjacency_matrix_return_matrix_safety_wit_27_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_28_boot : prim_adjacency_matrix_return_matrix_safety_wit_28_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_29_boot : prim_adjacency_matrix_return_matrix_safety_wit_29_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_30_boot : prim_adjacency_matrix_return_matrix_safety_wit_30_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_31_boot : prim_adjacency_matrix_return_matrix_safety_wit_31_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_32_boot : prim_adjacency_matrix_return_matrix_safety_wit_32_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_33_boot : prim_adjacency_matrix_return_matrix_safety_wit_33_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_34_boot : prim_adjacency_matrix_return_matrix_safety_wit_34_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_35_boot : prim_adjacency_matrix_return_matrix_safety_wit_35_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_36_boot : prim_adjacency_matrix_return_matrix_safety_wit_36_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_37_boot : prim_adjacency_matrix_return_matrix_safety_wit_37_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_38_boot : prim_adjacency_matrix_return_matrix_safety_wit_38_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_39_boot : prim_adjacency_matrix_return_matrix_safety_wit_39_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_40_boot : prim_adjacency_matrix_return_matrix_safety_wit_40_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_41_boot : prim_adjacency_matrix_return_matrix_safety_wit_41_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_42_boot : prim_adjacency_matrix_return_matrix_safety_wit_42_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_43_boot : prim_adjacency_matrix_return_matrix_safety_wit_43_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_44_boot : prim_adjacency_matrix_return_matrix_safety_wit_44_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_45_boot : prim_adjacency_matrix_return_matrix_safety_wit_45_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_46_boot : prim_adjacency_matrix_return_matrix_safety_wit_46_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_47_boot : prim_adjacency_matrix_return_matrix_safety_wit_47_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_48_boot : prim_adjacency_matrix_return_matrix_safety_wit_48_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_49_running : prim_adjacency_matrix_return_matrix_safety_wit_49_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_50_running : prim_adjacency_matrix_return_matrix_safety_wit_50_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_51_running : prim_adjacency_matrix_return_matrix_safety_wit_51_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_52_running : prim_adjacency_matrix_return_matrix_safety_wit_52_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_53_running : prim_adjacency_matrix_return_matrix_safety_wit_53_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_54_running : prim_adjacency_matrix_return_matrix_safety_wit_54_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_55_running : prim_adjacency_matrix_return_matrix_safety_wit_55_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_56_running : prim_adjacency_matrix_return_matrix_safety_wit_56_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_57_boot : prim_adjacency_matrix_return_matrix_safety_wit_57_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_58_boot : prim_adjacency_matrix_return_matrix_safety_wit_58_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_59_running : prim_adjacency_matrix_return_matrix_safety_wit_59_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_60_running : prim_adjacency_matrix_return_matrix_safety_wit_60_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_61_running : prim_adjacency_matrix_return_matrix_safety_wit_61_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_62_running : prim_adjacency_matrix_return_matrix_safety_wit_62_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_63_running : prim_adjacency_matrix_return_matrix_safety_wit_63_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_64_running : prim_adjacency_matrix_return_matrix_safety_wit_64_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_65_running : prim_adjacency_matrix_return_matrix_safety_wit_65_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_66_running : prim_adjacency_matrix_return_matrix_safety_wit_66_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_67_running : prim_adjacency_matrix_return_matrix_safety_wit_67_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_68_running : prim_adjacency_matrix_return_matrix_safety_wit_68_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_safety_wit_69_running : prim_adjacency_matrix_return_matrix_safety_wit_69_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_1 : prim_adjacency_matrix_return_matrix_entail_wit_1.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_2 : prim_adjacency_matrix_return_matrix_entail_wit_2.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_3 : prim_adjacency_matrix_return_matrix_entail_wit_3.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_4 : prim_adjacency_matrix_return_matrix_entail_wit_4.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_5 : prim_adjacency_matrix_return_matrix_entail_wit_5.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_6 : prim_adjacency_matrix_return_matrix_entail_wit_6.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_7_boot : prim_adjacency_matrix_return_matrix_entail_wit_7_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_8_boot : prim_adjacency_matrix_return_matrix_entail_wit_8_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_9_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_9_1_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_9_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_9_2_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_9_3_boot : prim_adjacency_matrix_return_matrix_entail_wit_9_3_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_9_4_boot : prim_adjacency_matrix_return_matrix_entail_wit_9_4_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_9_5_boot : prim_adjacency_matrix_return_matrix_entail_wit_9_5_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_9_6_boot : prim_adjacency_matrix_return_matrix_entail_wit_9_6_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_10_2_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_11_1_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_11_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_11_2_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_12_2_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_13_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_13_1_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_13_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_13_2_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_1_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_2_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_3_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_3_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_4_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_4_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_5_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_5_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_6_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_6_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_7_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_7_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_8_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_8_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_15_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_15_1_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_15_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_15_2_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_1_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_2_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_17_1_running : prim_adjacency_matrix_return_matrix_entail_wit_17_1_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_17_2_running : prim_adjacency_matrix_return_matrix_entail_wit_17_2_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_18_1_running : prim_adjacency_matrix_return_matrix_entail_wit_18_1_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_18_2_running : prim_adjacency_matrix_return_matrix_entail_wit_18_2_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_19_1_running : prim_adjacency_matrix_return_matrix_entail_wit_19_1_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_19_2_running : prim_adjacency_matrix_return_matrix_entail_wit_19_2_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_20_running : prim_adjacency_matrix_return_matrix_entail_wit_20_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_21_running : prim_adjacency_matrix_return_matrix_entail_wit_21_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_22_running : prim_adjacency_matrix_return_matrix_entail_wit_22_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_23_running : prim_adjacency_matrix_return_matrix_entail_wit_23_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_24_running : prim_adjacency_matrix_return_matrix_entail_wit_24_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_25_running : prim_adjacency_matrix_return_matrix_entail_wit_25_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_26_running : prim_adjacency_matrix_return_matrix_entail_wit_26_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_27_running : prim_adjacency_matrix_return_matrix_entail_wit_27_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_28_1_running : prim_adjacency_matrix_return_matrix_entail_wit_28_1_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_28_2_running : prim_adjacency_matrix_return_matrix_entail_wit_28_2_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_entail_wit_28_3_running : prim_adjacency_matrix_return_matrix_entail_wit_28_3_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_return_wit_1_running : prim_adjacency_matrix_return_matrix_return_wit_1_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_1_pure : prim_adjacency_matrix_return_matrix_partial_solve_wit_1_pure.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_1 : prim_adjacency_matrix_return_matrix_partial_solve_wit_1.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_2 : prim_adjacency_matrix_return_matrix_partial_solve_wit_2.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_3_pure : prim_adjacency_matrix_return_matrix_partial_solve_wit_3_pure.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_3 : prim_adjacency_matrix_return_matrix_partial_solve_wit_3.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_4 : prim_adjacency_matrix_return_matrix_partial_solve_wit_4.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_5_pure : prim_adjacency_matrix_return_matrix_partial_solve_wit_5_pure.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_5 : prim_adjacency_matrix_return_matrix_partial_solve_wit_5.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_6 : prim_adjacency_matrix_return_matrix_partial_solve_wit_6.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_7 : prim_adjacency_matrix_return_matrix_partial_solve_wit_7.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_8_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_8_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_9_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_9_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_10_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_10_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_11_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_11_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_12_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_12_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_13_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_13_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_14_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_14_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_15_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_15_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_16_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_16_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_17_boot : prim_adjacency_matrix_return_matrix_partial_solve_wit_17_boot.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_18_running_pure : prim_adjacency_matrix_return_matrix_partial_solve_wit_18_running_pure.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_18_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_18_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_19_running_pure : prim_adjacency_matrix_return_matrix_partial_solve_wit_19_running_pure.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_19_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_19_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_20_running_pure : prim_adjacency_matrix_return_matrix_partial_solve_wit_20_running_pure.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_20_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_20_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_21_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_21_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_22_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_22_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_23_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_23_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_24_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_24_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_25_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_25_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_26_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_26_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_27_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_27_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_28_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_28_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_partial_solve_wit_29_running : prim_adjacency_matrix_return_matrix_partial_solve_wit_29_running.
Axiom proof_of_prim_adjacency_matrix_return_matrix_derive_high_level_spec_by_low_level_spec : prim_adjacency_matrix_return_matrix_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
