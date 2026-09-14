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
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.dfs2_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import safeexecE_strategy_goal.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import safeexecE_strategy_proof.

(*----- Function dfs2 -----*)

Definition dfs2_safety_wit_1 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_safety_wit_2 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_safety_wit_3 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre fadj_row_l_low_level_spec 0))
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  “ ((u_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u_pre + 1 )) ”
.

Definition dfs2_safety_wit_4 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre fadj_row_l_low_level_spec 0))
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_safety_wit_5 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre fadj_row_l_low_level_spec 0))
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  “ ((u_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u_pre + 1 )) ”
.

Definition dfs2_safety_wit_6 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre fadj_row_l_low_level_spec 0))
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_safety_wit_7 := 
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH11 : (0 <= u0_low_level_spec)) (PreH12 : (u0_low_level_spec < n0_low_level_spec)) (PreH13 : (0 <= root0_low_level_spec)) (PreH14 : (root0_low_level_spec < n0_low_level_spec)) (PreH15 : (n0_low_level_spec <= 2147483646)) (PreH16 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH20 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH21 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))) (PreH22 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH23 : (0 <= v)) (PreH24 : (v < n0_low_level_spec)) (PreH25 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs2_safety_wit_8 := 
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_m) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_m) (0)) <> 0) -> ((Znth (w_2) (sid_l_) (0)) = (Znth (w_2) (sid_m) (0)))))) (PreH7 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_l_) (0)) <> 0) -> (((Znth (w_3) (vis2_m) (0)) = 0) -> ((Znth (w_3) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m) (0))))))) (PreH8 : ((Znth v vis2_m 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH25 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH27 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH28 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_l_ )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_l_ )
  **  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dfs2_safety_wit_9 := 
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_m) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_m) (0)) <> 0) -> ((Znth (w_2) (sid_l_) (0)) = (Znth (w_2) (sid_m) (0)))))) (PreH7 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_l_) (0)) <> 0) -> (((Znth (w_3) (vis2_m) (0)) = 0) -> ((Znth (w_3) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m) (0))))))) (PreH8 : ((Znth v vis2_m 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH25 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH27 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH28 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_l_ )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_l_ )
  **  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_safety_wit_10 := 
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dfs2_safety_wit_11 := 
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_entail_wit_1_1 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z)) ,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((Znth u_pre fadj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= (Znth u_pre fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth u_pre fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u0_low_level_spec) ” 
  &&  “ (u0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , ((((Znth u_pre fadj_row_l_low_level_spec 0) <= j) /\ (j < (Znth u_pre fadj_row_l_low_level_spec 0))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ”
  &&  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
) \/
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  TT && emp 
|--
  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) ((replace_Znth (root_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) ((replace_Znth (root_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (0)) = (Znth (root_pre) (sid_l_low_level_spec) (0)))))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) ((replace_Znth (root_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) ((replace_Znth (root_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0))) ” 
  &&  “ ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) ” 
  &&  “ forall (j: Z) , ((((Znth root_pre fadj_row_l_low_level_spec 0) <= j) /\ (j < (Znth root_pre fadj_row_l_low_level_spec 0))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) ((replace_Znth (root_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)) ” 
  &&  “ ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0)) ” 
  &&  “ (0 <= (Znth u_pre fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) ((replace_Znth (u_pre) ((Znth u_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (u_pre) (u_pre) ((Znth u_pre fadj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) (replace_Znth (u_pre) ((Znth u_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) ) ”
  &&  emp
).

Definition dfs2_entail_wit_1_1_split_goal_1 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) ((replace_Znth (root_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) ((replace_Znth (root_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (0)) = (Znth (root_pre) (sid_l_low_level_spec) (0))))))
.

Definition dfs2_entail_wit_1_1_split_goal_2 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) ((replace_Znth (root_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))
.

Definition dfs2_entail_wit_1_1_split_goal_3 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) ((replace_Znth (root_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)))
.

Definition dfs2_entail_wit_1_1_split_goal_4 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)
.

Definition dfs2_entail_wit_1_1_split_goal_5 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  forall (j: Z) , ((((Znth root_pre fadj_row_l_low_level_spec 0) <= j) /\ (j < (Znth root_pre fadj_row_l_low_level_spec 0))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) ((replace_Znth (root_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0))
.

Definition dfs2_entail_wit_1_1_split_goal_6 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)
.

Definition dfs2_entail_wit_1_1_split_goal_7 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec)))
.

Definition dfs2_entail_wit_1_1_split_goal_8 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0))
.

Definition dfs2_entail_wit_1_1_split_goal_9 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  (0 <= (Znth u_pre fadj_row_l_low_level_spec 0))
.

Definition dfs2_entail_wit_1_1_split_goal_10 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))
.

Definition dfs2_entail_wit_1_1_split_goal_11 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  ((Znth u_pre fadj_row_l_low_level_spec 0) = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))
.

Definition dfs2_entail_wit_1_1_split_goal_12 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) ((replace_Znth (u_pre) ((Znth u_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (u_pre) (u_pre) ((Znth u_pre fadj_row_l_low_level_spec 0))) X_low_level_spec )
.

Definition dfs2_entail_wit_1_1_split_goal_13 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) (replace_Znth (u_pre) ((Znth u_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
.

Definition dfs2_entail_wit_1_2 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z)) ,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((Znth u_pre fadj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= (Znth u_pre fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth u_pre fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u0_low_level_spec) ” 
  &&  “ (u0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , ((((Znth u_pre fadj_row_l_low_level_spec 0) <= j) /\ (j < (Znth u_pre fadj_row_l_low_level_spec 0))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ”
  &&  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
) \/
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) ((replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (0)) = (Znth (root_pre) (sid_l_low_level_spec) (0)))))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) ((replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0))) ” 
  &&  “ ((Znth (root_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) ” 
  &&  “ forall (j: Z) , ((((Znth u_pre fadj_row_l_low_level_spec 0) <= j) /\ (j < (Znth u_pre fadj_row_l_low_level_spec 0))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)) ” 
  &&  “ ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0)) ” 
  &&  “ (0 <= (Znth u_pre fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) ((replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((Znth u_pre fadj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) ) ”
  &&  emp
).

Definition dfs2_entail_wit_1_2_split_goal_1 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) ((replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (0)) = (Znth (root_pre) (sid_l_low_level_spec) (0))))))
.

Definition dfs2_entail_wit_1_2_split_goal_2 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) ((replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))
.

Definition dfs2_entail_wit_1_2_split_goal_3 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)))
.

Definition dfs2_entail_wit_1_2_split_goal_4 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((Znth (root_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)
.

Definition dfs2_entail_wit_1_2_split_goal_5 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  forall (j: Z) , ((((Znth u_pre fadj_row_l_low_level_spec 0) <= j) /\ (j < (Znth u_pre fadj_row_l_low_level_spec 0))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0))
.

Definition dfs2_entail_wit_1_2_split_goal_6 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)
.

Definition dfs2_entail_wit_1_2_split_goal_7 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec)))
.

Definition dfs2_entail_wit_1_2_split_goal_8 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0))
.

Definition dfs2_entail_wit_1_2_split_goal_9 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (0 <= (Znth u_pre fadj_row_l_low_level_spec 0))
.

Definition dfs2_entail_wit_1_2_split_goal_10 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))
.

Definition dfs2_entail_wit_1_2_split_goal_11 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((Znth u_pre fadj_row_l_low_level_spec 0) = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))
.

Definition dfs2_entail_wit_1_2_split_goal_12 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) ((replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((Znth u_pre fadj_row_l_low_level_spec 0))) X_low_level_spec )
.

Definition dfs2_entail_wit_1_2_split_goal_13 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
.

Definition dfs2_entail_wit_2 := 
(
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u0_low_level_spec) ” 
  &&  “ (u0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ” 
  &&  “ (0 <= (Znth i fadj_col_l_low_level_spec 0)) ” 
  &&  “ ((Znth i fadj_col_l_low_level_spec 0) < n0_low_level_spec) ” 
  &&  “ ((Znth i fadj_col_l_low_level_spec 0) = (Znth (i) (fadj_col_l_low_level_spec) (0))) ”
  &&  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
) \/
(
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  TT && emp 
|--
  “ ((Znth i fadj_col_l_low_level_spec 0) < n0_low_level_spec) ” 
  &&  “ (0 <= (Znth i fadj_col_l_low_level_spec 0)) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ”
  &&  emp
).

Definition dfs2_entail_wit_2_split_goal_1 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  ((Znth i fadj_col_l_low_level_spec 0) < n0_low_level_spec)
.

Definition dfs2_entail_wit_2_split_goal_2 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  (0 <= (Znth i fadj_col_l_low_level_spec 0))
.

Definition dfs2_entail_wit_2_split_goal_3 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))
.

Definition dfs2_entail_wit_2_split_goal_4 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))
.

Definition dfs2_entail_wit_2_split_goal_5 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))
.

Definition dfs2_entail_wit_2_split_goal_6 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))
.

Definition dfs2_entail_wit_3_1 := 
(
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_m_2) (0)) <> 0) -> ((Znth (w_4) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_m_2) (0)) <> 0) -> ((Znth (w_5) (sid_l_) (0)) = (Znth (w_5) (sid_m_2) (0)))))) (PreH7 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l_) (0)) <> 0) -> (((Znth (w_6) (vis2_m_2) (0)) = 0) -> ((Znth (w_6) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m_2) (0))))))) (PreH8 : ((Znth v vis2_m_2 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH25 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH27 : forall (w_7: Z) , (((0 <= w_7) /\ (w_7 < n0_low_level_spec)) -> (((Znth (w_7) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_7) (vis2_m_2) (0)) <> 0)))) (PreH28 : forall (w_8: Z) , (((0 <= w_8) /\ (w_8 < n0_low_level_spec)) -> (((Znth (w_8) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_8) (sid_m_2) (0)) = (Znth (w_8) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_9: Z) , (((0 <= w_9) /\ (w_9 < n0_low_level_spec)) -> (((Znth (w_9) (vis2_m_2) (0)) <> 0) -> (((Znth (w_9) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_9) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_l_ )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_l_ )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z)) ,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u0_low_level_spec) ” 
  &&  “ (u0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < (i + 1 ))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ”
  &&  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
) \/
(
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_m_2) (0)) <> 0) -> ((Znth (w_4) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_m_2) (0)) <> 0) -> ((Znth (w_5) (sid_l_) (0)) = (Znth (w_5) (sid_m_2) (0)))))) (PreH7 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l_) (0)) <> 0) -> (((Znth (w_6) (vis2_m_2) (0)) = 0) -> ((Znth (w_6) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m_2) (0))))))) (PreH8 : ((Znth v vis2_m_2 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH25 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH27 : forall (w_7: Z) , (((0 <= w_7) /\ (w_7 < n0_low_level_spec)) -> (((Znth (w_7) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_7) (vis2_m_2) (0)) <> 0)))) (PreH28 : forall (w_8: Z) , (((0 <= w_8) /\ (w_8 < n0_low_level_spec)) -> (((Znth (w_8) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_8) (sid_m_2) (0)) = (Znth (w_8) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_9: Z) , (((0 <= w_9) /\ (w_9 < n0_low_level_spec)) -> (((Znth (w_9) (vis2_m_2) (0)) <> 0) -> (((Znth (w_9) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_9) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_l_) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_l_) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0))) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_l_) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < (i + 1 ))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_l_) (0)) <> 0)) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_) (0)) <> 0) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition dfs2_entail_wit_3_1_split_goal_1 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_m_2) (0)) <> 0) -> ((Znth (w_4) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_m_2) (0)) <> 0) -> ((Znth (w_5) (sid_l_) (0)) = (Znth (w_5) (sid_m_2) (0)))))) (PreH7 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l_) (0)) <> 0) -> (((Znth (w_6) (vis2_m_2) (0)) = 0) -> ((Znth (w_6) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m_2) (0))))))) (PreH8 : ((Znth v vis2_m_2 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH25 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH27 : forall (w_7: Z) , (((0 <= w_7) /\ (w_7 < n0_low_level_spec)) -> (((Znth (w_7) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_7) (vis2_m_2) (0)) <> 0)))) (PreH28 : forall (w_8: Z) , (((0 <= w_8) /\ (w_8 < n0_low_level_spec)) -> (((Znth (w_8) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_8) (sid_m_2) (0)) = (Znth (w_8) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_9: Z) , (((0 <= w_9) /\ (w_9 < n0_low_level_spec)) -> (((Znth (w_9) (vis2_m_2) (0)) <> 0) -> (((Znth (w_9) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_9) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_l_) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))
.

Definition dfs2_entail_wit_3_1_split_goal_2 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_m_2) (0)) <> 0) -> ((Znth (w_4) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_m_2) (0)) <> 0) -> ((Znth (w_5) (sid_l_) (0)) = (Znth (w_5) (sid_m_2) (0)))))) (PreH7 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l_) (0)) <> 0) -> (((Znth (w_6) (vis2_m_2) (0)) = 0) -> ((Znth (w_6) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m_2) (0))))))) (PreH8 : ((Znth v vis2_m_2 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH25 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH27 : forall (w_7: Z) , (((0 <= w_7) /\ (w_7 < n0_low_level_spec)) -> (((Znth (w_7) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_7) (vis2_m_2) (0)) <> 0)))) (PreH28 : forall (w_8: Z) , (((0 <= w_8) /\ (w_8 < n0_low_level_spec)) -> (((Znth (w_8) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_8) (sid_m_2) (0)) = (Znth (w_8) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_9: Z) , (((0 <= w_9) /\ (w_9 < n0_low_level_spec)) -> (((Znth (w_9) (vis2_m_2) (0)) <> 0) -> (((Znth (w_9) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_9) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_l_) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))
.

Definition dfs2_entail_wit_3_1_split_goal_3 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_m_2) (0)) <> 0) -> ((Znth (w_4) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_m_2) (0)) <> 0) -> ((Znth (w_5) (sid_l_) (0)) = (Znth (w_5) (sid_m_2) (0)))))) (PreH7 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l_) (0)) <> 0) -> (((Znth (w_6) (vis2_m_2) (0)) = 0) -> ((Znth (w_6) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m_2) (0))))))) (PreH8 : ((Znth v vis2_m_2 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH25 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH27 : forall (w_7: Z) , (((0 <= w_7) /\ (w_7 < n0_low_level_spec)) -> (((Znth (w_7) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_7) (vis2_m_2) (0)) <> 0)))) (PreH28 : forall (w_8: Z) , (((0 <= w_8) /\ (w_8 < n0_low_level_spec)) -> (((Znth (w_8) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_8) (sid_m_2) (0)) = (Znth (w_8) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_9: Z) , (((0 <= w_9) /\ (w_9 < n0_low_level_spec)) -> (((Znth (w_9) (vis2_m_2) (0)) <> 0) -> (((Znth (w_9) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_9) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0)))
.

Definition dfs2_entail_wit_3_1_split_goal_4 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_m_2) (0)) <> 0) -> ((Znth (w_4) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_m_2) (0)) <> 0) -> ((Znth (w_5) (sid_l_) (0)) = (Znth (w_5) (sid_m_2) (0)))))) (PreH7 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l_) (0)) <> 0) -> (((Znth (w_6) (vis2_m_2) (0)) = 0) -> ((Znth (w_6) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m_2) (0))))))) (PreH8 : ((Znth v vis2_m_2 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH25 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH27 : forall (w_7: Z) , (((0 <= w_7) /\ (w_7 < n0_low_level_spec)) -> (((Znth (w_7) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_7) (vis2_m_2) (0)) <> 0)))) (PreH28 : forall (w_8: Z) , (((0 <= w_8) /\ (w_8 < n0_low_level_spec)) -> (((Znth (w_8) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_8) (sid_m_2) (0)) = (Znth (w_8) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_9: Z) , (((0 <= w_9) /\ (w_9 < n0_low_level_spec)) -> (((Znth (w_9) (vis2_m_2) (0)) <> 0) -> (((Znth (w_9) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_9) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  ((Znth (root0_low_level_spec) (vis2_l_) (0)) <> 0)
.

Definition dfs2_entail_wit_3_1_split_goal_5 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_m_2) (0)) <> 0) -> ((Znth (w_4) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_m_2) (0)) <> 0) -> ((Znth (w_5) (sid_l_) (0)) = (Znth (w_5) (sid_m_2) (0)))))) (PreH7 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l_) (0)) <> 0) -> (((Znth (w_6) (vis2_m_2) (0)) = 0) -> ((Znth (w_6) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m_2) (0))))))) (PreH8 : ((Znth v vis2_m_2 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH25 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH27 : forall (w_7: Z) , (((0 <= w_7) /\ (w_7 < n0_low_level_spec)) -> (((Znth (w_7) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_7) (vis2_m_2) (0)) <> 0)))) (PreH28 : forall (w_8: Z) , (((0 <= w_8) /\ (w_8 < n0_low_level_spec)) -> (((Znth (w_8) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_8) (sid_m_2) (0)) = (Znth (w_8) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_9: Z) , (((0 <= w_9) /\ (w_9 < n0_low_level_spec)) -> (((Znth (w_9) (vis2_m_2) (0)) <> 0) -> (((Znth (w_9) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_9) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  forall (j: Z) , (((lo <= j) /\ (j < (i + 1 ))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_l_) (0)) <> 0))
.

Definition dfs2_entail_wit_3_1_split_goal_6 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_m_2) (0)) <> 0) -> ((Znth (w_4) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_m_2) (0)) <> 0) -> ((Znth (w_5) (sid_l_) (0)) = (Znth (w_5) (sid_m_2) (0)))))) (PreH7 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l_) (0)) <> 0) -> (((Znth (w_6) (vis2_m_2) (0)) = 0) -> ((Znth (w_6) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m_2) (0))))))) (PreH8 : ((Znth v vis2_m_2 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH25 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH27 : forall (w_7: Z) , (((0 <= w_7) /\ (w_7 < n0_low_level_spec)) -> (((Znth (w_7) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_7) (vis2_m_2) (0)) <> 0)))) (PreH28 : forall (w_8: Z) , (((0 <= w_8) /\ (w_8 < n0_low_level_spec)) -> (((Znth (w_8) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_8) (sid_m_2) (0)) = (Znth (w_8) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_9: Z) , (((0 <= w_9) /\ (w_9 < n0_low_level_spec)) -> (((Znth (w_9) (vis2_m_2) (0)) <> 0) -> (((Znth (w_9) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_9) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  ((Znth (u0_low_level_spec) (vis2_l_) (0)) <> 0)
.

Definition dfs2_entail_wit_3_1_split_goal_7 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_m_2) (0)) <> 0) -> ((Znth (w_4) (vis2_l_) (0)) <> 0)))) (PreH6 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_m_2) (0)) <> 0) -> ((Znth (w_5) (sid_l_) (0)) = (Znth (w_5) (sid_m_2) (0)))))) (PreH7 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l_) (0)) <> 0) -> (((Znth (w_6) (vis2_m_2) (0)) = 0) -> ((Znth (w_6) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_m_2) (0))))))) (PreH8 : ((Znth v vis2_m_2 0) = 0)) (PreH9 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH10 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH11 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH12 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH13 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH14 : (0 <= lo)) (PreH15 : (lo <= i)) (PreH16 : (i < hi)) (PreH17 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH18 : (0 <= u0_low_level_spec)) (PreH19 : (u0_low_level_spec < n0_low_level_spec)) (PreH20 : (0 <= root0_low_level_spec)) (PreH21 : (root0_low_level_spec < n0_low_level_spec)) (PreH22 : (n0_low_level_spec <= 2147483646)) (PreH23 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH25 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH26 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH27 : forall (w_7: Z) , (((0 <= w_7) /\ (w_7 < n0_low_level_spec)) -> (((Znth (w_7) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_7) (vis2_m_2) (0)) <> 0)))) (PreH28 : forall (w_8: Z) , (((0 <= w_8) /\ (w_8 < n0_low_level_spec)) -> (((Znth (w_8) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_8) (sid_m_2) (0)) = (Znth (w_8) (sid_l_low_level_spec) (0)))))) (PreH29 : forall (w_9: Z) , (((0 <= w_9) /\ (w_9 < n0_low_level_spec)) -> (((Znth (w_9) (vis2_m_2) (0)) <> 0) -> (((Znth (w_9) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_9) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH30 : (0 <= v)) (PreH31 : (v < n0_low_level_spec)) (PreH32 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))) X_low_level_spec )
.

Definition dfs2_entail_wit_3_2 := 
(
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m_2) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m_2) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m_2) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m_2 )
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m_2 )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z)) ,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u0_low_level_spec) ” 
  &&  “ (u0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < (i + 1 ))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ”
  &&  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
) \/
(
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m_2) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m_2) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m_2) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m_2) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m_2) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m_2) (0)) <> 0))) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < (i + 1 ))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0)) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition dfs2_entail_wit_3_2_split_goal_1 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m_2) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m_2) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m_2) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m_2) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))
.

Definition dfs2_entail_wit_3_2_split_goal_2 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m_2) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m_2) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m_2) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m_2) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))
.

Definition dfs2_entail_wit_3_2_split_goal_3 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m_2) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m_2) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m_2) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m_2) (0)) <> 0)))
.

Definition dfs2_entail_wit_3_2_split_goal_4 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m_2) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m_2) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m_2) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  forall (j: Z) , (((lo <= j) /\ (j < (i + 1 ))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))
.

Definition dfs2_entail_wit_3_2_split_goal_5 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH19 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m_2) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m_2) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m_2) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m_2) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m_2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))) X_low_level_spec )
.

Definition dfs2_return_wit_1 := 
(
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  EX (vis2_l_: (@list Z))  (sid_l_: (@list Z)) ,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (return (tt)) X_low_level_spec ) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_l_) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_l_) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_l_) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ”
  &&  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_l_ )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_l_ )
) \/
(
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  TT && emp 
|--
  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition dfs2_return_wit_1_split_goal_1 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))
.

Definition dfs2_return_wit_1_split_goal_2 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))
.

Definition dfs2_return_wit_1_split_goal_3 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))
.

Definition dfs2_return_wit_1_split_goal_4 := 
forall (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_m) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_m) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (return (tt)) X_low_level_spec )
.

Definition dfs2_partial_solve_wit_1 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ (u_pre = root_pre) ”
  &&  (((vis2_pre + (u_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i vis2_pre u_pre 0 n_pre vis2_l_low_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_2 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((vis2_pre + (u_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i vis2_pre u_pre 0 n_pre vis2_l_low_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_3 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ (u_pre = root_pre) ”
  &&  (((sid_pre + (root_pre * sizeof(INT)))) # Int  |-> (Znth root_pre sid_l_low_level_spec 0))
  **  (IntArray.missing_i sid_pre root_pre 0 n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_4 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ (u_pre = root_pre) ”
  &&  (((sid_pre + (u_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i sid_pre u_pre 0 n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_5 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((sid_pre + (root_pre * sizeof(INT)))) # Int  |-> (Znth root_pre sid_l_low_level_spec 0))
  **  (IntArray.missing_i sid_pre root_pre 0 n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_6 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((sid_pre + (u_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i sid_pre u_pre 0 n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_7 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ (u_pre = root_pre) ”
  &&  (((fadj_row_pre + (u_pre * sizeof(INT)))) # Int  |-> (Znth u_pre fadj_row_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_row_pre u_pre 0 (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_8 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((fadj_row_pre + (u_pre * sizeof(INT)))) # Int  |-> (Znth u_pre fadj_row_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_row_pre u_pre 0 (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_9 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : (u_pre = root_pre)) ,
  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ (u_pre = root_pre) ”
  &&  (((fadj_row_pre + ((u_pre + 1 ) * sizeof(INT)))) # Int  |-> (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_row_pre (u_pre + 1 ) 0 (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_10 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (root0_low_level_spec = root_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0)) (PreH12 : (n0_low_level_spec = n_pre)) (PreH13 : (u0_low_level_spec = u_pre)) (PreH14 : (fadj_col0_low_level_spec = fadj_col_pre)) (PreH15 : (fadj_row0_low_level_spec = fadj_row_pre)) (PreH16 : (vis20_low_level_spec = vis2_pre)) (PreH17 : (sid0_low_level_spec = sid_pre)) (PreH18 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((fadj_row_pre + ((u_pre + 1 ) * sizeof(INT)))) # Int  |-> (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_row_pre (u_pre + 1 ) 0 (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_11 := 
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) ,
  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ (i < hi) ” 
  &&  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u0_low_level_spec) ” 
  &&  “ (u0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ”
  &&  (((fadj_col0_low_level_spec + (i * sizeof(INT)))) # Int  |-> (Znth i fadj_col_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_col0_low_level_spec i 0 (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
.

Definition dfs2_partial_solve_wit_12 := 
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH11 : (0 <= u0_low_level_spec)) (PreH12 : (u0_low_level_spec < n0_low_level_spec)) (PreH13 : (0 <= root0_low_level_spec)) (PreH14 : (root0_low_level_spec < n0_low_level_spec)) (PreH15 : (n0_low_level_spec <= 2147483646)) (PreH16 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH20 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH21 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))) (PreH22 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH23 : (0 <= v)) (PreH24 : (v < n0_low_level_spec)) (PreH25 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u0_low_level_spec) ” 
  &&  “ (u0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n0_low_level_spec) ” 
  &&  “ (v = (Znth (i) (fadj_col_l_low_level_spec) (0))) ”
  &&  (((vis20_low_level_spec + (v * sizeof(INT)))) # Int  |-> (Znth v vis2_m 0))
  **  (IntArray.missing_i vis20_low_level_spec v 0 n0_low_level_spec vis2_m )
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
.

Definition dfs2_partial_solve_wit_13_pure := 
(
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m 0) = 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (root0_low_level_spec = root0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (v) (vis2_m) (0)) = 0) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (bind ((dfs_scc (g_low_level_spec) (root0_low_level_spec) (v))) ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))))) X_low_level_spec ) ”
) \/
(
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (root0_low_level_spec <= INT_MAX)) (PreH5 : (u0_low_level_spec <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n0_low_level_spec <= INT_MAX)) (PreH8 : (v >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (root0_low_level_spec >= INT_MIN)) (PreH12 : (u0_low_level_spec >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (n0_low_level_spec >= INT_MIN)) (PreH15 : ((Znth v vis2_m 0) = 0)) (PreH16 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH19 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH20 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH21 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH22 : (0 <= lo)) (PreH23 : (lo <= i)) (PreH24 : (i < hi)) (PreH25 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH26 : (0 <= u0_low_level_spec)) (PreH27 : (u0_low_level_spec < n0_low_level_spec)) (PreH28 : (0 <= root0_low_level_spec)) (PreH29 : (root0_low_level_spec < n0_low_level_spec)) (PreH30 : (n0_low_level_spec <= 2147483646)) (PreH31 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH32 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH33 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH34 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH35 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH36 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))) (PreH37 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH38 : (0 <= v)) (PreH39 : (v < n0_low_level_spec)) (PreH40 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (bind ((dfs_scc (g_low_level_spec) (root0_low_level_spec) (v))) ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))))) X_low_level_spec ) ”
).

Definition dfs2_partial_solve_wit_13_pure_split_goal_1 := 
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (root0_low_level_spec <= INT_MAX)) (PreH5 : (u0_low_level_spec <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n0_low_level_spec <= INT_MAX)) (PreH8 : (v >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (root0_low_level_spec >= INT_MIN)) (PreH12 : (u0_low_level_spec >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (n0_low_level_spec >= INT_MIN)) (PreH15 : ((Znth v vis2_m 0) = 0)) (PreH16 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH19 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH20 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH21 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH22 : (0 <= lo)) (PreH23 : (lo <= i)) (PreH24 : (i < hi)) (PreH25 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH26 : (0 <= u0_low_level_spec)) (PreH27 : (u0_low_level_spec < n0_low_level_spec)) (PreH28 : (0 <= root0_low_level_spec)) (PreH29 : (root0_low_level_spec < n0_low_level_spec)) (PreH30 : (n0_low_level_spec <= 2147483646)) (PreH31 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH32 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH33 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH34 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH35 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH36 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))) (PreH37 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH38 : (0 <= v)) (PreH39 : (v < n0_low_level_spec)) (PreH40 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n0_low_level_spec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u0_low_level_spec)
  **  ((( &( "root" ) )) # Int  |-> root0_low_level_spec)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col0_low_level_spec)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row0_low_level_spec)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis20_low_level_spec)
  **  ((( &( "sid" ) )) # Ptr  |-> sid0_low_level_spec)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (bind ((dfs_scc (g_low_level_spec) (root0_low_level_spec) (v))) ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))))) X_low_level_spec ) ”
.

Definition dfs2_partial_solve_wit_13_aux := 
forall (sid0_low_level_spec: Z) (vis20_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (u0_low_level_spec: Z) (n0_low_level_spec: Z) (root0_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m 0) = 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n0_low_level_spec)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u0_low_level_spec)) (PreH13 : (u0_low_level_spec < n0_low_level_spec)) (PreH14 : (0 <= root0_low_level_spec)) (PreH15 : (root0_low_level_spec < n0_low_level_spec)) (PreH16 : (n0_low_level_spec <= 2147483646)) (PreH17 : ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0)) (PreH18 : ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH19 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH20 : ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0)) (PreH21 : forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH22 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0)))))) (PreH23 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0))))))) (PreH24 : (0 <= v)) (PreH25 : (v < n0_low_level_spec)) (PreH26 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (root0_low_level_spec = root0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (v) (vis2_m) (0)) = 0) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (bind ((dfs_scc (g_low_level_spec) (root0_low_level_spec) (v))) ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) ((i + 1 ))))) X_low_level_spec ) ” 
  &&  “ ((Znth v vis2_m 0) = 0) ” 
  &&  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root0_low_level_spec) (u0_low_level_spec) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u0_low_level_spec) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u0_low_level_spec) ” 
  &&  “ (u0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (0 <= root0_low_level_spec) ” 
  &&  “ (root0_low_level_spec < n0_low_level_spec) ” 
  &&  “ (n0_low_level_spec <= 2147483646) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root0_low_level_spec) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_m) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_m) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_m) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n0_low_level_spec) ” 
  &&  “ (v = (Znth (i) (fadj_col_l_low_level_spec) (0))) ”
  &&  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_m )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_m )
.

Definition dfs2_partial_solve_wit_13 := dfs2_partial_solve_wit_13_pure -> dfs2_partial_solve_wit_13_aux.

Definition dfs2_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (f_bind_spec: (unit -> (@ MonadErr.M  KSt B))) (X_bind_spec: (B -> (KSt -> Prop))) (root0_bind_spec: Z) (root_v_bind_spec: Z) (sid_l_bind_spec: (@list Z)) (vis2_l_bind_spec: (@list Z)) (fadj_row_l_bind_spec: (@list Z)) (fadj_col_l_bind_spec: (@list Z)) (g_bind_spec: AdjGraph) ,
  “ (csr_wf2 g_bind_spec fadj_col_l_bind_spec fadj_row_l_bind_spec vis2_l_bind_spec sid_l_bind_spec ) ” 
  &&  “ (csr2_faithful g_bind_spec fadj_col_l_bind_spec fadj_row_l_bind_spec ) ” 
  &&  “ ((adj_verts (g_bind_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_bind_spec) (fadj_col_l_bind_spec) (fadj_row_l_bind_spec) (vis2_l_bind_spec) (sid_l_bind_spec) (root_v_bind_spec)) (bind ((dfs_scc (g_bind_spec) (root_pre) (u_pre))) (f_bind_spec)) X_bind_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_bind_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_bind_spec) (0)) = 0) ” 
  &&  “ ((Znth (root_pre) (vis2_l_bind_spec) (0)) <> 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_bind_spec)) fadj_col_l_bind_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_bind_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_bind_spec )
  **  (IntArray.full sid_pre n_pre sid_l_bind_spec )
|--
EX (g_low_level_spec: AdjGraph) (fadj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (sid_l_low_level_spec: (@list Z)) (root_v_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root0_low_level_spec: Z) (n0_low_level_spec: Z) (u0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (vis20_low_level_spec: Z) (sid0_low_level_spec: Z) ,
  ((“ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ (u_pre = root_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec ))
  ||
  (“ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )))
  **
  ((EX vis2_l__2 sid_l__2,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l__2 sid_l__2 ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l__2) (sid_l__2) (root_v_low_level_spec)) (return (tt)) X_low_level_spec ) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l__2) (0)) <> 0) ” 
  &&  “ forall (w_4: Z) , (((0 <= w_4) /\ (w_4 < n0_low_level_spec)) -> (((Znth (w_4) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_4) (vis2_l__2) (0)) <> 0))) ” 
  &&  “ forall (w_5: Z) , (((0 <= w_5) /\ (w_5 < n0_low_level_spec)) -> (((Znth (w_5) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_5) (sid_l__2) (0)) = (Znth (w_5) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_6: Z) , (((0 <= w_6) /\ (w_6 < n0_low_level_spec)) -> (((Znth (w_6) (vis2_l__2) (0)) <> 0) -> (((Znth (w_6) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_6) (sid_l__2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ”
  &&  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_l__2 )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_l__2 ))
  -*
  (EX vis2_l_ sid_l_,
  “ (csr_wf2 g_bind_spec fadj_col_l_bind_spec fadj_row_l_bind_spec vis2_l_ sid_l_ ) ” 
  &&  “ ((adj_verts (g_bind_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_bind_spec) (fadj_col_l_bind_spec) (fadj_row_l_bind_spec) (vis2_l_) (sid_l_) (root_v_bind_spec)) (applyf (f_bind_spec) (tt)) X_bind_spec ) ” 
  &&  “ ((Znth (u_pre) (vis2_l_) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_bind_spec) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_bind_spec) (0)) <> 0) -> ((Znth (w_2) (sid_l_) (0)) = (Znth (w_2) (sid_l_bind_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) (vis2_l_) (0)) <> 0) -> (((Znth (w_3) (vis2_l_bind_spec) (0)) = 0) -> ((Znth (w_3) (sid_l_) (0)) = (Znth (root0_bind_spec) (sid_l_bind_spec) (0)))))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_bind_spec)) fadj_col_l_bind_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_bind_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )))
.

Definition dfs2_derive_phase2_spec_by_low_level_spec := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (k_phase2_spec: Z) (timer_v_phase2_spec: Z) (order_l_phase2_spec: (@list Z)) (fin_l_phase2_spec: (@list Z)) (sid_l_phase2_spec: (@list Z)) (sid_before_l_phase2_spec: (@list Z)) (vis2_l_phase2_spec: (@list Z)) (vis1_l_phase2_spec: (@list Z)) (fadj_row_l_phase2_spec: (@list Z)) (fadj_col_l_phase2_spec: (@list Z)) (g_phase2_spec: AdjGraph) ,
  “ (csr_wf2 g_phase2_spec fadj_col_l_phase2_spec fadj_row_l_phase2_spec vis2_l_phase2_spec sid_l_phase2_spec ) ” 
  &&  “ (csr2_faithful g_phase2_spec fadj_col_l_phase2_spec fadj_row_l_phase2_spec ) ” 
  &&  “ (AdjGraphValid g_phase2_spec ) ” 
  &&  “ ((adj_verts (g_phase2_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_phase2_spec fadj_col_l_phase2_spec fadj_row_l_phase2_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_phase2_spec)) = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k_phase2_spec) ” 
  &&  “ (k_phase2_spec < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (u_pre = root_pre) ” 
  &&  “ (root_pre = (Znth (k_phase2_spec) (order_l_phase2_spec) (0))) ” 
  &&  “ ((Znth (u_pre) (vis2_l_phase2_spec) (0)) = 0) ” 
  &&  “ ((Znth (root_pre) (vis2_l_phase2_spec) (0)) = 0) ” 
  &&  “ ((Znth (root_pre) (sid_l_phase2_spec) (0)) = root_pre) ” 
  &&  “ (sid_l_phase2_spec = (replace_Znth (root_pre) (root_pre) (sid_before_l_phase2_spec))) ” 
  &&  “ (phase2_sequence_residual_refinement g_phase2_spec fin_l_phase2_spec order_l_phase2_spec vis1_l_phase2_spec vis2_l_phase2_spec sid_before_l_phase2_spec timer_v_phase2_spec n_pre k_phase2_spec ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_phase2_spec)) fadj_col_l_phase2_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_phase2_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_phase2_spec )
  **  (IntArray.full sid_pre n_pre sid_l_phase2_spec )
|--
EX (g_low_level_spec: AdjGraph) (fadj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (sid_l_low_level_spec: (@list Z)) (root_v_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root0_low_level_spec: Z) (n0_low_level_spec: Z) (u0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (vis20_low_level_spec: Z) (sid0_low_level_spec: Z) ,
  ((“ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ (u_pre = root_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec ))
  ||
  (“ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )))
  **
  ((EX vis2_l__2 sid_l__2,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l__2 sid_l__2 ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l__2) (sid_l__2) (root_v_low_level_spec)) (return (tt)) X_low_level_spec ) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l__2) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_l__2) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_l__2) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_l__2) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_l__2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ”
  &&  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_l__2 )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_l__2 ))
  -*
  (EX vis2_l_ sid_l_,
  “ (dfs2_high_level_post g_phase2_spec fadj_col_l_phase2_spec fadj_row_l_phase2_spec vis2_l_phase2_spec sid_l_phase2_spec vis2_l_ sid_l_ root_pre root_pre n_pre ) ” 
  &&  “ (dfs2_phase2_post g_phase2_spec n_pre vis2_l_phase2_spec sid_l_phase2_spec vis2_l_ sid_l_ root_pre ) ” 
  &&  “ (phase2_sequence_residual_refinement g_phase2_spec fin_l_phase2_spec order_l_phase2_spec vis1_l_phase2_spec vis2_l_ sid_l_ timer_v_phase2_spec n_pre (k_phase2_spec + 1 ) ) ” 
  &&  “ (csr_wf2 g_phase2_spec fadj_col_l_phase2_spec fadj_row_l_phase2_spec vis2_l_ sid_l_ ) ” 
  &&  “ (csr2_faithful g_phase2_spec fadj_col_l_phase2_spec fadj_row_l_phase2_spec ) ” 
  &&  “ (AdjGraphValid g_phase2_spec ) ” 
  &&  “ ((adj_verts (g_phase2_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_phase2_spec fadj_col_l_phase2_spec fadj_row_l_phase2_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_phase2_spec)) = 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_phase2_spec)) fadj_col_l_phase2_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_phase2_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )))
.

Definition dfs2_derive_high_level_spec_by_low_level_spec := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (sid_l_high_level_spec: (@list Z)) (vis2_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) ,
  (“ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_l_high_level_spec sid_l_high_level_spec ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_high_level_spec) (0)) = 0) ” 
  &&  “ (u_pre = root_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec ))
  ||
  (“ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_l_high_level_spec sid_l_high_level_spec ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_high_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (root_pre) (vis2_l_high_level_spec) (0)) <> 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec ))
|--
EX (g_low_level_spec: AdjGraph) (fadj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (sid_l_low_level_spec: (@list Z)) (root_v_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root0_low_level_spec: Z) (n0_low_level_spec: Z) (u0_low_level_spec: Z) (fadj_col0_low_level_spec: Z) (fadj_row0_low_level_spec: Z) (vis20_low_level_spec: Z) (sid0_low_level_spec: Z) ,
  ((“ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ (u_pre = root_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec ))
  ||
  (“ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (root0_low_level_spec = root_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis2_l_low_level_spec) (0)) = 0) ” 
  &&  “ (n0_low_level_spec = n_pre) ” 
  &&  “ (u0_low_level_spec = u_pre) ” 
  &&  “ (fadj_col0_low_level_spec = fadj_col_pre) ” 
  &&  “ (fadj_row0_low_level_spec = fadj_row_pre) ” 
  &&  “ (vis20_low_level_spec = vis2_pre) ” 
  &&  “ (sid0_low_level_spec = sid_pre) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )))
  **
  ((EX vis2_l__2 sid_l__2,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l__2 sid_l__2 ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n0_low_level_spec) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l__2) (sid_l__2) (root_v_low_level_spec)) (return (tt)) X_low_level_spec ) ” 
  &&  “ ((Znth (u0_low_level_spec) (vis2_l__2) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n0_low_level_spec)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_l__2) (0)) <> 0))) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n0_low_level_spec)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (sid_l__2) (0)) = (Znth (w_2) (sid_l_low_level_spec) (0))))) ” 
  &&  “ forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n0_low_level_spec)) -> (((Znth (w_3) (vis2_l__2) (0)) <> 0) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) = 0) -> ((Znth (w_3) (sid_l__2) (0)) = (Znth (root0_low_level_spec) (sid_l_low_level_spec) (0)))))) ”
  &&  (IntArray.full fadj_col0_low_level_spec (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row0_low_level_spec (n0_low_level_spec + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis20_low_level_spec n0_low_level_spec vis2_l__2 )
  **  (IntArray.full sid0_low_level_spec n0_low_level_spec sid_l__2 ))
  -*
  (EX vis2_l_ sid_l_,
  “ (dfs2_high_level_post g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_l_high_level_spec sid_l_high_level_spec vis2_l_ sid_l_ root_pre u_pre n_pre ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.

Axiom proof_of_dfs2_safety_wit_1 : dfs2_safety_wit_1.
Axiom proof_of_dfs2_safety_wit_2 : dfs2_safety_wit_2.
Axiom proof_of_dfs2_safety_wit_3 : dfs2_safety_wit_3.
Axiom proof_of_dfs2_safety_wit_4 : dfs2_safety_wit_4.
Axiom proof_of_dfs2_safety_wit_5 : dfs2_safety_wit_5.
Axiom proof_of_dfs2_safety_wit_6 : dfs2_safety_wit_6.
Axiom proof_of_dfs2_safety_wit_7 : dfs2_safety_wit_7.
Axiom proof_of_dfs2_safety_wit_8 : dfs2_safety_wit_8.
Axiom proof_of_dfs2_safety_wit_9 : dfs2_safety_wit_9.
Axiom proof_of_dfs2_safety_wit_10 : dfs2_safety_wit_10.
Axiom proof_of_dfs2_safety_wit_11 : dfs2_safety_wit_11.
Axiom proof_of_dfs2_entail_wit_1_1 : dfs2_entail_wit_1_1.
Axiom proof_of_dfs2_entail_wit_1_2 : dfs2_entail_wit_1_2.
Axiom proof_of_dfs2_entail_wit_2 : dfs2_entail_wit_2.
Axiom proof_of_dfs2_entail_wit_3_1 : dfs2_entail_wit_3_1.
Axiom proof_of_dfs2_entail_wit_3_2 : dfs2_entail_wit_3_2.
Axiom proof_of_dfs2_return_wit_1 : dfs2_return_wit_1.
Axiom proof_of_dfs2_partial_solve_wit_1 : dfs2_partial_solve_wit_1.
Axiom proof_of_dfs2_partial_solve_wit_2 : dfs2_partial_solve_wit_2.
Axiom proof_of_dfs2_partial_solve_wit_3 : dfs2_partial_solve_wit_3.
Axiom proof_of_dfs2_partial_solve_wit_4 : dfs2_partial_solve_wit_4.
Axiom proof_of_dfs2_partial_solve_wit_5 : dfs2_partial_solve_wit_5.
Axiom proof_of_dfs2_partial_solve_wit_6 : dfs2_partial_solve_wit_6.
Axiom proof_of_dfs2_partial_solve_wit_7 : dfs2_partial_solve_wit_7.
Axiom proof_of_dfs2_partial_solve_wit_8 : dfs2_partial_solve_wit_8.
Axiom proof_of_dfs2_partial_solve_wit_9 : dfs2_partial_solve_wit_9.
Axiom proof_of_dfs2_partial_solve_wit_10 : dfs2_partial_solve_wit_10.
Axiom proof_of_dfs2_partial_solve_wit_11 : dfs2_partial_solve_wit_11.
Axiom proof_of_dfs2_partial_solve_wit_12 : dfs2_partial_solve_wit_12.
Axiom proof_of_dfs2_partial_solve_wit_13_pure : dfs2_partial_solve_wit_13_pure.
Axiom proof_of_dfs2_partial_solve_wit_13 : dfs2_partial_solve_wit_13.
Axiom proof_of_dfs2_derive_bind_spec_by_low_level_spec : dfs2_derive_bind_spec_by_low_level_spec.
Axiom proof_of_dfs2_derive_phase2_spec_by_low_level_spec : dfs2_derive_phase2_spec_by_low_level_spec.
Axiom proof_of_dfs2_derive_high_level_spec_by_low_level_spec : dfs2_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
