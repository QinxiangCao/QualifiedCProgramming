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
Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.dfs1_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import safeexecE_strategy_goal.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import safeexecE_strategy_proof.

(*----- Function dfs1 -----*)

Definition dfs1_safety_wit_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_safety_wit_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre radj_row_l_low_level_spec 0))
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
|--
  “ ((u_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u_pre + 1 )) ”
.

Definition dfs1_safety_wit_3 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre radj_row_l_low_level_spec 0))
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_safety_wit_4 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH5 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH6 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH7 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH8 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH9 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= i)) (PreH12 : (i < hi)) (PreH13 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH14 : (0 <= u_pre)) (PreH15 : (u_pre < n_pre)) (PreH16 : (n_pre <= 2147483646)) (PreH17 : (0 <= timer_m)) (PreH18 : (timer_m <= (count_nonzero (vis1_m)))) (PreH19 : (timer_m < n_pre)) (PreH20 : (timer_v_low_level_spec <= timer_m)) (PreH21 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH22 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH23 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH24 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH25 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH26 : (0 <= v)) (PreH27 : (v < n_pre)) (PreH28 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs1_safety_wit_5 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m fin_m timer_m vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m vis1_l_ timer_m timer_v_ )) (PreH11 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_m) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH17 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m)) (PreH29 : (timer_m <= (count_nonzero (vis1_m)))) (PreH30 : (timer_m < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m)) (PreH32 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH35 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  ((timer_p_pre) # Int  |-> timer_v_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dfs1_safety_wit_6 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m fin_m timer_m vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m vis1_l_ timer_m timer_v_ )) (PreH11 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_m) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH17 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m)) (PreH29 : (timer_m <= (count_nonzero (vis1_m)))) (PreH30 : (timer_m < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m)) (PreH32 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH35 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  ((timer_p_pre) # Int  |-> timer_v_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_safety_wit_7 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH27 : (0 <= v)) (PreH28 : (v < n_pre)) (PreH29 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dfs1_safety_wit_8 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH27 : (0 <= v)) (PreH28 : (v < n_pre)) (PreH29 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_safety_wit_9 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (timer_m) (u_pre) (fin_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ ((timer_m + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (timer_m + 1 )) ”
.

Definition dfs1_safety_wit_10 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (timer_m) (u_pre) (fin_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_entail_wit_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
|--
  EX (timer_m: Z)  (vis1_m: (@list Z))  (fin_m: (@list Z)) ,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((Znth u_pre radj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= (Znth u_pre radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) <= (Znth u_pre radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (timer_v_low_level_spec <= timer_m) ” 
  &&  “ ((timer_m + 1 ) <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u_pre) (vis1_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ” 
  &&  “ (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m ) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  TT && emp 
|--
  “ (dfs1_active_timer_surplus vis1_l_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) timer_v_low_level_spec timer_v_low_level_spec ) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))) (0)) <> 0)) ” 
  &&  “ ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))) (0)) <> 0) ” 
  &&  “ ((timer_v_low_level_spec + 1 ) <= (count_nonzero ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))))) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))))) ” 
  &&  “ ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) radj_row_l_low_level_spec 0)) ” 
  &&  “ (0 <= (Znth u_pre radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((Znth u_pre radj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) fin_l_low_level_spec timer_v_low_level_spec u_pre ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) timer_v_low_level_spec n_pre ) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) fin_l_low_level_spec timer_v_low_level_spec ) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) fin_l_low_level_spec ) ”
  &&  emp
).

Definition dfs1_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (dfs1_active_timer_surplus vis1_l_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) timer_v_low_level_spec timer_v_low_level_spec )
.

Definition dfs1_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))) (0)) <> 0))
.

Definition dfs1_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))) (0)) <> 0)
.

Definition dfs1_entail_wit_1_split_goal_4 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  ((timer_v_low_level_spec + 1 ) <= (count_nonzero ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec)))))
.

Definition dfs1_entail_wit_1_split_goal_5 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (timer_v_low_level_spec <= (count_nonzero ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec)))))
.

Definition dfs1_entail_wit_1_split_goal_6 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) <= (m_of (radj_row_l_low_level_spec)))
.

Definition dfs1_entail_wit_1_split_goal_7 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  ((Znth u_pre radj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) radj_row_l_low_level_spec 0))
.

Definition dfs1_entail_wit_1_split_goal_8 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (0 <= (Znth u_pre radj_row_l_low_level_spec 0))
.

Definition dfs1_entail_wit_1_split_goal_9 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) = (csr_hi (u_pre) (radj_row_l_low_level_spec)))
.

Definition dfs1_entail_wit_1_split_goal_10 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  ((Znth u_pre radj_row_l_low_level_spec 0) = (csr_lo (u_pre) (radj_row_l_low_level_spec)))
.

Definition dfs1_entail_wit_1_split_goal_11 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((Znth u_pre radj_row_l_low_level_spec 0))) X_low_level_spec )
.

Definition dfs1_entail_wit_1_split_goal_12 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) fin_l_low_level_spec timer_v_low_level_spec u_pre )
.

Definition dfs1_entail_wit_1_split_goal_13 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (dfs1_finish_prefix_marked fin_l_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) timer_v_low_level_spec n_pre )
.

Definition dfs1_entail_wit_1_split_goal_14 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) fin_l_low_level_spec timer_v_low_level_spec )
.

Definition dfs1_entail_wit_1_split_goal_15 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) fin_l_low_level_spec )
.

Definition dfs1_entail_wit_2 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (timer_v_low_level_spec <= timer_m) ” 
  &&  “ ((timer_m + 1 ) <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u_pre) (vis1_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ” 
  &&  “ (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m ) ” 
  &&  “ (0 <= (Znth i radj_col_l_low_level_spec 0)) ” 
  &&  “ ((Znth i radj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ ((Znth i radj_col_l_low_level_spec 0) = (Znth (i) (radj_col_l_low_level_spec) (0))) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  TT && emp 
|--
  “ ((Znth i radj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ (0 <= (Znth i radj_col_l_low_level_spec 0)) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ”
  &&  emp
).

Definition dfs1_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  ((Znth i radj_col_l_low_level_spec 0) < n_pre)
.

Definition dfs1_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (0 <= (Znth i radj_col_l_low_level_spec 0))
.

Definition dfs1_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))
.

Definition dfs1_entail_wit_3_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m_2 fin_m_2 timer_m_2 vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m_2 <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m_2 vis1_l_ timer_m_2 timer_v_ )) (PreH11 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_m_2) (0)) <> 0)) -> ((Znth (w_2) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m_2 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH17 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m_2)) (PreH29 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH30 : (timer_m_2 < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m_2)) (PreH32 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH35 : forall (w_3: Z) , ((((0 <= w_3) /\ (w_3 < n_pre)) /\ ((Znth (w_3) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_3) (vis1_m_2) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  ((timer_p_pre) # Int  |-> timer_v_)
|--
  EX (timer_m: Z)  (vis1_m: (@list Z))  (fin_m: (@list Z)) ,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (timer_v_low_level_spec <= timer_m) ” 
  &&  “ ((timer_m + 1 ) <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u_pre) (vis1_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ” 
  &&  “ (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m ) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m_2 fin_m_2 timer_m_2 vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m_2 <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m_2 vis1_l_ timer_m_2 timer_v_ )) (PreH11 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_m_2) (0)) <> 0)) -> ((Znth (w_2) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m_2 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH17 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m_2)) (PreH29 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH30 : (timer_m_2 < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m_2)) (PreH32 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH35 : forall (w_3: Z) , ((((0 <= w_3) /\ (w_3 < n_pre)) /\ ((Znth (w_3) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_3) (vis1_m_2) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_l_ timer_v_low_level_spec timer_v_ ) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0)) ” 
  &&  “ ((Znth (u_pre) (vis1_l_) (0)) <> 0) ” 
  &&  “ ((timer_v_ + 1 ) <= (count_nonzero (vis1_l_))) ” 
  &&  “ (timer_v_ < n_pre) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_l_ fin_l_ timer_v_ u_pre ) ”
  &&  emp
).

Definition dfs1_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m_2 fin_m_2 timer_m_2 vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m_2 <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m_2 vis1_l_ timer_m_2 timer_v_ )) (PreH11 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_m_2) (0)) <> 0)) -> ((Znth (w_2) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m_2 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH17 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m_2)) (PreH29 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH30 : (timer_m_2 < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m_2)) (PreH32 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH35 : forall (w_3: Z) , ((((0 <= w_3) /\ (w_3 < n_pre)) /\ ((Znth (w_3) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_3) (vis1_m_2) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_l_ timer_v_low_level_spec timer_v_ )
.

Definition dfs1_entail_wit_3_1_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m_2 fin_m_2 timer_m_2 vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m_2 <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m_2 vis1_l_ timer_m_2 timer_v_ )) (PreH11 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_m_2) (0)) <> 0)) -> ((Znth (w_2) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m_2 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH17 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m_2)) (PreH29 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH30 : (timer_m_2 < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m_2)) (PreH32 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH35 : forall (w_3: Z) , ((((0 <= w_3) /\ (w_3 < n_pre)) /\ ((Znth (w_3) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_3) (vis1_m_2) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0))
.

Definition dfs1_entail_wit_3_1_split_goal_3 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m_2 fin_m_2 timer_m_2 vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m_2 <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m_2 vis1_l_ timer_m_2 timer_v_ )) (PreH11 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_m_2) (0)) <> 0)) -> ((Znth (w_2) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m_2 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH17 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m_2)) (PreH29 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH30 : (timer_m_2 < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m_2)) (PreH32 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH35 : forall (w_3: Z) , ((((0 <= w_3) /\ (w_3 < n_pre)) /\ ((Znth (w_3) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_3) (vis1_m_2) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  ((Znth (u_pre) (vis1_l_) (0)) <> 0)
.

Definition dfs1_entail_wit_3_1_split_goal_4 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m_2 fin_m_2 timer_m_2 vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m_2 <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m_2 vis1_l_ timer_m_2 timer_v_ )) (PreH11 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_m_2) (0)) <> 0)) -> ((Znth (w_2) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m_2 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH17 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m_2)) (PreH29 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH30 : (timer_m_2 < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m_2)) (PreH32 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH35 : forall (w_3: Z) , ((((0 <= w_3) /\ (w_3 < n_pre)) /\ ((Znth (w_3) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_3) (vis1_m_2) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  ((timer_v_ + 1 ) <= (count_nonzero (vis1_l_)))
.

Definition dfs1_entail_wit_3_1_split_goal_5 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m_2 fin_m_2 timer_m_2 vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m_2 <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m_2 vis1_l_ timer_m_2 timer_v_ )) (PreH11 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_m_2) (0)) <> 0)) -> ((Znth (w_2) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m_2 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH17 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m_2)) (PreH29 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH30 : (timer_m_2 < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m_2)) (PreH32 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH35 : forall (w_3: Z) , ((((0 <= w_3) /\ (w_3 < n_pre)) /\ ((Znth (w_3) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_3) (vis1_m_2) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (timer_v_ < n_pre)
.

Definition dfs1_entail_wit_3_1_split_goal_6 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m_2 fin_m_2 timer_m_2 vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m_2 <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m_2 vis1_l_ timer_m_2 timer_v_ )) (PreH11 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_m_2) (0)) <> 0)) -> ((Znth (w_2) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m_2 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH17 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m_2)) (PreH29 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH30 : (timer_m_2 < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m_2)) (PreH32 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH35 : forall (w_3: Z) , ((((0 <= w_3) /\ (w_3 < n_pre)) /\ ((Znth (w_3) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_3) (vis1_m_2) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec )
.

Definition dfs1_entail_wit_3_1_split_goal_7 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_low_level_spec vis1_m_2 fin_m_2 timer_m_2 vis1_l_ fin_l_ timer_v_ v )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer_m_2 <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m_2 vis1_l_ timer_m_2 timer_v_ )) (PreH11 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_m_2) (0)) <> 0)) -> ((Znth (w_2) (vis1_l_) (0)) <> 0))) (PreH12 : ((Znth v vis1_m_2 0) = 0)) (PreH13 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH14 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH17 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH18 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH19 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH20 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= i)) (PreH23 : (i < hi)) (PreH24 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH25 : (0 <= u_pre)) (PreH26 : (u_pre < n_pre)) (PreH27 : (n_pre <= 2147483646)) (PreH28 : (0 <= timer_m_2)) (PreH29 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH30 : (timer_m_2 < n_pre)) (PreH31 : (timer_v_low_level_spec <= timer_m_2)) (PreH32 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH33 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH34 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH35 : forall (w_3: Z) , ((((0 <= w_3) /\ (w_3 < n_pre)) /\ ((Znth (w_3) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_3) (vis1_m_2) (0)) <> 0))) (PreH36 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH37 : (0 <= v)) (PreH38 : (v < n_pre)) (PreH39 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_l_ fin_l_ timer_v_ u_pre )
.

Definition dfs1_entail_wit_3_2 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m_2 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH6 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m_2)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m_2)) (PreH19 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH20 : (timer_m_2 < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m_2)) (PreH22 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m_2) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH27 : (0 <= v)) (PreH28 : (v < n_pre)) (PreH29 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m_2 )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m_2 )
  **  ((timer_p_pre) # Int  |-> timer_m_2)
|--
  EX (timer_m: Z)  (vis1_m: (@list Z))  (fin_m: (@list Z)) ,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (timer_v_low_level_spec <= timer_m) ” 
  &&  “ ((timer_m + 1 ) <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u_pre) (vis1_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ” 
  &&  “ (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m ) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m_2 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH6 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m_2)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m_2)) (PreH19 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH20 : (timer_m_2 < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m_2)) (PreH22 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m_2) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH27 : (0 <= v)) (PreH28 : (v < n_pre)) (PreH29 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m_2) (0)) <> 0)) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m_2)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition dfs1_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m_2 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH6 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m_2)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m_2)) (PreH19 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH20 : (timer_m_2 < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m_2)) (PreH22 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m_2) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH27 : (0 <= v)) (PreH28 : (v < n_pre)) (PreH29 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m_2) (0)) <> 0))
.

Definition dfs1_entail_wit_3_2_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m_2 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 timer_m_2 )) (PreH6 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer_m_2 n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m_2 fin_m_2 timer_m_2 u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m_2)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m_2)) (PreH19 : (timer_m_2 <= (count_nonzero (vis1_m_2)))) (PreH20 : (timer_m_2 < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m_2)) (PreH22 : ((timer_m_2 + 1 ) <= (count_nonzero (vis1_m_2)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m_2) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m_2) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m_2 timer_v_low_level_spec timer_m_2 )) (PreH27 : (0 <= v)) (PreH28 : (v < n_pre)) (PreH29 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m_2)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec )
.

Definition dfs1_return_wit_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (timer_m) (u_pre) (fin_m)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((timer_p_pre) # Int  |-> (timer_m + 1 ))
|--
  EX (timer_v_: Z)  (vis1_l_: (@list Z))  (fin_l_: (@list Z)) ,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ timer_v_ ) ” 
  &&  “ (dfs1_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_l_ fin_l_ timer_v_ u_pre ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (0 <= timer_v_) ” 
  &&  “ (timer_v_ <= (count_nonzero (vis1_l_))) ” 
  &&  “ (timer_v_low_level_spec <= timer_v_) ” 
  &&  “ (dfs1_timer_surplus_preserved vis1_l_low_level_spec vis1_l_ timer_v_low_level_spec timer_v_ ) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0)) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  ((timer_p_pre) # Int  |-> timer_v_)
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  TT && emp 
|--
  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ” 
  &&  “ (dfs1_timer_surplus_preserved vis1_l_low_level_spec vis1_m timer_v_low_level_spec (timer_m + 1 ) ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) ((replace_Znth (timer_m) (u_pre) (fin_m))) ((timer_m + 1 ))) (return (tt)) X_low_level_spec ) ” 
  &&  “ (dfs1_finish_prefix_marked (replace_Znth (timer_m) (u_pre) (fin_m)) vis1_m (timer_m + 1 ) n_pre ) ” 
  &&  “ (dfs1_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m (replace_Znth (timer_m) (u_pre) (fin_m)) (timer_m + 1 ) u_pre ) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m (replace_Znth (timer_m) (u_pre) (fin_m)) (timer_m + 1 ) ) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m (replace_Znth (timer_m) (u_pre) (fin_m)) ) ”
  &&  emp
).

Definition dfs1_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))
.

Definition dfs1_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (dfs1_timer_surplus_preserved vis1_l_low_level_spec vis1_m timer_v_low_level_spec (timer_m + 1 ) )
.

Definition dfs1_return_wit_1_split_goal_3 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) ((replace_Znth (timer_m) (u_pre) (fin_m))) ((timer_m + 1 ))) (return (tt)) X_low_level_spec )
.

Definition dfs1_return_wit_1_split_goal_4 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (dfs1_finish_prefix_marked (replace_Znth (timer_m) (u_pre) (fin_m)) vis1_m (timer_m + 1 ) n_pre )
.

Definition dfs1_return_wit_1_split_goal_5 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (dfs1_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m (replace_Znth (timer_m) (u_pre) (fin_m)) (timer_m + 1 ) u_pre )
.

Definition dfs1_return_wit_1_split_goal_6 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m (replace_Znth (timer_m) (u_pre) (fin_m)) (timer_m + 1 ) )
.

Definition dfs1_return_wit_1_split_goal_7 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m (replace_Znth (timer_m) (u_pre) (fin_m)) )
.

Definition dfs1_partial_solve_wit_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_low_level_spec) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec))) ” 
  &&  “ (timer_v_low_level_spec < n_pre) ”
  &&  (((vis1_pre + (u_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i vis1_pre u_pre 0 n_pre vis1_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
.

Definition dfs1_partial_solve_wit_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_low_level_spec) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec))) ” 
  &&  “ (timer_v_low_level_spec < n_pre) ”
  &&  (((radj_row_pre + (u_pre * sizeof(INT)))) # Int  |-> (Znth u_pre radj_row_l_low_level_spec 0))
  **  (IntArray.missing_i radj_row_pre u_pre 0 (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
.

Definition dfs1_partial_solve_wit_3 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec )) (PreH5 : (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH7 : (0 <= u_pre)) (PreH8 : (u_pre < n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH11 : (0 <= timer_v_low_level_spec)) (PreH12 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) (PreH13 : (timer_v_low_level_spec < n_pre)) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_low_level_spec) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec))) ” 
  &&  “ (timer_v_low_level_spec < n_pre) ”
  &&  (((radj_row_pre + ((u_pre + 1 ) * sizeof(INT)))) # Int  |-> (Znth (u_pre + 1 ) radj_row_l_low_level_spec 0))
  **  (IntArray.missing_i radj_row_pre (u_pre + 1 ) 0 (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec)
.

Definition dfs1_partial_solve_wit_4 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (i < hi) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (timer_v_low_level_spec <= timer_m) ” 
  &&  “ ((timer_m + 1 ) <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u_pre) (vis1_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ” 
  &&  “ (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m ) ”
  &&  (((radj_col_pre + (i * sizeof(INT)))) # Int  |-> (Znth i radj_col_l_low_level_spec 0))
  **  (IntArray.missing_i radj_col_pre i 0 (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
.

Definition dfs1_partial_solve_wit_5 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH2 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH5 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH6 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH7 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH8 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH9 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= i)) (PreH12 : (i < hi)) (PreH13 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH14 : (0 <= u_pre)) (PreH15 : (u_pre < n_pre)) (PreH16 : (n_pre <= 2147483646)) (PreH17 : (0 <= timer_m)) (PreH18 : (timer_m <= (count_nonzero (vis1_m)))) (PreH19 : (timer_m < n_pre)) (PreH20 : (timer_v_low_level_spec <= timer_m)) (PreH21 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH22 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH23 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH24 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH25 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH26 : (0 <= v)) (PreH27 : (v < n_pre)) (PreH28 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (timer_v_low_level_spec <= timer_m) ” 
  &&  “ ((timer_m + 1 ) <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u_pre) (vis1_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ” 
  &&  “ (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m ) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (i) (radj_col_l_low_level_spec) (0))) ”
  &&  (((vis1_pre + (v * sizeof(INT)))) # Int  |-> (Znth v vis1_m 0))
  **  (IntArray.missing_i vis1_pre v 0 n_pre vis1_m )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
.

Definition dfs1_partial_solve_wit_6_pure := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m 0) = 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH27 : (0 <= v)) (PreH28 : (v < n_pre)) (PreH29 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (v) (vis1_m) (0)) = 0) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (bind ((dfs_finish (g_low_level_spec) (v))) ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))))) X_low_level_spec ) ”
) \/
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (timer_m <= INT_MAX)) (PreH2 : (v <= INT_MAX)) (PreH3 : (hi <= INT_MAX)) (PreH4 : (lo <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (u_pre <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (timer_m >= INT_MIN)) (PreH9 : (v >= INT_MIN)) (PreH10 : (hi >= INT_MIN)) (PreH11 : (lo >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (u_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((Znth v vis1_m 0) = 0)) (PreH16 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH17 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH20 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH21 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH22 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH23 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH24 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= i)) (PreH27 : (i < hi)) (PreH28 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH29 : (0 <= u_pre)) (PreH30 : (u_pre < n_pre)) (PreH31 : (n_pre <= 2147483646)) (PreH32 : (0 <= timer_m)) (PreH33 : (timer_m <= (count_nonzero (vis1_m)))) (PreH34 : (timer_m < n_pre)) (PreH35 : (timer_v_low_level_spec <= timer_m)) (PreH36 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH37 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH38 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH39 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH40 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH41 : (0 <= v)) (PreH42 : (v < n_pre)) (PreH43 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (bind ((dfs_finish (g_low_level_spec) (v))) ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))))) X_low_level_spec ) ”
).

Definition dfs1_partial_solve_wit_6_pure_split_goal_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (timer_m <= INT_MAX)) (PreH2 : (v <= INT_MAX)) (PreH3 : (hi <= INT_MAX)) (PreH4 : (lo <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (u_pre <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (timer_m >= INT_MIN)) (PreH9 : (v >= INT_MIN)) (PreH10 : (hi >= INT_MIN)) (PreH11 : (lo >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (u_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((Znth v vis1_m 0) = 0)) (PreH16 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH17 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH20 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH21 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH22 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH23 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH24 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= i)) (PreH27 : (i < hi)) (PreH28 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH29 : (0 <= u_pre)) (PreH30 : (u_pre < n_pre)) (PreH31 : (n_pre <= 2147483646)) (PreH32 : (0 <= timer_m)) (PreH33 : (timer_m <= (count_nonzero (vis1_m)))) (PreH34 : (timer_m < n_pre)) (PreH35 : (timer_v_low_level_spec <= timer_m)) (PreH36 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH37 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH38 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH39 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH40 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH41 : (0 <= v)) (PreH42 : (v < n_pre)) (PreH43 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (bind ((dfs_finish (g_low_level_spec) (v))) ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))))) X_low_level_spec ) ”
.

Definition dfs1_partial_solve_wit_6_aux := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m 0) = 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) (PreH27 : (0 <= v)) (PreH28 : (v < n_pre)) (PreH29 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (v) (vis1_m) (0)) = 0) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (bind ((dfs_finish (g_low_level_spec) (v))) ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))))) X_low_level_spec ) ” 
  &&  “ ((Znth v vis1_m 0) = 0) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (timer_v_low_level_spec <= timer_m) ” 
  &&  “ ((timer_m + 1 ) <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u_pre) (vis1_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ” 
  &&  “ (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m ) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (i) (radj_col_l_low_level_spec) (0))) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
.

Definition dfs1_partial_solve_wit_6 := dfs1_partial_solve_wit_6_pure -> dfs1_partial_solve_wit_6_aux.

Definition dfs1_partial_solve_wit_7 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (timer_m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m )) (PreH6 : (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre )) (PreH7 : (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre )) (PreH8 : (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i <= hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= 2147483646)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m <= (count_nonzero (vis1_m)))) (PreH20 : (timer_m < n_pre)) (PreH21 : (timer_v_low_level_spec <= timer_m)) (PreH22 : ((timer_m + 1 ) <= (count_nonzero (vis1_m)))) (PreH23 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH24 : ((Znth (u_pre) (vis1_m) (0)) <> 0)) (PreH25 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0))) (PreH26 : (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m )) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
|--
  “ (i >= hi) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m timer_m ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_m n_pre ) ” 
  &&  “ (dfs1_active_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_m fin_m timer_m u_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer_m < n_pre) ” 
  &&  “ (timer_v_low_level_spec <= timer_m) ” 
  &&  “ ((timer_m + 1 ) <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ ((Znth (u_pre) (vis1_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_m) (0)) <> 0)) ” 
  &&  “ (dfs1_active_timer_surplus vis1_l_low_level_spec vis1_m timer_v_low_level_spec timer_m ) ”
  &&  (((fin_pre + (timer_m * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i fin_pre timer_m 0 n_pre fin_m )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((timer_p_pre) # Int  |-> timer_m)
.

Definition dfs1_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (f_bind_spec: (unit -> (@ MonadErr.M  KSt B))) (X_bind_spec: (B -> (KSt -> Prop))) (timer_v_bind_spec: Z) (fin_l_bind_spec: (@list Z)) (vis1_l_bind_spec: (@list Z)) (radj_row_l_bind_spec: (@list Z)) (radj_col_l_bind_spec: (@list Z)) (g_bind_spec: AdjGraph) ,
  “ (csr_wf1 g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec vis1_l_bind_spec fin_l_bind_spec ) ” 
  &&  “ (csr1_faithful g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec ) ” 
  &&  “ ((adj_verts (g_bind_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec vis1_l_bind_spec fin_l_bind_spec timer_v_bind_spec ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_bind_spec vis1_l_bind_spec timer_v_bind_spec n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_bind_spec) (radj_col_l_bind_spec) (radj_row_l_bind_spec) (vis1_l_bind_spec) (fin_l_bind_spec) (timer_v_bind_spec)) (bind ((dfs_finish (g_bind_spec) (u_pre))) (f_bind_spec)) X_bind_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis1_l_bind_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_bind_spec) ” 
  &&  “ (timer_v_bind_spec <= (count_nonzero (vis1_l_bind_spec))) ” 
  &&  “ (timer_v_bind_spec < n_pre) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_bind_spec)) radj_col_l_bind_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_bind_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_bind_spec )
  **  (IntArray.full fin_pre n_pre fin_l_bind_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_bind_spec)
|--
EX (g_low_level_spec: AdjGraph) (radj_col_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (timer_v_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) ,
  (“ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_low_level_spec) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec))) ” 
  &&  “ (timer_v_low_level_spec < n_pre) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec))
  **
  ((EX timer_v__2 vis1_l__2 fin_l__2,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l__2 fin_l__2 ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l__2 fin_l__2 timer_v__2 ) ” 
  &&  “ (dfs1_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_l__2 fin_l__2 timer_v__2 u_pre ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l__2 vis1_l__2 timer_v__2 n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l__2) (fin_l__2) (timer_v__2)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (0 <= timer_v__2) ” 
  &&  “ (timer_v__2 <= (count_nonzero (vis1_l__2))) ” 
  &&  “ (timer_v_low_level_spec <= timer_v__2) ” 
  &&  “ (dfs1_timer_surplus_preserved vis1_l_low_level_spec vis1_l__2 timer_v_low_level_spec timer_v__2 ) ” 
  &&  “ forall (w_2: Z) , ((((0 <= w_2) /\ (w_2 < n_pre)) /\ ((Znth (w_2) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w_2) (vis1_l__2) (0)) <> 0)) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l__2 )
  **  (IntArray.full fin_pre n_pre fin_l__2 )
  **  ((timer_p_pre) # Int  |-> timer_v__2))
  -*
  (EX timer_v_ vis1_l_ fin_l_,
  “ (csr_wf1 g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec vis1_l_ fin_l_ ) ” 
  &&  “ ((adj_verts (g_bind_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec vis1_l_ fin_l_ timer_v_ ) ” 
  &&  “ (dfs1_sequence_extension g_bind_spec vis1_l_bind_spec fin_l_bind_spec timer_v_bind_spec vis1_l_ fin_l_ timer_v_ u_pre ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_bind_spec) (radj_col_l_bind_spec) (radj_row_l_bind_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf (f_bind_spec) (tt)) X_bind_spec ) ” 
  &&  “ (0 <= timer_v_) ” 
  &&  “ (timer_v_ <= (count_nonzero (vis1_l_))) ” 
  &&  “ (timer_v_bind_spec <= timer_v_) ” 
  &&  “ (dfs1_timer_surplus_preserved vis1_l_bind_spec vis1_l_ timer_v_bind_spec timer_v_ ) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_bind_spec) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0)) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_bind_spec)) radj_col_l_bind_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_bind_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  ((timer_p_pre) # Int  |-> timer_v_)))
.

Definition dfs1_derive_high_level_spec_by_low_level_spec := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_high_level_spec: (unit -> (KSt -> Prop))) (timer_v_high_level_spec: Z) (fin_l_high_level_spec: (@list Z)) (vis1_l_high_level_spec: (@list Z)) (radj_row_l_high_level_spec: (@list Z)) (radj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) ,
  “ (csr_wf1 g_high_level_spec radj_col_l_high_level_spec radj_row_l_high_level_spec vis1_l_high_level_spec fin_l_high_level_spec ) ” 
  &&  “ (csr1_faithful g_high_level_spec radj_col_l_high_level_spec radj_row_l_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_high_level_spec radj_col_l_high_level_spec radj_row_l_high_level_spec vis1_l_high_level_spec fin_l_high_level_spec timer_v_high_level_spec ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_high_level_spec vis1_l_high_level_spec timer_v_high_level_spec n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l_high_level_spec) (radj_row_l_high_level_spec) (vis1_l_high_level_spec) (fin_l_high_level_spec) (timer_v_high_level_spec)) (dfs_finish (g_high_level_spec) (u_pre)) X_high_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis1_l_high_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_high_level_spec) ” 
  &&  “ (timer_v_high_level_spec <= (count_nonzero (vis1_l_high_level_spec))) ” 
  &&  “ (timer_v_high_level_spec < n_pre) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_high_level_spec)) radj_col_l_high_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_high_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_high_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_high_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_high_level_spec)
|--
EX (g_low_level_spec: AdjGraph) (radj_col_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (timer_v_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) ,
  (“ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ (csr1_faithful g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_low_level_spec vis1_l_low_level_spec timer_v_low_level_spec n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_low_level_spec) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec))) ” 
  &&  “ (timer_v_low_level_spec < n_pre) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  ((timer_p_pre) # Int  |-> timer_v_low_level_spec))
  **
  ((EX timer_v__2 vis1_l__2 fin_l__2,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l__2 fin_l__2 ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l__2 fin_l__2 timer_v__2 ) ” 
  &&  “ (dfs1_sequence_extension g_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec timer_v_low_level_spec vis1_l__2 fin_l__2 timer_v__2 u_pre ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l__2 vis1_l__2 timer_v__2 n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l__2) (fin_l__2) (timer_v__2)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (0 <= timer_v__2) ” 
  &&  “ (timer_v__2 <= (count_nonzero (vis1_l__2))) ” 
  &&  “ (timer_v_low_level_spec <= timer_v__2) ” 
  &&  “ (dfs1_timer_surplus_preserved vis1_l_low_level_spec vis1_l__2 timer_v_low_level_spec timer_v__2 ) ” 
  &&  “ forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_l_low_level_spec) (0)) <> 0)) -> ((Znth (w) (vis1_l__2) (0)) <> 0)) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l__2 )
  **  (IntArray.full fin_pre n_pre fin_l__2 )
  **  ((timer_p_pre) # Int  |-> timer_v__2))
  -*
  (EX vis1_l_ fin_l_ timer_v_,
  “ (dfs1_sequence_state_ready g_high_level_spec radj_col_l_high_level_spec radj_row_l_high_level_spec vis1_l_ fin_l_ timer_v_ ) ” 
  &&  “ (dfs1_sequence_extension g_high_level_spec vis1_l_high_level_spec fin_l_high_level_spec timer_v_high_level_spec vis1_l_ fin_l_ timer_v_ u_pre ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l_high_level_spec) (radj_row_l_high_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (return (tt)) X_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_high_level_spec)) radj_col_l_high_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_high_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  ((timer_p_pre) # Int  |-> timer_v_)))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.

Axiom proof_of_dfs1_safety_wit_1 : dfs1_safety_wit_1.
Axiom proof_of_dfs1_safety_wit_2 : dfs1_safety_wit_2.
Axiom proof_of_dfs1_safety_wit_3 : dfs1_safety_wit_3.
Axiom proof_of_dfs1_safety_wit_4 : dfs1_safety_wit_4.
Axiom proof_of_dfs1_safety_wit_5 : dfs1_safety_wit_5.
Axiom proof_of_dfs1_safety_wit_6 : dfs1_safety_wit_6.
Axiom proof_of_dfs1_safety_wit_7 : dfs1_safety_wit_7.
Axiom proof_of_dfs1_safety_wit_8 : dfs1_safety_wit_8.
Axiom proof_of_dfs1_safety_wit_9 : dfs1_safety_wit_9.
Axiom proof_of_dfs1_safety_wit_10 : dfs1_safety_wit_10.
Axiom proof_of_dfs1_entail_wit_1 : dfs1_entail_wit_1.
Axiom proof_of_dfs1_entail_wit_2 : dfs1_entail_wit_2.
Axiom proof_of_dfs1_entail_wit_3_1 : dfs1_entail_wit_3_1.
Axiom proof_of_dfs1_entail_wit_3_2 : dfs1_entail_wit_3_2.
Axiom proof_of_dfs1_return_wit_1 : dfs1_return_wit_1.
Axiom proof_of_dfs1_partial_solve_wit_1 : dfs1_partial_solve_wit_1.
Axiom proof_of_dfs1_partial_solve_wit_2 : dfs1_partial_solve_wit_2.
Axiom proof_of_dfs1_partial_solve_wit_3 : dfs1_partial_solve_wit_3.
Axiom proof_of_dfs1_partial_solve_wit_4 : dfs1_partial_solve_wit_4.
Axiom proof_of_dfs1_partial_solve_wit_5 : dfs1_partial_solve_wit_5.
Axiom proof_of_dfs1_partial_solve_wit_6_pure : dfs1_partial_solve_wit_6_pure.
Axiom proof_of_dfs1_partial_solve_wit_6 : dfs1_partial_solve_wit_6.
Axiom proof_of_dfs1_partial_solve_wit_7 : dfs1_partial_solve_wit_7.
Axiom proof_of_dfs1_derive_bind_spec_by_low_level_spec : dfs1_derive_bind_spec_by_low_level_spec.
Axiom proof_of_dfs1_derive_high_level_spec_by_low_level_spec : dfs1_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
