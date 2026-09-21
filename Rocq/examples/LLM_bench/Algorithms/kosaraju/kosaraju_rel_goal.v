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
Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.dfs2_lib.
Require Import SimpleC.EE.LLM_bench.Algorithms.kosaraju.kosaraju_rel_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import safeexecE_strategy_goal.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import safeexecE_strategy_proof.

(*----- Function transpose -----*)

Definition transpose_safety_wit_1 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (m_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (m_pre <= 2147483646)) (PreH6 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH7 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : (AdjGraphValid g_low_level_spec )) (PreH10 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m_pre)) (PreH12 : ((Zlength (radj_row_l_low_level_spec)) = (n_pre + 1 ))) (PreH13 : ((Zlength (pos_l_low_level_spec)) = n_pre)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition transpose_safety_wit_2 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (m: Z) (v: Z) (rr_m: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < v)) -> ((Znth (k) (rr_m) (0)) = 0))) ,
  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition transpose_safety_wit_3 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (m: Z) (v: Z) (rr_m: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < v)) -> ((Znth (k) (rr_m) (0)) = 0))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (v) (0) (rr_m)) )
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition transpose_safety_wit_4 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < v)) -> ((Znth (k) (rr_m) (0)) = 0))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition transpose_safety_wit_5 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (((Znth v rr_m 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth v rr_m 0) + 1 )) ”
) \/
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (((Znth v rr_m 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth v rr_m 0) + 1 )) ”
).

Definition transpose_safety_wit_5_split_goal_1 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (((Znth v rr_m 0) + 1 ) <= INT_MAX) ”
.

Definition transpose_safety_wit_5_split_goal_2 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ ((INT_MIN) <= ((Znth v rr_m 0) + 1 )) ”
.

Definition transpose_safety_wit_6 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition transpose_safety_wit_7 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (v) (((Znth v rr_m 0) + 1 )) (rr_m)) )
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition transpose_safety_wit_8 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (j: Z) (m: Z) (PreH1 : (j >= m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition transpose_safety_wit_9 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (j: Z) (m: Z) (PreH1 : (j >= m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition transpose_safety_wit_10 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (v: Z) (rr_m: (@list Z)) (pos_m: (@list Z)) (cnt_m: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m )) (PreH19 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m)))) ,
  (IntArray.full pos_pre n_pre (replace_Znth (v) (sum) (pos_m)) )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (v) (sum) (rr_m)) )
  **  ((( &( "deg" ) )) # Int  |-> (Znth v rr_m 0))
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
|--
  “ ((sum + (Znth v rr_m 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth v rr_m 0) )) ”
.

Definition transpose_safety_wit_11 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (v: Z) (rr_m: (@list Z)) (pos_m: (@list Z)) (cnt_m: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m )) (PreH19 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m)))) ,
  (IntArray.full pos_pre n_pre (replace_Znth (v) (sum) (pos_m)) )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (v) (sum) (rr_m)) )
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth v rr_m 0) ))
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition transpose_safety_wit_12 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m: (@list Z)) (cnt_m: (@list Z)) (pos_m: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m )) (PreH19 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m)))) ,
  ((( &( "u" ) )) # Int  |->_)
  **  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (n_pre) (sum) (rr_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition transpose_safety_wit_13 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m)) = n_pre)) (PreH13 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u fadj_row_l_low_level_spec 0))
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ ((u + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u + 1 )) ”
.

Definition transpose_safety_wit_14 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m)) = n_pre)) (PreH13 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u fadj_row_l_low_level_spec 0))
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition transpose_safety_wit_15 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) (replace_Znth (p) (u) (rc_m)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ ((p + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition transpose_safety_wit_16 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) (replace_Znth (p) (u) (rc_m)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition transpose_safety_wit_17 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full pos_pre n_pre (replace_Znth (v) ((p + 1 )) (pos_m)) )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) (replace_Znth (p) (u) (rc_m)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition transpose_safety_wit_18 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full pos_pre n_pre (replace_Znth (v) ((p + 1 )) (pos_m)) )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) (replace_Znth (p) (u) (rc_m)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition transpose_safety_wit_19 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m: (@list Z)) (pos_m: (@list Z)) (rc_m: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j >= hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ ((u + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u + 1 )) ”
.

Definition transpose_entail_wit_1 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (m_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (m_pre <= 2147483646)) (PreH6 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH7 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : (AdjGraphValid g_low_level_spec )) (PreH10 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m_pre)) (PreH12 : ((Zlength (radj_row_l_low_level_spec)) = (n_pre + 1 ))) (PreH13 : ((Zlength (pos_l_low_level_spec)) = n_pre)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  EX (rr_m: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m_pre <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m_pre) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (rr_m) (0)) = 0)) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
) \/
(
forall (m_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (m_pre <= 2147483646)) (PreH6 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH7 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : (AdjGraphValid g_low_level_spec )) (PreH10 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m_pre)) (PreH12 : ((Zlength (radj_row_l_low_level_spec)) = (n_pre + 1 ))) (PreH13 : ((Zlength (pos_l_low_level_spec)) = n_pre)) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (radj_row_l_low_level_spec) (0)) = 0)) ”
  &&  emp
).

Definition transpose_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (m_pre <= 2147483646)) (PreH6 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH7 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : (AdjGraphValid g_low_level_spec )) (PreH10 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m_pre)) (PreH12 : ((Zlength (radj_row_l_low_level_spec)) = (n_pre + 1 ))) (PreH13 : ((Zlength (pos_l_low_level_spec)) = n_pre)) ,
  forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (radj_row_l_low_level_spec) (0)) = 0))
.

Definition transpose_entail_wit_2 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (m: Z) (v: Z) (rr_m_2: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < v)) -> ((Znth (k) (rr_m_2) (0)) = 0))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (v) (0) (rr_m_2)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  EX (rr_m: (@list Z)) ,
  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (v + 1 ))) -> ((Znth (k) (rr_m) (0)) = 0)) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
) \/
(
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (m: Z) (v: Z) (rr_m_2: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < v)) -> ((Znth (k) (rr_m_2) (0)) = 0))) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (v) (0) (rr_m_2)))) = (n_pre + 1 )) ”
  &&  emp
).

Definition transpose_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (m: Z) (v: Z) (rr_m_2: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < v)) -> ((Znth (k) (rr_m_2) (0)) = 0))) ,
  ((Zlength ((replace_Znth (v) (0) (rr_m_2)))) = (n_pre + 1 ))
.

Definition transpose_entail_wit_3 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < v)) -> ((Znth (k_2) (rr_m_2) (0)) = 0))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m_2 )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  EX (rr_m: (@list Z)) ,
  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ (transpose_count_ready n_pre 0 rr_m ) ” 
  &&  “ (transpose_count_values n_pre 0 fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= 0))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
) \/
(
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < v)) -> ((Znth (k_2) (rr_m_2) (0)) = 0))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= 0))) ” 
  &&  “ (transpose_count_values n_pre 0 fadj_col_l_low_level_spec rr_m_2 ) ” 
  &&  “ (transpose_count_ready n_pre 0 rr_m_2 ) ”
  &&  emp
).

Definition transpose_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < v)) -> ((Znth (k_2) (rr_m_2) (0)) = 0))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= 0)))
.

Definition transpose_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < v)) -> ((Znth (k_2) (rr_m_2) (0)) = 0))) ,
  (transpose_count_values n_pre 0 fadj_col_l_low_level_spec rr_m_2 )
.

Definition transpose_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < v)) -> ((Znth (k_2) (rr_m_2) (0)) = 0))) ,
  (transpose_count_ready n_pre 0 rr_m_2 )
.

Definition transpose_entail_wit_4 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (m: Z) (rr_m: (@list Z)) (PreH1 : (j < m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m) (0))) /\ ((Znth (k_2) (rr_m) (0)) <= j)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (0 <= m) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= (Znth j fadj_col_l_low_level_spec 0)) ” 
  &&  “ ((Znth j fadj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ ((Znth j fadj_col_l_low_level_spec 0) = (Znth (j) (fadj_col_l_low_level_spec) (0))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ (transpose_count_ready n_pre j rr_m ) ” 
  &&  “ (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
) \/
(
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (m: Z) (rr_m: (@list Z)) (PreH1 : (j < m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m) (0))) /\ ((Znth (k_2) (rr_m) (0)) <= j)))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j))) ” 
  &&  “ ((Znth j fadj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ (0 <= (Znth j fadj_col_l_low_level_spec 0)) ”
  &&  emp
).

Definition transpose_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (m: Z) (rr_m: (@list Z)) (PreH1 : (j < m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m) (0))) /\ ((Znth (k_2) (rr_m) (0)) <= j)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))
.

Definition transpose_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (m: Z) (rr_m: (@list Z)) (PreH1 : (j < m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m) (0))) /\ ((Znth (k_2) (rr_m) (0)) <= j)))) ,
  ((Znth j fadj_col_l_low_level_spec 0) < n_pre)
.

Definition transpose_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (m: Z) (rr_m: (@list Z)) (PreH1 : (j < m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m) (0))) /\ ((Znth (k_2) (rr_m) (0)) <= j)))) ,
  (0 <= (Znth j fadj_col_l_low_level_spec 0))
.

Definition transpose_entail_wit_5 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m_2 )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m_2 )) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m_2) (0))) /\ ((Znth (k_2) (rr_m_2) (0)) <= j)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  EX (rr_m: (@list Z)) ,
  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ (transpose_count_ready n_pre (j + 1 ) rr_m ) ” 
  &&  “ (transpose_count_values n_pre (j + 1 ) fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= (j + 1 )))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
) \/
(
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m_2 )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m_2 )) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m_2) (0))) /\ ((Znth (k_2) (rr_m_2) (0)) <= j)))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) ((replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2))) (0))) /\ ((Znth (k) ((replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2))) (0)) <= (j + 1 )))) ” 
  &&  “ (transpose_count_values n_pre (j + 1 ) fadj_col_l_low_level_spec (replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2)) ) ” 
  &&  “ (transpose_count_ready n_pre (j + 1 ) (replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2)))) = (n_pre + 1 )) ”
  &&  emp
).

Definition transpose_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m_2 )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m_2 )) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m_2) (0))) /\ ((Znth (k_2) (rr_m_2) (0)) <= j)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) ((replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2))) (0))) /\ ((Znth (k) ((replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2))) (0)) <= (j + 1 ))))
.

Definition transpose_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m_2 )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m_2 )) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m_2) (0))) /\ ((Znth (k_2) (rr_m_2) (0)) <= j)))) ,
  (transpose_count_values n_pre (j + 1 ) fadj_col_l_low_level_spec (replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2)) )
.

Definition transpose_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m_2 )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m_2 )) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m_2) (0))) /\ ((Znth (k_2) (rr_m_2) (0)) <= j)))) ,
  (transpose_count_ready n_pre (j + 1 ) (replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2)) )
.

Definition transpose_entail_wit_5_split_goal_4 := 
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m_2 )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m_2 )) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m_2) (0))) /\ ((Znth (k_2) (rr_m_2) (0)) <= j)))) ,
  ((Zlength ((replace_Znth (v) (((Znth v rr_m_2 0) + 1 )) (rr_m_2)))) = (n_pre + 1 ))
.

Definition transpose_entail_wit_6 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (j: Z) (m: Z) (PreH1 : (j >= m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m_2 )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m_2 )) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m_2) (0))) /\ ((Znth (k_2) (rr_m_2) (0)) <= j)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m_2 )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  EX (rr_m: (@list Z))  (cnt_m: (@list Z))  (pos_m: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ (transpose_prefix_inv n_pre m 0 0 rr_m cnt_m ) ” 
  &&  “ (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m ) ” 
  &&  “ (transpose_prefix_offsets n_pre 0 rr_m pos_m cnt_m ) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((0 < 0) -> ((csr_lo (0) (rr_m)) = 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m) ” 
  &&  “ ((0 < n_pre) -> ((0 + (Znth (0) (rr_m) (0)) ) <= m)) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
) \/
(
forall (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m_2: (@list Z)) (j: Z) (m: Z) (PreH1 : (j >= m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m_2 )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m_2 )) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (rr_m_2) (0))) /\ ((Znth (k_2) (rr_m_2) (0)) <= j)))) ,
  TT && emp 
|--
  EX (cnt_m: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (adj_verts (g_low_level_spec))) ” 
  &&  “ (transpose_prefix_inv (adj_verts (g_low_level_spec)) (m_of (fadj_row_l_low_level_spec)) 0 0 rr_m_2 cnt_m ) ” 
  &&  “ (transpose_count_values (adj_verts (g_low_level_spec)) (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec cnt_m ) ” 
  &&  “ (transpose_prefix_offsets (adj_verts (g_low_level_spec)) 0 rr_m_2 pos_l_low_level_spec cnt_m ) ” 
  &&  “ ((0 < 0) -> ((csr_lo (0) (rr_m_2)) = 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 < (adj_verts (g_low_level_spec))) -> ((0 + (Znth (0) (rr_m_2) (0)) ) <= (m_of (fadj_row_l_low_level_spec)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (adj_verts (g_low_level_spec)))) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= (m_of (fadj_row_l_low_level_spec))))) ”
  &&  emp
).

Definition transpose_entail_wit_7 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (v: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (cnt_m_2: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m_2 )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m_2 )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m_2 )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  (IntArray.full pos_pre n_pre (replace_Znth (v) (sum) (pos_m_2)) )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (v) (sum) (rr_m_2)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
|--
  EX (rr_m: (@list Z))  (cnt_m: (@list Z))  (pos_m: (@list Z)) ,
  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ (transpose_prefix_inv n_pre m (v + 1 ) (sum + (Znth v rr_m_2 0) ) rr_m cnt_m ) ” 
  &&  “ (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m ) ” 
  &&  “ (transpose_prefix_offsets n_pre (v + 1 ) rr_m pos_m cnt_m ) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((0 < (v + 1 )) -> ((csr_lo (0) (rr_m)) = 0)) ” 
  &&  “ (0 <= (sum + (Znth v rr_m_2 0) )) ” 
  &&  “ ((sum + (Znth v rr_m_2 0) ) <= m) ” 
  &&  “ (((v + 1 ) < n_pre) -> (((sum + (Znth v rr_m_2 0) ) + (Znth ((v + 1 )) (rr_m) (0)) ) <= m)) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
) \/
(
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (v: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (cnt_m_2: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m_2 )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m_2 )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m_2 )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  TT && emp 
|--
  EX (cnt_m: (@list Z)) ,
  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= (adj_verts (g_low_level_spec))) ” 
  &&  “ ((Zlength ((replace_Znth (v) (sum) (pos_m_2)))) = (adj_verts (g_low_level_spec))) ” 
  &&  “ (transpose_prefix_inv (adj_verts (g_low_level_spec)) (m_of (fadj_row_l_low_level_spec)) (v + 1 ) (sum + (Znth v rr_m_2 0) ) (replace_Znth (v) (sum) (rr_m_2)) cnt_m ) ” 
  &&  “ (transpose_count_values (adj_verts (g_low_level_spec)) (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec cnt_m ) ” 
  &&  “ (transpose_prefix_offsets (adj_verts (g_low_level_spec)) (v + 1 ) (replace_Znth (v) (sum) (rr_m_2)) (replace_Znth (v) (sum) (pos_m_2)) cnt_m ) ” 
  &&  “ ((Zlength ((replace_Znth (v) (sum) (rr_m_2)))) = ((adj_verts (g_low_level_spec)) + 1 )) ” 
  &&  “ ((0 < (v + 1 )) -> ((csr_lo (0) ((replace_Znth (v) (sum) (rr_m_2)))) = 0)) ” 
  &&  “ (0 <= (sum + (Znth v rr_m_2 0) )) ” 
  &&  “ ((sum + (Znth v rr_m_2 0) ) <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (((v + 1 ) < (adj_verts (g_low_level_spec))) -> (((sum + (Znth v rr_m_2 0) ) + (Znth ((v + 1 )) ((replace_Znth (v) (sum) (rr_m_2))) (0)) ) <= (m_of (fadj_row_l_low_level_spec)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (adj_verts (g_low_level_spec)))) -> ((0 <= (Znth (k) ((replace_Znth (v) (sum) (rr_m_2))) (0))) /\ ((Znth (k) ((replace_Znth (v) (sum) (rr_m_2))) (0)) <= (m_of (fadj_row_l_low_level_spec))))) ”
  &&  emp
).

Definition transpose_entail_wit_8 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m_2: (@list Z)) (cnt_m: (@list Z)) (pos_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (n_pre) (sum) (rr_m_2)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_m_2 )
|--
  EX (rr_m: (@list Z))  (pos_m: (@list Z))  (rc_m: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (transpose_scatter_inv n_pre m (csr_lo (0) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (0) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
) \/
(
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m_2: (@list Z)) (cnt_m: (@list Z)) (pos_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  TT && emp 
|--
  “ (transpose_scatter_contents g_low_level_spec n_pre 0 fadj_row_l_low_level_spec fadj_col_l_low_level_spec (replace_Znth (n_pre) (sum) (rr_m_2)) radj_col_l_low_level_spec ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec (replace_Znth (n_pre) (sum) (rr_m_2)) ) ” 
  &&  “ (transpose_scatter_inv n_pre m 0 fadj_col_l_low_level_spec (replace_Znth (n_pre) (sum) (rr_m_2)) pos_m_2 ) ” 
  &&  “ ((csr_lo (0) ((replace_Znth (n_pre) (sum) (rr_m_2)))) = 0) ” 
  &&  “ ((Zlength ((replace_Znth (n_pre) (sum) (rr_m_2)))) = (n_pre + 1 )) ” 
  &&  “ (sum = m) ”
  &&  emp
).

Definition transpose_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m_2: (@list Z)) (cnt_m: (@list Z)) (pos_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  (transpose_scatter_contents g_low_level_spec n_pre 0 fadj_row_l_low_level_spec fadj_col_l_low_level_spec (replace_Znth (n_pre) (sum) (rr_m_2)) radj_col_l_low_level_spec )
.

Definition transpose_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m_2: (@list Z)) (cnt_m: (@list Z)) (pos_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec (replace_Znth (n_pre) (sum) (rr_m_2)) )
.

Definition transpose_entail_wit_8_split_goal_3 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m_2: (@list Z)) (cnt_m: (@list Z)) (pos_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  (transpose_scatter_inv n_pre m 0 fadj_col_l_low_level_spec (replace_Znth (n_pre) (sum) (rr_m_2)) pos_m_2 )
.

Definition transpose_entail_wit_8_split_goal_4 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m_2: (@list Z)) (cnt_m: (@list Z)) (pos_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  ((csr_lo (0) ((replace_Znth (n_pre) (sum) (rr_m_2)))) = 0)
.

Definition transpose_entail_wit_8_split_goal_5 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m_2: (@list Z)) (cnt_m: (@list Z)) (pos_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  ((Zlength ((replace_Znth (n_pre) (sum) (rr_m_2)))) = (n_pre + 1 ))
.

Definition transpose_entail_wit_8_split_goal_6 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m_2: (@list Z)) (cnt_m: (@list Z)) (pos_m_2: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m_2)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m_2 cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m_2 pos_m_2 cnt_m )) (PreH19 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m_2)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m_2) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m_2) (0))) /\ ((Znth (k) (rr_m_2) (0)) <= m)))) ,
  (sum = m)
.

Definition transpose_entail_wit_9 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m_2 )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m_2 )
  **  (IntArray.full pos_pre n_pre pos_m_2 )
|--
  EX (rr_m: (@list Z))  (pos_m: (@list Z))  (rc_m: (@list Z)) ,
  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((Znth u fadj_row_l_low_level_spec 0) = (csr_lo (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth (u + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= (Znth u fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u fadj_row_l_low_level_spec 0) <= (Znth u fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u fadj_row_l_low_level_spec 0) <= (Znth (u + 1 ) fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (transpose_scatter_inv n_pre m (Znth u fadj_row_l_low_level_spec 0) fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre (Znth u fadj_row_l_low_level_spec 0) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
) \/
(
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  TT && emp 
|--
  “ (transpose_scatter_contents g_low_level_spec n_pre (Znth u fadj_row_l_low_level_spec 0) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 ) ” 
  &&  “ (transpose_scatter_inv n_pre sum (Znth u fadj_row_l_low_level_spec 0) fadj_col_l_low_level_spec rr_m_2 pos_m_2 ) ” 
  &&  “ ((Znth (u + 1 ) fadj_row_l_low_level_spec 0) <= sum) ” 
  &&  “ ((Znth u fadj_row_l_low_level_spec 0) <= (Znth (u + 1 ) fadj_row_l_low_level_spec 0)) ” 
  &&  “ (0 <= (Znth u fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth u fadj_row_l_low_level_spec 0) = (csr_lo (u) (fadj_row_l_low_level_spec))) ”
  &&  emp
).

Definition transpose_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (transpose_scatter_contents g_low_level_spec n_pre (Znth u fadj_row_l_low_level_spec 0) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )
.

Definition transpose_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (transpose_scatter_inv n_pre sum (Znth u fadj_row_l_low_level_spec 0) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )
.

Definition transpose_entail_wit_9_split_goal_3 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Znth (u + 1 ) fadj_row_l_low_level_spec 0) <= sum)
.

Definition transpose_entail_wit_9_split_goal_4 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Znth u fadj_row_l_low_level_spec 0) <= (Znth (u + 1 ) fadj_row_l_low_level_spec 0))
.

Definition transpose_entail_wit_9_split_goal_5 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (0 <= (Znth u fadj_row_l_low_level_spec 0))
.

Definition transpose_entail_wit_9_split_goal_6 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Znth (u + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u) (fadj_row_l_low_level_spec)))
.

Definition transpose_entail_wit_9_split_goal_7 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((Zlength (rr_m_2)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Znth u fadj_row_l_low_level_spec 0) = (csr_lo (u) (fadj_row_l_low_level_spec)))
.

Definition transpose_entail_wit_10 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (rc_m_2: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j < hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m_2)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m_2 )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m_2 )
  **  (IntArray.full pos_pre n_pre pos_m_2 )
|--
  EX (rr_m: (@list Z))  (pos_m: (@list Z))  (rc_m: (@list Z)) ,
  “ (0 <= j) ” 
  &&  “ (j < hi) ” 
  &&  “ (0 <= (Znth j fadj_col_l_low_level_spec 0)) ” 
  &&  “ ((Znth j fadj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ ((Znth j fadj_col_l_low_level_spec 0) = (Znth (j) (fadj_col_l_low_level_spec) (0))) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (lo = (csr_lo (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= j) ” 
  &&  “ (j <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
) \/
(
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (rc_m_2: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j < hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m_2)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  TT && emp 
|--
  “ ((Znth j fadj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ (0 <= (Znth j fadj_col_l_low_level_spec 0)) ”
  &&  emp
).

Definition transpose_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (rc_m_2: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j < hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m_2)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Znth j fadj_col_l_low_level_spec 0) < n_pre)
.

Definition transpose_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (rc_m_2: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j < hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m_2)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (0 <= (Znth j fadj_col_l_low_level_spec 0))
.

Definition transpose_entail_wit_11 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= v)) (PreH4 : (v < n_pre)) (PreH5 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= m)) (PreH11 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (m <= 2147483646)) (PreH13 : (sum = m)) (PreH14 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH16 : ((Zlength (pos_m)) = n_pre)) (PreH17 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH18 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH20 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH21 : (AdjGraphValid g_low_level_spec )) (PreH22 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH23 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH24 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= j)) (PreH27 : (j <= hi)) (PreH28 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH29 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m )) (PreH30 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH31 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (IntArray.full pos_pre n_pre pos_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m_2 )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m_2 )
|--
  EX (rr_m: (@list Z))  (rc_m: (@list Z))  (pos_m_2: (@list Z)) ,
  “ (0 <= j) ” 
  &&  “ (j < hi) ” 
  &&  “ (0 <= (Znth v pos_m 0)) ” 
  &&  “ ((Znth v pos_m 0) < (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth v pos_m 0) = (Znth (v) (pos_m_2) (0))) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (j) (fadj_col_l_low_level_spec) (0))) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m_2)) = n_pre) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (lo = (csr_lo (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= j) ” 
  &&  “ (j <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m_2 ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m_2 )
) \/
(
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= v)) (PreH4 : (v < n_pre)) (PreH5 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= m)) (PreH11 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (m <= 2147483646)) (PreH13 : (sum = m)) (PreH14 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH16 : ((Zlength (pos_m)) = n_pre)) (PreH17 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH18 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH20 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH21 : (AdjGraphValid g_low_level_spec )) (PreH22 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH23 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH24 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= j)) (PreH27 : (j <= hi)) (PreH28 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH29 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m )) (PreH30 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH31 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  TT && emp 
|--
  “ ((Znth v pos_m 0) < m) ” 
  &&  “ (0 <= (Znth v pos_m 0)) ”
  &&  emp
).

Definition transpose_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= v)) (PreH4 : (v < n_pre)) (PreH5 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= m)) (PreH11 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (m <= 2147483646)) (PreH13 : (sum = m)) (PreH14 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH16 : ((Zlength (pos_m)) = n_pre)) (PreH17 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH18 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH20 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH21 : (AdjGraphValid g_low_level_spec )) (PreH22 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH23 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH24 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= j)) (PreH27 : (j <= hi)) (PreH28 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH29 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m )) (PreH30 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH31 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Znth v pos_m 0) < m)
.

Definition transpose_entail_wit_11_split_goal_2 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= v)) (PreH4 : (v < n_pre)) (PreH5 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= m)) (PreH11 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (m <= 2147483646)) (PreH13 : (sum = m)) (PreH14 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH16 : ((Zlength (pos_m)) = n_pre)) (PreH17 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH18 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH20 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH21 : (AdjGraphValid g_low_level_spec )) (PreH22 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH23 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH24 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= j)) (PreH27 : (j <= hi)) (PreH28 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH29 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m )) (PreH30 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH31 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (0 <= (Znth v pos_m 0))
.

Definition transpose_entail_wit_12 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m_2) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m_2)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (IntArray.full pos_pre n_pre (replace_Znth (v) ((p + 1 )) (pos_m_2)) )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) (replace_Znth (p) (u) (rc_m_2)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m_2 )
|--
  EX (rr_m: (@list Z))  (pos_m: (@list Z))  (rc_m: (@list Z)) ,
  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ (lo = (csr_lo (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (transpose_scatter_inv n_pre m (j + 1 ) fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre (j + 1 ) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
) \/
(
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m_2) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m_2)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  TT && emp 
|--
  “ (transpose_scatter_contents g_low_level_spec n_pre (j + 1 ) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 (replace_Znth (p) (u) (rc_m_2)) ) ” 
  &&  “ (transpose_scatter_inv n_pre m (j + 1 ) fadj_col_l_low_level_spec rr_m_2 (replace_Znth (v) ((p + 1 )) (pos_m_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (v) ((p + 1 )) (pos_m_2)))) = n_pre) ” 
  &&  “ ((Zlength ((replace_Znth (v) ((p + 1 )) (pos_m_2)))) = n_pre) ” 
  &&  “ ((Zlength ((replace_Znth (p) (u) (rc_m_2)))) = m) ”
  &&  emp
).

Definition transpose_entail_wit_12_split_goal_1 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m_2) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m_2)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (transpose_scatter_contents g_low_level_spec n_pre (j + 1 ) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 (replace_Znth (p) (u) (rc_m_2)) )
.

Definition transpose_entail_wit_12_split_goal_2 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m_2) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m_2)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (transpose_scatter_inv n_pre m (j + 1 ) fadj_col_l_low_level_spec rr_m_2 (replace_Znth (v) ((p + 1 )) (pos_m_2)) )
.

Definition transpose_entail_wit_12_split_goal_3 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m_2) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m_2)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Zlength ((replace_Znth (v) ((p + 1 )) (pos_m_2)))) = n_pre)
.

Definition transpose_entail_wit_12_split_goal_4 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m_2) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m_2)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Zlength ((replace_Znth (v) ((p + 1 )) (pos_m_2)))) = n_pre)
.

Definition transpose_entail_wit_12_split_goal_5 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m_2: (@list Z)) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m_2) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m_2)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Zlength ((replace_Znth (p) (u) (rc_m_2)))) = m)
.

Definition transpose_entail_wit_13 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (rc_m_2: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j >= hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m_2)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m_2 )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m_2 )
  **  (IntArray.full pos_pre n_pre pos_m_2 )
|--
  EX (rr_m: (@list Z))  (pos_m: (@list Z))  (rc_m: (@list Z)) ,
  “ (0 <= (u + 1 )) ” 
  &&  “ ((u + 1 ) <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (transpose_scatter_inv n_pre m (csr_lo ((u + 1 )) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre (csr_lo ((u + 1 )) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
) \/
(
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (rc_m_2: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j >= hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m_2)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  TT && emp 
|--
  “ (transpose_scatter_contents g_low_level_spec n_pre (csr_lo ((u + 1 )) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 ) ” 
  &&  “ (transpose_scatter_inv n_pre sum (csr_lo ((u + 1 )) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 ) ” 
  &&  “ ((Zlength (rr_m_2)) = (n_pre + 1 )) ”
  &&  emp
).

Definition transpose_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (rc_m_2: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j >= hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m_2)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (transpose_scatter_contents g_low_level_spec n_pre (csr_lo ((u + 1 )) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )
.

Definition transpose_entail_wit_13_split_goal_2 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (rc_m_2: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j >= hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m_2)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  (transpose_scatter_inv n_pre sum (csr_lo ((u + 1 )) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m_2 pos_m_2 )
.

Definition transpose_entail_wit_13_split_goal_3 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m_2: (@list Z)) (pos_m_2: (@list Z)) (rc_m_2: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j >= hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m_2)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m_2)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m_2)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m_2)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m_2 pos_m_2 )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m_2 )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m_2 rc_m_2 )) ,
  ((Zlength (rr_m_2)) = (n_pre + 1 ))
.

Definition transpose_return_wit_1 := 
(
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (pos_m: (@list Z)) (rc_m: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (u >= n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m)) = n_pre)) (PreH13 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  EX (pos_l_: (@list Z))  (radj_col_l_: (@list Z))  (radj_row_l_: (@list Z)) ,
  “ (transpose_spec g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec radj_col_l_ radj_row_l_ n_pre ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_ )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_ )
  **  (IntArray.full pos_pre n_pre pos_l_ )
) \/
(
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (pos_m: (@list Z)) (rc_m: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (u >= n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m)) = n_pre)) (PreH13 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  TT && emp 
|--
  “ (transpose_spec g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec rc_m rr_m n_pre ) ”
  &&  emp
).

Definition transpose_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (pos_m: (@list Z)) (rc_m: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (u >= n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m)) = n_pre)) (PreH13 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (transpose_spec g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec rc_m rr_m n_pre )
.

Definition transpose_partial_solve_wit_1 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (m: Z) (v: Z) (rr_m: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < v)) -> ((Znth (k) (rr_m) (0)) = 0))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (v < n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < v)) -> ((Znth (k) (rr_m) (0)) = 0)) ”
  &&  (((radj_row_pre + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i radj_row_pre v 0 (n_pre + 1 ) rr_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
.

Definition transpose_partial_solve_wit_2 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (m: Z) (rr_m: (@list Z)) (PreH1 : (j < m)) (PreH2 : (0 <= m)) (PreH3 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (0 <= j)) (PreH5 : (j <= m)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH17 : (transpose_count_ready n_pre j rr_m )) (PreH18 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (j < m) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ (transpose_count_ready n_pre j rr_m ) ” 
  &&  “ (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j))) ”
  &&  (((fadj_col_pre + (j * sizeof(INT)))) # Int  |-> (Znth j fadj_col_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_col_pre j 0 (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
.

Definition transpose_partial_solve_wit_3 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (0 <= m) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (j) (fadj_col_l_low_level_spec) (0))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ (transpose_count_ready n_pre j rr_m ) ” 
  &&  “ (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j))) ”
  &&  (((radj_row_pre + (v * sizeof(INT)))) # Int  |-> (Znth v rr_m 0))
  **  (IntArray.missing_i radj_row_pre v 0 (n_pre + 1 ) rr_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
.

Definition transpose_partial_solve_wit_4 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (pos_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rr_m: (@list Z)) (m: Z) (j: Z) (v: Z) (PreH1 : (0 <= m)) (PreH2 : (0 <= j)) (PreH3 : (j < (m_of (fadj_row_l_low_level_spec)))) (PreH4 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH10 : (m <= 2147483646)) (PreH11 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH13 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH14 : (AdjGraphValid g_low_level_spec )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH17 : ((Zlength (pos_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH19 : (transpose_count_ready n_pre j rr_m )) (PreH20 : (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m )) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
|--
  “ (0 <= m) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (j) (fadj_col_l_low_level_spec) (0))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ (transpose_count_ready n_pre j rr_m ) ” 
  &&  “ (transpose_count_values n_pre j fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= j))) ”
  &&  (((radj_row_pre + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i radj_row_pre v 0 (n_pre + 1 ) rr_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec )
.

Definition transpose_partial_solve_wit_5 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (v: Z) (rr_m: (@list Z)) (pos_m: (@list Z)) (cnt_m: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m )) (PreH19 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (v < n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ (transpose_prefix_inv n_pre m v sum rr_m cnt_m ) ” 
  &&  “ (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m ) ” 
  &&  “ (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m ) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((0 < v) -> ((csr_lo (0) (rr_m)) = 0)) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= m) ” 
  &&  “ ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m)) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m))) ”
  &&  (((radj_row_pre + (v * sizeof(INT)))) # Int  |-> (Znth v rr_m 0))
  **  (IntArray.missing_i radj_row_pre v 0 (n_pre + 1 ) rr_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_m )
.

Definition transpose_partial_solve_wit_6 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (v: Z) (rr_m: (@list Z)) (pos_m: (@list Z)) (cnt_m: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m )) (PreH19 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (v < n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ (transpose_prefix_inv n_pre m v sum rr_m cnt_m ) ” 
  &&  “ (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m ) ” 
  &&  “ (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m ) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((0 < v) -> ((csr_lo (0) (rr_m)) = 0)) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= m) ” 
  &&  “ ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m)) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m))) ”
  &&  (((radj_row_pre + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i radj_row_pre v 0 (n_pre + 1 ) rr_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_m )
.

Definition transpose_partial_solve_wit_7 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (v: Z) (rr_m: (@list Z)) (pos_m: (@list Z)) (cnt_m: (@list Z)) (PreH1 : (v < n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m )) (PreH19 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (v) (sum) (rr_m)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (v < n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ (transpose_prefix_inv n_pre m v sum rr_m cnt_m ) ” 
  &&  “ (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m ) ” 
  &&  “ (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m ) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((0 < v) -> ((csr_lo (0) (rr_m)) = 0)) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= m) ” 
  &&  “ ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m)) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m))) ”
  &&  (((pos_pre + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos_pre v 0 n_pre pos_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) (replace_Znth (v) (sum) (rr_m)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
.

Definition transpose_partial_solve_wit_8 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (rr_m: (@list Z)) (cnt_m: (@list Z)) (pos_m: (@list Z)) (m: Z) (v: Z) (PreH1 : (v >= n_pre)) (PreH2 : (0 <= v)) (PreH3 : (v <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH11 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH12 : (AdjGraphValid g_low_level_spec )) (PreH13 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH15 : ((Zlength (pos_m)) = n_pre)) (PreH16 : (transpose_prefix_inv n_pre m v sum rr_m cnt_m )) (PreH17 : (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m )) (PreH18 : (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m )) (PreH19 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH20 : ((0 < v) -> ((csr_lo (0) (rr_m)) = 0))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= m)) (PreH23 : ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (v >= n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ (transpose_prefix_inv n_pre m v sum rr_m cnt_m ) ” 
  &&  “ (transpose_count_values n_pre m fadj_col_l_low_level_spec cnt_m ) ” 
  &&  “ (transpose_prefix_offsets n_pre v rr_m pos_m cnt_m ) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((0 < v) -> ((csr_lo (0) (rr_m)) = 0)) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= m) ” 
  &&  “ ((v < n_pre) -> ((sum + (Znth (v) (rr_m) (0)) ) <= m)) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (rr_m) (0))) /\ ((Znth (k) (rr_m) (0)) <= m))) ”
  &&  (((radj_row_pre + (n_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i radj_row_pre n_pre 0 (n_pre + 1 ) rr_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_m )
.

Definition transpose_partial_solve_wit_9 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m)) = n_pre)) (PreH13 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (u < n_pre) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (((fadj_row_pre + (u * sizeof(INT)))) # Int  |-> (Znth u fadj_row_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_row_pre u 0 (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
.

Definition transpose_partial_solve_wit_10 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (sum: Z) (m: Z) (u: Z) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (0 <= u)) (PreH3 : (u <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m)) = n_pre)) (PreH13 : ((Zlength (rr_m)) = (n_pre + 1 ))) (PreH14 : ((csr_lo (0) (rr_m)) = 0)) (PreH15 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : (AdjGraphValid g_low_level_spec )) (PreH19 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH20 : (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m )) (PreH21 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH22 : (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (u < n_pre) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((Zlength (rr_m)) = (n_pre + 1 )) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (transpose_scatter_inv n_pre m (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre (csr_lo (u) (fadj_row_l_low_level_spec)) fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (((fadj_row_pre + ((u + 1 ) * sizeof(INT)))) # Int  |-> (Znth (u + 1 ) fadj_row_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_row_pre (u + 1 ) 0 (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
.

Definition transpose_partial_solve_wit_11 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (j: Z) (hi: Z) (lo: Z) (rr_m: (@list Z)) (pos_m: (@list Z)) (rc_m: (@list Z)) (sum: Z) (m: Z) (u: Z) (PreH1 : (j < hi)) (PreH2 : (0 <= u)) (PreH3 : (u < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= m)) (PreH7 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH8 : (m <= 2147483646)) (PreH9 : (sum = m)) (PreH10 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH11 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH12 : ((Zlength (pos_m)) = n_pre)) (PreH13 : ((csr_lo (0) (rr_m)) = 0)) (PreH14 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH16 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH17 : (AdjGraphValid g_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH20 : ((Zlength (pos_m)) = n_pre)) (PreH21 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH22 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH23 : (0 <= lo)) (PreH24 : (lo <= j)) (PreH25 : (j <= hi)) (PreH26 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH27 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m )) (PreH28 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH29 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (j < hi) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ (lo = (csr_lo (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= j) ” 
  &&  “ (j <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (((fadj_col_pre + (j * sizeof(INT)))) # Int  |-> (Znth j fadj_col_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_col_pre j 0 (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
.

Definition transpose_partial_solve_wit_12 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= v)) (PreH4 : (v < n_pre)) (PreH5 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= m)) (PreH11 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (m <= 2147483646)) (PreH13 : (sum = m)) (PreH14 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH16 : ((Zlength (pos_m)) = n_pre)) (PreH17 : ((csr_lo (0) (rr_m)) = 0)) (PreH18 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH20 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH21 : (AdjGraphValid g_low_level_spec )) (PreH22 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH23 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH24 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= j)) (PreH27 : (j <= hi)) (PreH28 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH29 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m )) (PreH30 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH31 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (0 <= j) ” 
  &&  “ (j < hi) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (j) (fadj_col_l_low_level_spec) (0))) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (lo = (csr_lo (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= j) ” 
  &&  “ (j <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (((pos_pre + (v * sizeof(INT)))) # Int  |-> (Znth v pos_m 0))
  **  (IntArray.missing_i pos_pre v 0 n_pre pos_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
.

Definition transpose_partial_solve_wit_13 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (0 <= j) ” 
  &&  “ (j < hi) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (p = (Znth (v) (pos_m) (0))) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (j) (fadj_col_l_low_level_spec) (0))) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (lo = (csr_lo (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= j) ” 
  &&  “ (j <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (((radj_col_pre + (p * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i radj_col_pre p 0 (m_of (fadj_row_l_low_level_spec)) rc_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
.

Definition transpose_partial_solve_wit_14 := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (radj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (rc_m: (@list Z)) (rr_m: (@list Z)) (pos_m: (@list Z)) (j: Z) (hi: Z) (p: Z) (v: Z) (u: Z) (m: Z) (sum: Z) (lo: Z) (PreH1 : (0 <= j)) (PreH2 : (j < hi)) (PreH3 : (0 <= p)) (PreH4 : (p < (m_of (fadj_row_l_low_level_spec)))) (PreH5 : (p = (Znth (v) (pos_m) (0)))) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (v = (Znth (j) (fadj_col_l_low_level_spec) (0)))) (PreH9 : (0 <= u)) (PreH10 : (u < n_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= m)) (PreH14 : (m = (m_of (fadj_row_l_low_level_spec)))) (PreH15 : (m <= 2147483646)) (PreH16 : (sum = m)) (PreH17 : ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec)))) (PreH18 : ((Zlength (radj_col_l_low_level_spec)) = m)) (PreH19 : ((Zlength (pos_m)) = n_pre)) (PreH20 : ((csr_lo (0) (rr_m)) = 0)) (PreH21 : (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH22 : ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0)) (PreH23 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH24 : (AdjGraphValid g_low_level_spec )) (PreH25 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH26 : (lo = (csr_lo (u) (fadj_row_l_low_level_spec)))) (PreH27 : (hi = (csr_hi (u) (fadj_row_l_low_level_spec)))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= j)) (PreH30 : (j <= hi)) (PreH31 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH32 : (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m )) (PreH33 : (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m )) (PreH34 : (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m )) ,
  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) (replace_Znth (p) (u) (rc_m)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
  **  (IntArray.full pos_pre n_pre pos_m )
|--
  “ (0 <= j) ” 
  &&  “ (j < hi) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (p = (Znth (v) (pos_m) (0))) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (j) (fadj_col_l_low_level_spec) (0))) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (sum = m) ” 
  &&  “ ((Zlength (rc_m)) = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m) ” 
  &&  “ ((Zlength (pos_m)) = n_pre) ” 
  &&  “ ((csr_lo (0) (rr_m)) = 0) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (lo = (csr_lo (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= j) ” 
  &&  “ (j <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (transpose_scatter_inv n_pre m j fadj_col_l_low_level_spec rr_m pos_m ) ” 
  &&  “ (transpose_scatter_rows n_pre m fadj_col_l_low_level_spec rr_m ) ” 
  &&  “ (transpose_scatter_contents g_low_level_spec n_pre j fadj_row_l_low_level_spec fadj_col_l_low_level_spec rr_m rc_m ) ”
  &&  (((pos_pre + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos_pre v 0 n_pre pos_m )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) (replace_Znth (p) (u) (rc_m)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) rr_m )
.

(*----- Function kosaraju -----*)

Definition kosaraju_safety_wit_1 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2147483646)) (PreH4 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH5 : (AdjGraphValid g_high_level_spec )) (PreH6 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH7 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH8 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH9 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "radj_row" ) )) # Ptr  |->_)
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  ((( &( "radj_col" ) )) # Ptr  |-> retval)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition kosaraju_safety_wit_2 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2147483646)) (PreH4 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH5 : (AdjGraphValid g_high_level_spec )) (PreH6 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH7 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH8 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH9 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "radj_row" ) )) # Ptr  |->_)
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  ((( &( "radj_col" ) )) # Ptr  |-> retval)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kosaraju_safety_wit_3 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (l_3: (@list Z)) (retval_3: Z) (l_4: (@list Z)) (retval_4: Z) (l_5: (@list Z)) (retval_5: Z) (l_6: (@list Z)) (retval_6: Z) (PreH1 : ((Zlength (l_6)) = n_pre)) (PreH2 : ((Zlength (l_5)) = n_pre)) (PreH3 : ((Zlength (l_4)) = n_pre)) (PreH4 : ((Zlength (l_3)) = n_pre)) (PreH5 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH6 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2147483646)) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH13 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH14 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "timer" ) )) # Int  |->_)
  **  (IntArray.full retval_6 n_pre l_6 )
  **  ((( &( "vis2" ) )) # Ptr  |-> retval_6)
  **  (IntArray.full retval_5 n_pre l_5 )
  **  ((( &( "fin" ) )) # Ptr  |-> retval_5)
  **  (IntArray.full retval_4 n_pre l_4 )
  **  ((( &( "vis1" ) )) # Ptr  |-> retval_4)
  **  (IntArray.full retval_3 n_pre l_3 )
  **  ((( &( "pos" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> retval_2)
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  ((( &( "radj_col" ) )) # Ptr  |-> retval)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_safety_wit_4 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (vis1_l0: (@list Z)) (fin_l0: (@list Z)) (vis2_l0: (@list Z)) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (timer = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_l0)) = n_pre)) (PreH7 : ((Zlength (radj_col_l0)) = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : ((Zlength (radj_row_l0)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pos_l0)) = n_pre)) (PreH10 : ((Zlength (vis1_l0)) = n_pre)) (PreH11 : ((Zlength (fin_l0)) = n_pre)) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "u" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_l0 )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_l0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_safety_wit_5 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vm: (@list Z)) (vm2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm) (0)) = 0))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col m radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vm )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vm2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_safety_wit_6 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vm: (@list Z)) (vm2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm) (0)) = 0))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full vis1 n_pre (replace_Znth (u) (0) (vm)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col m radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vm2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_safety_wit_7 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vm: (@list Z)) (vm2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm) (0)) = 0))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full vis2 n_pre (replace_Znth (u) (0) (vm2)) )
  **  (IntArray.full vis1 n_pre (replace_Znth (u) (0) (vm)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col m radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
|--
  “ ((u + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u + 1 )) ”
.

Definition kosaraju_safety_wit_8 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (pos_l_: (@list Z)) (radj_col_l_: (@list Z)) (radj_row_l_: (@list Z)) (PreH1 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_ radj_row_l_ n_pre )) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (timer = 0)) (PreH6 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH7 : ((Zlength (vis1_zero)) = n_pre)) (PreH8 : ((Zlength (vis2_zero)) = n_pre)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0))) (PreH10 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH11 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH12 : (AdjGraphValid g_high_level_spec )) (PreH13 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH14 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "u" ) )) # Int  |->_)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l_ )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_ )
  **  (IntArray.full pos n_pre pos_l_ )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_safety_wit_9 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u)) (PreH7 : (u <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH13 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (IntArray.full vis1 n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_safety_wit_10 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (u: Z) (m: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_m_: (@list Z)) (fin_m_: (@list Z)) (timer_: Z) (PreH1 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m_) (fin_m_) (timer_)) (dfs_finish_schedule (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_zero)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= u)) (PreH11 : (u < n_pre)) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m_ fin_m_ vis1_zero fin_l0 timer_ n_pre (u + 1 ) )) (PreH13 : (dfs1_finish_prefix_marked fin_m_ vis1_m_ timer_ n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH15 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m_ fin_m_ timer_ )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer_)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m_ )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m_ )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ ((u + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u + 1 )) ”
.

Definition kosaraju_safety_wit_11 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) <> 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (IntArray.full vis1 n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ ((u + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u + 1 )) ”
.

Definition kosaraju_safety_wit_12 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (pos_l: (@list Z)) (radj_row: Z) (radj_col: Z) (radj_col_l: (@list Z)) (fin_m: (@list Z)) (timer: Z) (vis1_m: (@list Z)) (u: Z) (radj_row_l: (@list Z)) (m: Z) (PreH1 : (u >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u)) (PreH7 : (u <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH13 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_safety_wit_13 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (radj_col_l: (@list Z)) (sid_m: (@list Z)) (vis2_m: (@list Z)) (vis1_m: (@list Z)) (order_l: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l: (@list Z)) (m: Z) (PreH1 : (i < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m)) = n_pre)) (PreH9 : ((Zlength (order_l)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_m)) = n_pre)) (PreH12 : ((Zlength (sid_m)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "timer" ) )) # Int  |-> timer_m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_m )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre order_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (((n_pre - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre - 1 ) - i )) ”
.

Definition kosaraju_safety_wit_14 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (radj_col_l: (@list Z)) (sid_m: (@list Z)) (vis2_m: (@list Z)) (vis1_m: (@list Z)) (order_l: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l: (@list Z)) (m: Z) (PreH1 : (i < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m)) = n_pre)) (PreH9 : ((Zlength (order_l)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_m)) = n_pre)) (PreH12 : ((Zlength (sid_m)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "timer" ) )) # Int  |-> timer_m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_m )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre order_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition kosaraju_safety_wit_15 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (radj_col_l: (@list Z)) (sid_m: (@list Z)) (vis2_m: (@list Z)) (vis1_m: (@list Z)) (order_l: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l: (@list Z)) (m: Z) (PreH1 : (i < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m)) = n_pre)) (PreH9 : ((Zlength (order_l)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_m)) = n_pre)) (PreH12 : ((Zlength (sid_m)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "timer" ) )) # Int  |-> timer_m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_m )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre order_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kosaraju_safety_wit_16 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (radj_col_l: (@list Z)) (sid_m: (@list Z)) (vis2_m: (@list Z)) (vis1_m: (@list Z)) (order_l: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l: (@list Z)) (m: Z) (PreH1 : (i < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m)) = n_pre)) (PreH9 : ((Zlength (order_l)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_m)) = n_pre)) (PreH12 : ((Zlength (sid_m)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  (IntArray.full pos n_pre (replace_Znth (i) ((Znth ((n_pre - 1 ) - i ) fin_m 0)) (order_l)) )
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "timer" ) )) # Int  |-> timer_m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_m )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition kosaraju_safety_wit_17 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (radj_col_l: (@list Z)) (sid_m: (@list Z)) (vis2_m: (@list Z)) (vis1_m: (@list Z)) (order_l: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l: (@list Z)) (m: Z) (PreH1 : (i >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m)) = n_pre)) (PreH9 : ((Zlength (order_l)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_m)) = n_pre)) (PreH12 : ((Zlength (sid_m)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer_m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_m )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre order_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_safety_wit_18 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (m = (m_of (radj_row_l)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= root)) (PreH8 : (root < n_pre)) (PreH9 : (root = (Znth (k) (order_l) (0)))) (PreH10 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH11 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH12 : (AdjGraphValid g_high_level_spec )) (PreH13 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH14 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH16 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  (IntArray.full vis2 n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  ((( &( "timer" ) )) # Int  |-> timer_m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre order_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_safety_wit_19 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (sid_m1: (@list Z)) (root: Z) (m: Z) (k: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (vis2_m_: (@list Z)) (sid_m_: (@list Z)) (PreH1 : (dfs2_high_level_post g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 vis2_m_ sid_m_ root root n_pre )) (PreH2 : (dfs2_phase2_post g_high_level_spec n_pre vis2_m sid_m1 vis2_m_ sid_m_ root )) (PreH3 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_ sid_m_ )) (PreH4 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH5 : (AdjGraphValid g_high_level_spec )) (PreH6 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH7 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH9 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH10 : (m = (m_of (radj_row_l)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (0 <= root)) (PreH16 : (root < n_pre)) (PreH17 : (root = (Znth (k) (order_l) (0)))) (PreH18 : ((Znth (root) (vis2_m) (0)) = 0)) (PreH19 : (sid_m1 = (replace_Znth (root) (root) (sid_m)))) (PreH20 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m_ sid_m_ timer_m n_pre (k + 1 ) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer_m)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_m_ )
  **  (IntArray.full sid_pre n_pre sid_m_ )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre order_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition kosaraju_safety_wit_20 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (PreH1 : ((Znth root vis2_m 0) <> 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  (IntArray.full vis2 n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "timer" ) )) # Int  |-> timer_m)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre order_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition kosaraju_entail_wit_1 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (l_3: (@list Z)) (retval_3: Z) (l_4: (@list Z)) (retval_4: Z) (l_5: (@list Z)) (retval_5: Z) (l_6: (@list Z)) (retval_6: Z) (PreH1 : ((Zlength (l_6)) = n_pre)) (PreH2 : ((Zlength (l_5)) = n_pre)) (PreH3 : ((Zlength (l_4)) = n_pre)) (PreH4 : ((Zlength (l_3)) = n_pre)) (PreH5 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH6 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2147483646)) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH13 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH14 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  (IntArray.full retval_6 n_pre l_6 )
  **  (IntArray.full retval_5 n_pre l_5 )
  **  (IntArray.full retval_4 n_pre l_4 )
  **  (IntArray.full retval_3 n_pre l_3 )
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  EX (fin_l0: (@list Z))  (vis1_l0: (@list Z))  (pos_l0: (@list Z))  (radj_row_l0: (@list Z))  (radj_col_l0: (@list Z))  (vis2_l0: (@list Z)) ,
  “ ((Znth n_pre fadj_row_l_high_level_spec 0) = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis2_l0)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l0)) = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ ((Zlength (radj_row_l0)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pos_l0)) = n_pre) ” 
  &&  “ ((Zlength (vis1_l0)) = n_pre) ” 
  &&  “ ((Zlength (fin_l0)) = n_pre) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full retval (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  (IntArray.full retval_2 (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full retval_3 n_pre pos_l0 )
  **  (IntArray.full retval_4 n_pre vis1_l0 )
  **  (IntArray.full retval_5 n_pre fin_l0 )
  **  (IntArray.full retval_6 n_pre vis2_l0 )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (l_3: (@list Z)) (l_4: (@list Z)) (l_5: (@list Z)) (l_6: (@list Z)) (PreH1 : ((Zlength (l_6)) = n_pre)) (PreH2 : ((Zlength (l_5)) = n_pre)) (PreH3 : ((Zlength (l_4)) = n_pre)) (PreH4 : ((Zlength (l_3)) = n_pre)) (PreH5 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH6 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 2147483646)) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH12 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH13 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH14 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
|--
  EX (radj_col_l0: (@list Z)) ,
  “ ((Znth n_pre fadj_row_l_high_level_spec 0) = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (l_6)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l0)) = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ ((Zlength (l_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (l_3)) = n_pre) ” 
  &&  “ ((Zlength (l_4)) = n_pre) ” 
  &&  “ ((Zlength (l_5)) = n_pre) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (IntArray.full retval (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
).

Definition kosaraju_entail_wit_2 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (vis1_l0: (@list Z)) (fin_l0: (@list Z)) (vis2_l0: (@list Z)) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (timer = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_l0)) = n_pre)) (PreH7 : ((Zlength (radj_col_l0)) = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : ((Zlength (radj_row_l0)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pos_l0)) = n_pre)) (PreH10 : ((Zlength (vis1_l0)) = n_pre)) (PreH11 : ((Zlength (fin_l0)) = n_pre)) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full vis1 n_pre vis1_l0 )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vis2_l0 )
|--
  EX (vm2: (@list Z))  (vm: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (timer = 0) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (fin_l0)) = n_pre) ” 
  &&  “ ((Zlength (vm)) = n_pre) ” 
  &&  “ ((Zlength (vm2)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 0)) -> ((Znth (i) (vm) (0)) = 0)) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 0)) -> ((Znth (i_2) (vm2) (0)) = 0)) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col m radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full vis1 n_pre vm )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vm2 )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (timer: Z) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (vis1_l0: (@list Z)) (fin_l0: (@list Z)) (vis2_l0: (@list Z)) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (timer = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_l0)) = n_pre)) (PreH7 : ((Zlength (radj_col_l0)) = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : ((Zlength (radj_row_l0)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pos_l0)) = n_pre)) (PreH10 : ((Zlength (vis1_l0)) = n_pre)) (PreH11 : ((Zlength (fin_l0)) = n_pre)) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  TT && emp 
|--
  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 0)) -> ((Znth (i_2) (vis2_l0) (0)) = 0)) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 0)) -> ((Znth (i) (vis1_l0) (0)) = 0)) ”
  &&  emp
).

Definition kosaraju_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (timer: Z) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (vis1_l0: (@list Z)) (fin_l0: (@list Z)) (vis2_l0: (@list Z)) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (timer = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_l0)) = n_pre)) (PreH7 : ((Zlength (radj_col_l0)) = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : ((Zlength (radj_row_l0)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pos_l0)) = n_pre)) (PreH10 : ((Zlength (vis1_l0)) = n_pre)) (PreH11 : ((Zlength (fin_l0)) = n_pre)) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 0)) -> ((Znth (i_2) (vis2_l0) (0)) = 0))
.

Definition kosaraju_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (timer: Z) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (vis1_l0: (@list Z)) (fin_l0: (@list Z)) (vis2_l0: (@list Z)) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (timer = 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_l0)) = n_pre)) (PreH7 : ((Zlength (radj_col_l0)) = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : ((Zlength (radj_row_l0)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pos_l0)) = n_pre)) (PreH10 : ((Zlength (vis1_l0)) = n_pre)) (PreH11 : ((Zlength (fin_l0)) = n_pre)) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  forall (i: Z) , (((0 <= i) /\ (i < 0)) -> ((Znth (i) (vis1_l0) (0)) = 0))
.

Definition kosaraju_entail_wit_3 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vm_2: (@list Z)) (vm2_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm_2)) = n_pre)) (PreH11 : ((Zlength (vm2_2)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm_2) (0)) = 0))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2_2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full vis2 n_pre (replace_Znth (u) (0) (vm2_2)) )
  **  (IntArray.full vis1 n_pre (replace_Znth (u) (0) (vm_2)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col m radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full fin n_pre fin_l0 )
|--
  EX (vm2: (@list Z))  (vm: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= (u + 1 )) ” 
  &&  “ ((u + 1 ) <= n_pre) ” 
  &&  “ (timer = 0) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (fin_l0)) = n_pre) ” 
  &&  “ ((Zlength (vm)) = n_pre) ” 
  &&  “ ((Zlength (vm2)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (u + 1 ))) -> ((Znth (i) (vm) (0)) = 0)) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (u + 1 ))) -> ((Znth (i_2) (vm2) (0)) = 0)) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col m radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full vis1 n_pre vm )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vm2 )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (timer: Z) (u: Z) (m: Z) (vm_2: (@list Z)) (vm2_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm_2)) = n_pre)) (PreH11 : ((Zlength (vm2_2)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm_2) (0)) = 0))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2_2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (u) (0) (vm2_2)))) = n_pre) ” 
  &&  “ ((Zlength ((replace_Znth (u) (0) (vm_2)))) = n_pre) ”
  &&  emp
).

Definition kosaraju_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (timer: Z) (u: Z) (m: Z) (vm_2: (@list Z)) (vm2_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm_2)) = n_pre)) (PreH11 : ((Zlength (vm2_2)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm_2) (0)) = 0))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2_2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((Zlength ((replace_Znth (u) (0) (vm2_2)))) = n_pre)
.

Definition kosaraju_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (timer: Z) (u: Z) (m: Z) (vm_2: (@list Z)) (vm2_2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm_2)) = n_pre)) (PreH11 : ((Zlength (vm2_2)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm_2) (0)) = 0))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2_2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((Zlength ((replace_Znth (u) (0) (vm_2)))) = n_pre)
.

Definition kosaraju_entail_wit_4 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (vm2: (@list Z)) (vm: (@list Z)) (timer: Z) (u: Z) (m: Z) (PreH1 : (u >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < u)) -> ((Znth (i_3) (vm) (0)) = 0))) (PreH13 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < u)) -> ((Znth (i_4) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col m radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full vis1 n_pre vm )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vm2 )
|--
  EX (vis2_zero: (@list Z))  (vis1_zero: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (timer = 0) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis1_zero)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0)) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0)) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vis2_zero )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (fin_l0: (@list Z)) (radj_col: Z) (vm2: (@list Z)) (vm: (@list Z)) (timer: Z) (u: Z) (m: Z) (PreH1 : (u >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < u)) -> ((Znth (i_3) (vm) (0)) = 0))) (PreH13 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < u)) -> ((Znth (i_4) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full radj_col m radj_col_l0 )
|--
  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vm2) (0)) = 0)) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vm) (0)) = 0)) ”
  &&  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
).

Definition kosaraju_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (fin_l0: (@list Z)) (radj_col: Z) (vm2: (@list Z)) (vm: (@list Z)) (timer: Z) (u: Z) (m: Z) (PreH1 : (u >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < u)) -> ((Znth (i_3) (vm) (0)) = 0))) (PreH13 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < u)) -> ((Znth (i_4) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full radj_col m radj_col_l0 )
|--
  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vm2) (0)) = 0)) ”
.

Definition kosaraju_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (fin_l0: (@list Z)) (radj_col: Z) (vm2: (@list Z)) (vm: (@list Z)) (timer: Z) (u: Z) (m: Z) (PreH1 : (u >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < u)) -> ((Znth (i_3) (vm) (0)) = 0))) (PreH13 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < u)) -> ((Znth (i_4) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full radj_col m radj_col_l0 )
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vm) (0)) = 0)) ”
.

Definition kosaraju_entail_wit_4_split_goal_spatial := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (fin_l0: (@list Z)) (radj_col: Z) (vm2: (@list Z)) (vm: (@list Z)) (timer: Z) (u: Z) (m: Z) (PreH1 : (u >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < u)) -> ((Znth (i_3) (vm) (0)) = 0))) (PreH13 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < u)) -> ((Znth (i_4) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full radj_col m radj_col_l0 )
|--
  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
.

Definition kosaraju_entail_wit_5 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (pos_l_: (@list Z)) (radj_col_l_: (@list Z)) (radj_row_l_: (@list Z)) (PreH1 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_ radj_row_l_ n_pre )) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (timer = 0)) (PreH6 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH7 : ((Zlength (vis1_zero)) = n_pre)) (PreH8 : ((Zlength (vis2_zero)) = n_pre)) (PreH9 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis1_zero) (0)) = 0))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((Znth (i_3) (vis2_zero) (0)) = 0))) (PreH11 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH12 : (AdjGraphValid g_high_level_spec )) (PreH13 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH14 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l_ )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_ )
  **  (IntArray.full pos n_pre pos_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  EX (pos_l: (@list Z))  (radj_col_l: (@list Z))  (fin_m: (@list Z))  (vis1_m: (@list Z))  (radj_row_l: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis1_m)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre 0 ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre ) ” 
  &&  “ (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_zero )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l_: (@list Z)) (radj_row_l_: (@list Z)) (PreH1 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_ radj_row_l_ n_pre )) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (timer = 0)) (PreH6 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH7 : ((Zlength (vis1_zero)) = n_pre)) (PreH8 : ((Zlength (vis2_zero)) = n_pre)) (PreH9 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis1_zero) (0)) = 0))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((Znth (i_3) (vis2_zero) (0)) = 0))) (PreH11 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH12 : (AdjGraphValid g_high_level_spec )) (PreH13 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH14 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l_ )
|--
  EX (radj_col_l: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l_))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis1_zero)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l_ vis1_zero fin_l0 vis1_zero fin_l0 timer n_pre 0 ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_l0 vis1_zero timer n_pre ) ” 
  &&  “ (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l_ n_pre ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ”
  &&  (IntArray.full radj_col (m_of (radj_row_l_)) radj_col_l )
).

Definition kosaraju_entail_wit_6 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) = 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre ) ” 
  &&  “ (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_high_level_spec radj_col_l radj_row_l ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer ) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) ) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u) (vis1_m) (0)) = 0) ” 
  &&  “ (0 <= timer) ” 
  &&  “ (timer <= (count_nonzero (vis1_m))) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_zero )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) = 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  TT && emp 
|--
  “ (timer <= (count_nonzero (vis1_m))) ” 
  &&  “ (0 <= timer) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) ) ” 
  &&  “ (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer ) ” 
  &&  “ (csr1_faithful g_high_level_spec radj_col_l radj_row_l ) ” 
  &&  “ (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ”
  &&  emp
).

Definition kosaraju_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) = 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (timer <= (count_nonzero (vis1_m)))
.

Definition kosaraju_entail_wit_6_split_goal_2 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) = 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (0 <= timer)
.

Definition kosaraju_entail_wit_6_split_goal_3 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) = 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )
.

Definition kosaraju_entail_wit_6_split_goal_4 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) = 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )
.

Definition kosaraju_entail_wit_6_split_goal_5 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) = 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (csr1_faithful g_high_level_spec radj_col_l radj_row_l )
.

Definition kosaraju_entail_wit_6_split_goal_6 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) = 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )
.

Definition kosaraju_entail_wit_6_split_goal_7 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : ((Znth u vis1_m 0) = 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))
.

Definition kosaraju_entail_wit_7 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (m: Z) (timer: Z) (u: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_high_level_spec vis1_m fin_m timer vis1_l_ fin_l_ timer_v_ u )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 )))) (tt)) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m vis1_l_ timer timer_v_ )) (PreH11 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_m) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0))) (PreH12 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH13 : (m = (m_of (radj_row_l)))) (PreH14 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH15 : ((Zlength (vis2_zero)) = n_pre)) (PreH16 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH17 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH18 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )) (PreH19 : (csr1_faithful g_high_level_spec radj_col_l radj_row_l )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH21 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )) (PreH22 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH23 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH24 : (0 <= u)) (PreH25 : (u < n_pre)) (PreH26 : (n_pre <= 2147483646)) (PreH27 : ((Znth (u) (vis1_m) (0)) = 0)) (PreH28 : (0 <= timer)) (PreH29 : (timer <= (count_nonzero (vis1_m)))) (PreH30 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH31 : (AdjGraphValid g_high_level_spec )) (PreH32 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH33 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full vis1 n_pre vis1_l_ )
  **  (IntArray.full fin n_pre fin_l_ )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  EX (vis1_m_: (@list Z))  (fin_m_: (@list Z)) ,
  “ (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m_) (fin_m_) (timer_v_)) (dfs_finish_schedule (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m_ fin_m_ vis1_zero fin_l0 timer_v_ n_pre (u + 1 ) ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m_ vis1_m_ timer_v_ n_pre ) ” 
  &&  “ (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre ) ” 
  &&  “ (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m_ fin_m_ timer_v_ ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis1 n_pre vis1_m_ )
  **  (IntArray.full fin n_pre fin_m_ )
  **  (IntArray.full vis2 n_pre vis2_zero )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (timer: Z) (u: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_high_level_spec vis1_m fin_m timer vis1_l_ fin_l_ timer_v_ u )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 )))) (tt)) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m vis1_l_ timer timer_v_ )) (PreH11 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_m) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0))) (PreH12 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH13 : (m = (m_of (radj_row_l)))) (PreH14 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH15 : ((Zlength (vis2_zero)) = n_pre)) (PreH16 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH17 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH18 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )) (PreH19 : (csr1_faithful g_high_level_spec radj_col_l radj_row_l )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH21 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )) (PreH22 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH23 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH24 : (0 <= u)) (PreH25 : (u < n_pre)) (PreH26 : (n_pre <= 2147483646)) (PreH27 : ((Znth (u) (vis1_m) (0)) = 0)) (PreH28 : (0 <= timer)) (PreH29 : (timer <= (count_nonzero (vis1_m)))) (PreH30 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH31 : (AdjGraphValid g_high_level_spec )) (PreH32 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH33 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  TT && emp 
|--
  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ vis1_zero fin_l0 timer_v_ n_pre (u + 1 ) ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_l_) (fin_l_) (timer_v_)) (dfs_finish_schedule (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) ) ”
  &&  emp
).

Definition kosaraju_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (timer: Z) (u: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_high_level_spec vis1_m fin_m timer vis1_l_ fin_l_ timer_v_ u )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 )))) (tt)) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m vis1_l_ timer timer_v_ )) (PreH11 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_m) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0))) (PreH12 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH13 : (m = (m_of (radj_row_l)))) (PreH14 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH15 : ((Zlength (vis2_zero)) = n_pre)) (PreH16 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH17 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH18 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )) (PreH19 : (csr1_faithful g_high_level_spec radj_col_l radj_row_l )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH21 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )) (PreH22 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH23 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH24 : (0 <= u)) (PreH25 : (u < n_pre)) (PreH26 : (n_pre <= 2147483646)) (PreH27 : ((Znth (u) (vis1_m) (0)) = 0)) (PreH28 : (0 <= timer)) (PreH29 : (timer <= (count_nonzero (vis1_m)))) (PreH30 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH31 : (AdjGraphValid g_high_level_spec )) (PreH32 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH33 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ vis1_zero fin_l0 timer_v_ n_pre (u + 1 ) )
.

Definition kosaraju_entail_wit_7_split_goal_2 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (timer: Z) (u: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_high_level_spec vis1_m fin_m timer vis1_l_ fin_l_ timer_v_ u )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 )))) (tt)) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m vis1_l_ timer timer_v_ )) (PreH11 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_m) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0))) (PreH12 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH13 : (m = (m_of (radj_row_l)))) (PreH14 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH15 : ((Zlength (vis2_zero)) = n_pre)) (PreH16 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH17 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH18 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )) (PreH19 : (csr1_faithful g_high_level_spec radj_col_l radj_row_l )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH21 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )) (PreH22 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH23 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH24 : (0 <= u)) (PreH25 : (u < n_pre)) (PreH26 : (n_pre <= 2147483646)) (PreH27 : ((Znth (u) (vis1_m) (0)) = 0)) (PreH28 : (0 <= timer)) (PreH29 : (timer <= (count_nonzero (vis1_m)))) (PreH30 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH31 : (AdjGraphValid g_high_level_spec )) (PreH32 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH33 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))
.

Definition kosaraju_entail_wit_7_split_goal_3 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (timer: Z) (u: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_l_ fin_l_ timer_v_ )) (PreH4 : (dfs1_sequence_extension g_high_level_spec vis1_m fin_m timer vis1_l_ fin_l_ timer_v_ u )) (PreH5 : (dfs1_finish_prefix_marked fin_l_ vis1_l_ timer_v_ n_pre )) (PreH6 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 )))) (tt)) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH7 : (0 <= timer_v_)) (PreH8 : (timer_v_ <= (count_nonzero (vis1_l_)))) (PreH9 : (timer <= timer_v_)) (PreH10 : (dfs1_timer_surplus_preserved vis1_m vis1_l_ timer timer_v_ )) (PreH11 : forall (w: Z) , ((((0 <= w) /\ (w < n_pre)) /\ ((Znth (w) (vis1_m) (0)) <> 0)) -> ((Znth (w) (vis1_l_) (0)) <> 0))) (PreH12 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH13 : (m = (m_of (radj_row_l)))) (PreH14 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH15 : ((Zlength (vis2_zero)) = n_pre)) (PreH16 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH17 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH18 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )) (PreH19 : (csr1_faithful g_high_level_spec radj_col_l radj_row_l )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH21 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )) (PreH22 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH23 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH24 : (0 <= u)) (PreH25 : (u < n_pre)) (PreH26 : (n_pre <= 2147483646)) (PreH27 : ((Znth (u) (vis1_m) (0)) = 0)) (PreH28 : (0 <= timer)) (PreH29 : (timer <= (count_nonzero (vis1_m)))) (PreH30 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH31 : (AdjGraphValid g_high_level_spec )) (PreH32 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH33 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_l_) (fin_l_) (timer_v_)) (dfs_finish_schedule (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )
.

Definition kosaraju_entail_wit_8_1 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l_2: (@list Z)) (radj_row_l_2: (@list Z)) (pos_l_2: (@list Z)) (u: Z) (m: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_m_: (@list Z)) (fin_m_: (@list Z)) (timer_: Z) (PreH1 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l_2) (radj_row_l_2) (vis1_m_) (fin_m_) (timer_)) (dfs_finish_schedule (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l_2) (radj_row_l_2) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l_2)))) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_zero)) = n_pre)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= u)) (PreH11 : (u < n_pre)) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_ fin_m_ vis1_zero fin_l0 timer_ n_pre (u + 1 ) )) (PreH13 : (dfs1_finish_prefix_marked fin_m_ vis1_m_ timer_ n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_ fin_m_ timer_ )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l_2)) radj_col_l_2 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_2 )
  **  (IntArray.full pos n_pre pos_l_2 )
  **  (IntArray.full vis1 n_pre vis1_m_ )
  **  (IntArray.full fin n_pre fin_m_ )
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  EX (pos_l: (@list Z))  (radj_col_l: (@list Z))  (fin_m: (@list Z))  (vis1_m: (@list Z))  (radj_row_l: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= (u + 1 )) ” 
  &&  “ ((u + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis1_m)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_ n_pre (u + 1 ) ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer_ n_pre ) ” 
  &&  “ (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_zero )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l_2: (@list Z)) (radj_row_l_2: (@list Z)) (u: Z) (m: Z) (vis1_m_: (@list Z)) (fin_m_: (@list Z)) (timer_: Z) (PreH1 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l_2) (radj_row_l_2) (vis1_m_) (fin_m_) (timer_)) (dfs_finish_schedule (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l_2) (radj_row_l_2) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l_2)))) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_zero)) = n_pre)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= u)) (PreH11 : (u < n_pre)) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_ fin_m_ vis1_zero fin_l0 timer_ n_pre (u + 1 ) )) (PreH13 : (dfs1_finish_prefix_marked fin_m_ vis1_m_ timer_ n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_ fin_m_ timer_ )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  TT && emp 
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ ((Zlength (vis1_m_)) = n_pre) ”
  &&  emp
).

Definition kosaraju_entail_wit_8_1_split_goal_1 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l_2: (@list Z)) (radj_row_l_2: (@list Z)) (u: Z) (m: Z) (vis1_m_: (@list Z)) (fin_m_: (@list Z)) (timer_: Z) (PreH1 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l_2) (radj_row_l_2) (vis1_m_) (fin_m_) (timer_)) (dfs_finish_schedule (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l_2) (radj_row_l_2) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l_2)))) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_zero)) = n_pre)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= u)) (PreH11 : (u < n_pre)) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_ fin_m_ vis1_zero fin_l0 timer_ n_pre (u + 1 ) )) (PreH13 : (dfs1_finish_prefix_marked fin_m_ vis1_m_ timer_ n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_ fin_m_ timer_ )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))
.

Definition kosaraju_entail_wit_8_1_split_goal_2 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l_2: (@list Z)) (radj_row_l_2: (@list Z)) (u: Z) (m: Z) (vis1_m_: (@list Z)) (fin_m_: (@list Z)) (timer_: Z) (PreH1 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l_2) (radj_row_l_2) (vis1_m_) (fin_m_) (timer_)) (dfs_finish_schedule (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l_2) (radj_row_l_2) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH2 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l_2)))) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis2_zero)) = n_pre)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (0 <= u)) (PreH11 : (u < n_pre)) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_ fin_m_ vis1_zero fin_l0 timer_ n_pre (u + 1 ) )) (PreH13 : (dfs1_finish_prefix_marked fin_m_ vis1_m_ timer_ n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_ fin_m_ timer_ )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH19 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((Zlength (vis1_m_)) = n_pre)
.

Definition kosaraju_entail_wit_8_2 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (radj_col_l_2: (@list Z)) (radj_row_l_2: (@list Z)) (pos_l_2: (@list Z)) (PreH1 : ((Znth u vis1_m_2 0) <> 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l_2)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m_2)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (IntArray.full vis1 n_pre vis1_m_2 )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l_2)) radj_col_l_2 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_2 )
  **  (IntArray.full pos n_pre pos_l_2 )
  **  (IntArray.full fin n_pre fin_m_2 )
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  EX (pos_l: (@list Z))  (radj_col_l: (@list Z))  (fin_m: (@list Z))  (vis1_m: (@list Z))  (radj_row_l: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= (u + 1 )) ” 
  &&  “ ((u + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis1_m)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre (u + 1 ) ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre ) ” 
  &&  “ (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_zero )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (radj_col_l_2: (@list Z)) (radj_row_l_2: (@list Z)) (PreH1 : ((Znth u vis1_m_2 0) <> 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l_2)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m_2)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  TT && emp 
|--
  “ (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre (u + 1 ) ) ”
  &&  emp
).

Definition kosaraju_entail_wit_8_2_split_goal_1 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (timer: Z) (u: Z) (m: Z) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (radj_col_l_2: (@list Z)) (radj_row_l_2: (@list Z)) (PreH1 : ((Znth u vis1_m_2 0) <> 0)) (PreH2 : (u < n_pre)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l_2)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (0 <= u)) (PreH8 : (u <= n_pre)) (PreH9 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH10 : ((Zlength (vis1_m_2)) = n_pre)) (PreH11 : ((Zlength (vis2_zero)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH13 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u )) (PreH14 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH15 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH19 : (AdjGraphValid g_high_level_spec )) (PreH20 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre (u + 1 ) )
.

Definition kosaraju_entail_wit_9 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (pos_l: (@list Z)) (radj_row: Z) (radj_col: Z) (radj_col_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer: Z) (vis1_m_2: (@list Z)) (u_2: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (u_2 >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u_2)) (PreH7 : (u_2 <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m_2)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u_2 )) (PreH13 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l_2)) radj_col_l_2 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_2 )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis1 n_pre vis1_m_2 )
  **  (IntArray.full fin n_pre fin_m_2 )
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  EX (radj_col_l: (@list Z))  (sid_m: (@list Z))  (vis2_m: (@list Z))  (vis1_m: (@list Z))  (order_l: (@list Z))  (fin_m: (@list Z))  (radj_row_l: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (fin_m)) = n_pre) ” 
  &&  “ ((Zlength (order_l)) = n_pre) ” 
  &&  “ ((Zlength (vis1_m)) = n_pre) ” 
  &&  “ ((Zlength (vis2_m)) = n_pre) ” 
  &&  “ ((Zlength (sid_m)) = n_pre) ” 
  &&  “ forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0)) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < 0)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0)))) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre n_pre ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
) \/
(
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (pos_l: (@list Z)) (radj_col_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer: Z) (vis1_m_2: (@list Z)) (u_2: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (u_2 >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u_2)) (PreH7 : (u_2 <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m_2)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u_2 )) (PreH13 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  TT && emp 
|--
  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_zero sid_l_high_level_spec ) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre n_pre ) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < 0)) -> ((Znth (u) (pos_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m_2) (0)))) ” 
  &&  “ forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_zero) (0)) = 0)) ” 
  &&  “ ((Zlength (pos_l)) = n_pre) ” 
  &&  “ ((Zlength (fin_m_2)) = n_pre) ”
  &&  emp
).

Definition kosaraju_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer: Z) (vis1_m_2: (@list Z)) (u_2: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (u_2 >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u_2)) (PreH7 : (u_2 <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m_2)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u_2 )) (PreH13 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_zero sid_l_high_level_spec )
.

Definition kosaraju_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer: Z) (vis1_m_2: (@list Z)) (u_2: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (u_2 >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u_2)) (PreH7 : (u_2 <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m_2)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u_2 )) (PreH13 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre n_pre )
.

Definition kosaraju_entail_wit_9_split_goal_3 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (pos_l: (@list Z)) (radj_col_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer: Z) (vis1_m_2: (@list Z)) (u_2: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (u_2 >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u_2)) (PreH7 : (u_2 <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m_2)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u_2 )) (PreH13 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  forall (u: Z) , (((0 <= u) /\ (u < 0)) -> ((Znth (u) (pos_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m_2) (0))))
.

Definition kosaraju_entail_wit_9_split_goal_4 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer: Z) (vis1_m_2: (@list Z)) (u_2: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (u_2 >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u_2)) (PreH7 : (u_2 <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m_2)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u_2 )) (PreH13 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_zero) (0)) = 0))
.

Definition kosaraju_entail_wit_9_split_goal_5 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (pos_l: (@list Z)) (radj_col_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer: Z) (vis1_m_2: (@list Z)) (u_2: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (u_2 >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u_2)) (PreH7 : (u_2 <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m_2)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u_2 )) (PreH13 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  ((Zlength (pos_l)) = n_pre)
.

Definition kosaraju_entail_wit_9_split_goal_6 := 
forall (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (radj_col_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer: Z) (vis1_m_2: (@list Z)) (u_2: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (u_2 >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u_2)) (PreH7 : (u_2 <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m_2)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer n_pre u_2 )) (PreH13 : (dfs1_finish_prefix_marked fin_m_2 vis1_m_2 timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_2 radj_row_l_2 n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  ((Zlength (fin_m_2)) = n_pre)
.

Definition kosaraju_entail_wit_10 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (radj_col_l_2: (@list Z)) (sid_m_2: (@list Z)) (vis2_m_2: (@list Z)) (vis1_m_2: (@list Z)) (order_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (i < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m_2)) = n_pre)) (PreH9 : ((Zlength (order_l_2)) = n_pre)) (PreH10 : ((Zlength (vis1_m_2)) = n_pre)) (PreH11 : ((Zlength (vis2_m_2)) = n_pre)) (PreH12 : ((Zlength (sid_m_2)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m_2) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l_2) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m_2) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  (IntArray.full pos n_pre (replace_Znth (i) ((Znth ((n_pre - 1 ) - i ) fin_m_2 0)) (order_l_2)) )
  **  (IntArray.full fin n_pre fin_m_2 )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m_2 )
  **  (IntArray.full vis2 n_pre vis2_m_2 )
  **  (IntArray.full radj_col (m_of (radj_row_l_2)) radj_col_l_2 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_2 )
  **  (IntArray.full vis1 n_pre vis1_m_2 )
|--
  EX (radj_col_l: (@list Z))  (sid_m: (@list Z))  (vis2_m: (@list Z))  (vis1_m: (@list Z))  (order_l: (@list Z))  (fin_m: (@list Z))  (radj_row_l: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (fin_m)) = n_pre) ” 
  &&  “ ((Zlength (order_l)) = n_pre) ” 
  &&  “ ((Zlength (vis1_m)) = n_pre) ” 
  &&  “ ((Zlength (vis2_m)) = n_pre) ” 
  &&  “ ((Zlength (sid_m)) = n_pre) ” 
  &&  “ forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0)) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < (i + 1 ))) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0)))) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
) \/
(
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (radj_col_l_2: (@list Z)) (sid_m_2: (@list Z)) (vis2_m_2: (@list Z)) (vis1_m_2: (@list Z)) (order_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (i < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m_2)) = n_pre)) (PreH9 : ((Zlength (order_l_2)) = n_pre)) (PreH10 : ((Zlength (vis1_m_2)) = n_pre)) (PreH11 : ((Zlength (vis2_m_2)) = n_pre)) (PreH12 : ((Zlength (sid_m_2)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m_2) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l_2) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m_2) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (i) ((Znth ((n_pre - 1 ) - i ) fin_m_2 0)) (order_l_2)))) = n_pre) ”
  &&  emp
).

Definition kosaraju_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (radj_col_l_2: (@list Z)) (sid_m_2: (@list Z)) (vis2_m_2: (@list Z)) (vis1_m_2: (@list Z)) (order_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (i < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m_2)) = n_pre)) (PreH9 : ((Zlength (order_l_2)) = n_pre)) (PreH10 : ((Zlength (vis1_m_2)) = n_pre)) (PreH11 : ((Zlength (vis2_m_2)) = n_pre)) (PreH12 : ((Zlength (sid_m_2)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m_2) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l_2) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m_2) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  ((Zlength ((replace_Znth (i) ((Znth ((n_pre - 1 ) - i ) fin_m_2 0)) (order_l_2)))) = n_pre)
.

Definition kosaraju_entail_wit_11 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (radj_col_l_2: (@list Z)) (sid_m_2: (@list Z)) (vis2_m_2: (@list Z)) (vis1_m_2: (@list Z)) (order_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (i >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m_2)) = n_pre)) (PreH9 : ((Zlength (order_l_2)) = n_pre)) (PreH10 : ((Zlength (vis1_m_2)) = n_pre)) (PreH11 : ((Zlength (vis2_m_2)) = n_pre)) (PreH12 : ((Zlength (sid_m_2)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m_2) (0)) = 0))) (PreH14 : forall (u_2: Z) , (((0 <= u_2) /\ (u_2 < i)) -> ((Znth (u_2) (order_l_2) (0)) = (Znth (((n_pre - 1 ) - u_2 )) (fin_m_2) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m_2 )
  **  (IntArray.full vis2 n_pre vis2_m_2 )
  **  (IntArray.full fin n_pre fin_m_2 )
  **  (IntArray.full radj_col (m_of (radj_row_l_2)) radj_col_l_2 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_2 )
  **  (IntArray.full pos n_pre order_l_2 )
  **  (IntArray.full vis1 n_pre vis1_m_2 )
|--
  EX (radj_col_l: (@list Z))  (fin_m: (@list Z))  (order_l: (@list Z))  (vis1_m: (@list Z))  (vis2_m: (@list Z))  (sid_m: (@list Z))  (radj_row_l: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre 0 ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ” 
  &&  “ ((0 = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
) \/
(
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (radj_col_l_2: (@list Z)) (sid_m_2: (@list Z)) (vis2_m_2: (@list Z)) (vis1_m_2: (@list Z)) (order_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (i >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m_2)) = n_pre)) (PreH9 : ((Zlength (order_l_2)) = n_pre)) (PreH10 : ((Zlength (vis1_m_2)) = n_pre)) (PreH11 : ((Zlength (vis2_m_2)) = n_pre)) (PreH12 : ((Zlength (sid_m_2)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m_2) (0)) = 0))) (PreH14 : forall (u_2: Z) , (((0 <= u_2) /\ (u_2 < i)) -> ((Znth (u_2) (order_l_2) (0)) = (Znth (((n_pre - 1 ) - u_2 )) (fin_m_2) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  TT && emp 
|--
  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre 0 ) ”
  &&  emp
).

Definition kosaraju_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (radj_col_l_2: (@list Z)) (sid_m_2: (@list Z)) (vis2_m_2: (@list Z)) (vis1_m_2: (@list Z)) (order_l_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (i >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m_2)) = n_pre)) (PreH9 : ((Zlength (order_l_2)) = n_pre)) (PreH10 : ((Zlength (vis1_m_2)) = n_pre)) (PreH11 : ((Zlength (vis2_m_2)) = n_pre)) (PreH12 : ((Zlength (sid_m_2)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m_2) (0)) = 0))) (PreH14 : forall (u_2: Z) , (((0 <= u_2) /\ (u_2 < i)) -> ((Znth (u_2) (order_l_2) (0)) = (Znth (((n_pre - 1 ) - u_2 )) (fin_m_2) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l_2 radj_row_l_2 vis1_m_2 fin_m_2 vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre 0 )
.

Definition kosaraju_entail_wit_12 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (k: Z) (m: Z) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH14 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) (PreH15 : ((k = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))))) ,
  (IntArray.full pos n_pre order_l )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (Znth k order_l 0)) ” 
  &&  “ ((Znth k order_l 0) < n_pre) ” 
  &&  “ ((Znth k order_l 0) = (Znth (k) (order_l) (0))) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
) \/
(
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (k: Z) (m: Z) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_row_l: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH14 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) (PreH15 : ((k = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))))) ,
  TT && emp 
|--
  “ ((Znth k order_l 0) < n_pre) ” 
  &&  “ (0 <= (Znth k order_l 0)) ”
  &&  emp
).

Definition kosaraju_entail_wit_12_split_goal_1 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (k: Z) (m: Z) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_row_l: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH14 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) (PreH15 : ((k = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))))) ,
  ((Znth k order_l 0) < n_pre)
.

Definition kosaraju_entail_wit_12_split_goal_2 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (k: Z) (m: Z) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_row_l: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH14 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) (PreH15 : ((k = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))))) ,
  (0 <= (Znth k order_l 0))
.

Definition kosaraju_entail_wit_13 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (PreH1 : ((Znth root vis2_m 0) = 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  (IntArray.full sid_pre n_pre (replace_Znth (root) (root) (sid_m)) )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  EX (sid_m1: (@list Z)) ,
  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (root < n_pre) ” 
  &&  “ (root = (Znth (k) (order_l) (0))) ” 
  &&  “ ((Znth (root) (vis2_m) (0)) = 0) ” 
  &&  “ ((Znth (root) (sid_m1) (0)) = root) ” 
  &&  “ (sid_m1 = (replace_Znth (root) (root) (sid_m))) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m1 )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
) \/
(
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (PreH1 : ((Znth root vis2_m 0) = 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  TT && emp 
|--
  “ ((Znth (root) ((replace_Znth (root) (root) (sid_m))) (0)) = root) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m (replace_Znth (root) (root) (sid_m)) ) ”
  &&  emp
).

Definition kosaraju_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (PreH1 : ((Znth root vis2_m 0) = 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  ((Znth (root) ((replace_Znth (root) (root) (sid_m))) (0)) = root)
.

Definition kosaraju_entail_wit_13_split_goal_2 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (PreH1 : ((Znth root vis2_m 0) = 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m (replace_Znth (root) (root) (sid_m)) )
.

Definition kosaraju_entail_wit_14 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (sid_m1: (@list Z)) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (dfs2_high_level_post g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 vis2_l_ sid_l_ root root n_pre )) (PreH2 : (dfs2_phase2_post g_high_level_spec n_pre vis2_m sid_m1 vis2_l_ sid_l_ root )) (PreH3 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_l_ sid_l_ timer_m n_pre (k + 1 ) )) (PreH4 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_l_ sid_l_ )) (PreH5 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH6 : (AdjGraphValid g_high_level_spec )) (PreH7 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH8 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH9 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH10 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 )) (PreH11 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH12 : (AdjGraphValid g_high_level_spec )) (PreH13 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH14 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH16 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH17 : (m = (m_of (radj_row_l)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 2147483646)) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (0 <= root)) (PreH23 : (root < n_pre)) (PreH24 : (root = (Znth (k) (order_l) (0)))) (PreH25 : ((Znth (root) (vis2_m) (0)) = 0)) (PreH26 : ((Znth (root) (sid_m1) (0)) = root)) (PreH27 : (sid_m1 = (replace_Znth (root) (root) (sid_m)))) (PreH28 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full vis2 n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  EX (vis2_m_: (@list Z))  (sid_m_: (@list Z)) ,
  “ (dfs2_high_level_post g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 vis2_m_ sid_m_ root root n_pre ) ” 
  &&  “ (dfs2_phase2_post g_high_level_spec n_pre vis2_m sid_m1 vis2_m_ sid_m_ root ) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_ sid_m_ ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (root < n_pre) ” 
  &&  “ (root = (Znth (k) (order_l) (0))) ” 
  &&  “ ((Znth (root) (vis2_m) (0)) = 0) ” 
  &&  “ (sid_m1 = (replace_Znth (root) (root) (sid_m))) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m_ sid_m_ timer_m n_pre (k + 1 ) ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full vis2 n_pre vis2_m_ )
  **  (IntArray.full sid_pre n_pre sid_m_ )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
.

Definition kosaraju_entail_wit_15_1 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m_2: (@list Z)) (order_l_2: (@list Z)) (vis1_m_2: (@list Z)) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (timer_m: Z) (radj_col_l_2: (@list Z)) (radj_row_l_2: (@list Z)) (sid_m1: (@list Z)) (root: Z) (m: Z) (k: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (vis2_m_: (@list Z)) (sid_m_: (@list Z)) (PreH1 : (dfs2_high_level_post g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m1 vis2_m_ sid_m_ root root n_pre )) (PreH2 : (dfs2_phase2_post g_high_level_spec n_pre vis2_m_2 sid_m1 vis2_m_ sid_m_ root )) (PreH3 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_ sid_m_ )) (PreH4 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH5 : (AdjGraphValid g_high_level_spec )) (PreH6 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH7 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH9 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH10 : (m = (m_of (radj_row_l_2)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (0 <= root)) (PreH16 : (root < n_pre)) (PreH17 : (root = (Znth (k) (order_l_2) (0)))) (PreH18 : ((Znth (root) (vis2_m_2) (0)) = 0)) (PreH19 : (sid_m1 = (replace_Znth (root) (root) (sid_m_2)))) (PreH20 : (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_ sid_m_ timer_m n_pre (k + 1 ) )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full vis2 n_pre vis2_m_ )
  **  (IntArray.full sid_pre n_pre sid_m_ )
  **  (IntArray.full fin n_pre fin_m_2 )
  **  (IntArray.full radj_col (m_of (radj_row_l_2)) radj_col_l_2 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_2 )
  **  (IntArray.full pos n_pre order_l_2 )
  **  (IntArray.full vis1 n_pre vis1_m_2 )
|--
  EX (radj_col_l: (@list Z))  (fin_m: (@list Z))  (order_l: (@list Z))  (vis1_m: (@list Z))  (vis2_m: (@list Z))  (sid_m: (@list Z))  (radj_row_l: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre (k + 1 ) ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ” 
  &&  “ (((k + 1 ) = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
) \/
(
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m_2: (@list Z)) (order_l_2: (@list Z)) (vis1_m_2: (@list Z)) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (timer_m: Z) (radj_row_l_2: (@list Z)) (sid_m1: (@list Z)) (root: Z) (m: Z) (k: Z) (vis2_m_: (@list Z)) (sid_m_: (@list Z)) (PreH1 : (dfs2_high_level_post g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m1 vis2_m_ sid_m_ root root n_pre )) (PreH2 : (dfs2_phase2_post g_high_level_spec n_pre vis2_m_2 sid_m1 vis2_m_ sid_m_ root )) (PreH3 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_ sid_m_ )) (PreH4 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH5 : (AdjGraphValid g_high_level_spec )) (PreH6 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH7 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH9 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH10 : (m = (m_of (radj_row_l_2)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (0 <= root)) (PreH16 : (root < n_pre)) (PreH17 : (root = (Znth (k) (order_l_2) (0)))) (PreH18 : ((Znth (root) (vis2_m_2) (0)) = 0)) (PreH19 : (sid_m1 = (replace_Znth (root) (root) (sid_m_2)))) (PreH20 : (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_ sid_m_ timer_m n_pre (k + 1 ) )) ,
  TT && emp 
|--
  “ (((k + 1 ) = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m_) (0)) = (Znth (v) (sid_m_) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m_) (0)) = (Znth (v) (sid_m_) (0)))))))) ”
  &&  emp
).

Definition kosaraju_entail_wit_15_1_split_goal_1 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m_2: (@list Z)) (order_l_2: (@list Z)) (vis1_m_2: (@list Z)) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (timer_m: Z) (radj_row_l_2: (@list Z)) (sid_m1: (@list Z)) (root: Z) (m: Z) (k: Z) (vis2_m_: (@list Z)) (sid_m_: (@list Z)) (PreH1 : (dfs2_high_level_post g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m1 vis2_m_ sid_m_ root root n_pre )) (PreH2 : (dfs2_phase2_post g_high_level_spec n_pre vis2_m_2 sid_m1 vis2_m_ sid_m_ root )) (PreH3 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_ sid_m_ )) (PreH4 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH5 : (AdjGraphValid g_high_level_spec )) (PreH6 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH7 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH9 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH10 : (m = (m_of (radj_row_l_2)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 2147483646)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (0 <= root)) (PreH16 : (root < n_pre)) (PreH17 : (root = (Znth (k) (order_l_2) (0)))) (PreH18 : ((Znth (root) (vis2_m_2) (0)) = 0)) (PreH19 : (sid_m1 = (replace_Znth (root) (root) (sid_m_2)))) (PreH20 : (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_ sid_m_ timer_m n_pre (k + 1 ) )) ,
  (((k + 1 ) = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m_) (0)) = (Znth (v) (sid_m_) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m_) (0)) = (Znth (v) (sid_m_) (0))))))))
.

Definition kosaraju_entail_wit_15_2 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m_2: (@list Z)) (order_l_2: (@list Z)) (vis1_m_2: (@list Z)) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (timer_m: Z) (radj_col_l_2: (@list Z)) (radj_row_l_2: (@list Z)) (m: Z) (k: Z) (root: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (PreH1 : ((Znth root vis2_m_2 0) <> 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l_2) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  (IntArray.full vis2 n_pre vis2_m_2 )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m_2 )
  **  (IntArray.full fin n_pre fin_m_2 )
  **  (IntArray.full radj_col (m_of (radj_row_l_2)) radj_col_l_2 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_2 )
  **  (IntArray.full pos n_pre order_l_2 )
  **  (IntArray.full vis1 n_pre vis1_m_2 )
|--
  EX (radj_col_l: (@list Z))  (fin_m: (@list Z))  (order_l: (@list Z))  (vis1_m: (@list Z))  (vis2_m: (@list Z))  (sid_m: (@list Z))  (radj_row_l: (@list Z)) ,
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre (k + 1 ) ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ” 
  &&  “ (((k + 1 ) = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
) \/
(
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m_2: (@list Z)) (order_l_2: (@list Z)) (vis1_m_2: (@list Z)) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (timer_m: Z) (radj_row_l_2: (@list Z)) (m: Z) (k: Z) (root: Z) (PreH1 : ((Znth root vis2_m_2 0) <> 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l_2) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  TT && emp 
|--
  “ (((k + 1 ) = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m_2) (0)) = (Znth (v) (sid_m_2) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m_2) (0)) = (Znth (v) (sid_m_2) (0)))))))) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre (k + 1 ) ) ”
  &&  emp
).

Definition kosaraju_entail_wit_15_2_split_goal_1 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m_2: (@list Z)) (order_l_2: (@list Z)) (vis1_m_2: (@list Z)) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (timer_m: Z) (radj_row_l_2: (@list Z)) (m: Z) (k: Z) (root: Z) (PreH1 : ((Znth root vis2_m_2 0) <> 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l_2) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  (((k + 1 ) = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m_2) (0)) = (Znth (v) (sid_m_2) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m_2) (0)) = (Znth (v) (sid_m_2) (0))))))))
.

Definition kosaraju_entail_wit_15_2_split_goal_2 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m_2: (@list Z)) (order_l_2: (@list Z)) (vis1_m_2: (@list Z)) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (timer_m: Z) (radj_row_l_2: (@list Z)) (m: Z) (k: Z) (root: Z) (PreH1 : ((Znth root vis2_m_2 0) <> 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l_2) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) ,
  (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre (k + 1 ) )
.

Definition kosaraju_entail_wit_16 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (radj_col_l_2: (@list Z)) (fin: Z) (vis2: Z) (fin_m_2: (@list Z)) (order_l_2: (@list Z)) (vis1_m_2: (@list Z)) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (timer_m: Z) (k: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (k >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre k )) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH14 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) (PreH15 : ((k = n_pre) -> forall (u_2: Z) , (((0 <= u_2) /\ (u_2 < n_pre)) -> forall (v_2: Z) , (((0 <= v_2) /\ (v_2 < n_pre)) -> ((((Znth (u_2) (sid_m_2) (0)) = (Znth (v_2) (sid_m_2) (0))) -> (mutually_reachable g_high_level_spec u_2 v_2 )) /\ ((mutually_reachable g_high_level_spec u_2 v_2 ) -> ((Znth (u_2) (sid_m_2) (0)) = (Znth (v_2) (sid_m_2) (0))))))))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m_2 )
  **  (IntArray.full vis2 n_pre vis2_m_2 )
  **  (IntArray.full fin n_pre fin_m_2 )
  **  (IntArray.full radj_col (m_of (radj_row_l_2)) radj_col_l_2 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l_2 )
  **  (IntArray.full pos n_pre order_l_2 )
  **  (IntArray.full vis1 n_pre vis1_m_2 )
|--
  EX (vis2_m: (@list Z))  (fin_m: (@list Z))  (vis1_m: (@list Z))  (order_l: (@list Z))  (radj_col_l: (@list Z))  (sid_m: (@list Z))  (radj_row_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full radj_col m radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
) \/
(
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col: Z) (radj_col_l_2: (@list Z)) (fin_m_2: (@list Z)) (order_l_2: (@list Z)) (vis1_m_2: (@list Z)) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (timer_m: Z) (k: Z) (radj_row_l_2: (@list Z)) (m: Z) (PreH1 : (k >= n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (phase2_sequence_residual_refinement g_high_level_spec fin_m_2 order_l_2 vis1_m_2 vis2_m_2 sid_m_2 timer_m n_pre k )) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH14 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m_2 sid_m_2 )) (PreH15 : ((k = n_pre) -> forall (u_2: Z) , (((0 <= u_2) /\ (u_2 < n_pre)) -> forall (v_2: Z) , (((0 <= v_2) /\ (v_2 < n_pre)) -> ((((Znth (u_2) (sid_m_2) (0)) = (Znth (v_2) (sid_m_2) (0))) -> (mutually_reachable g_high_level_spec u_2 v_2 )) /\ ((mutually_reachable g_high_level_spec u_2 v_2 ) -> ((Znth (u_2) (sid_m_2) (0)) = (Znth (v_2) (sid_m_2) (0))))))))) ,
  (IntArray.full radj_col (m_of (radj_row_l_2)) radj_col_l_2 )
|--
  EX (radj_col_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l_2))) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m_2) (0)) = (Znth (v) (sid_m_2) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m_2) (0)) = (Znth (v) (sid_m_2) (0))))))) ”
  &&  (IntArray.full radj_col m radj_col_l )
).

Definition kosaraju_return_wit_1 := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (sid_m: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : forall (u_2: Z) , (((0 <= u_2) /\ (u_2 < n_pre)) -> forall (v_2: Z) , (((0 <= v_2) /\ (v_2 < n_pre)) -> ((((Znth (u_2) (sid_m) (0)) = (Znth (v_2) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u_2 v_2 )) /\ ((mutually_reachable g_high_level_spec u_2 v_2 ) -> ((Znth (u_2) (sid_m) (0)) = (Znth (v_2) (sid_m) (0)))))))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  EX (sid_l_: (@list Z)) ,
  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_l_) (0)) = (Znth (v) (sid_l_) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_l_) (0)) = (Znth (v) (sid_l_) (0))))))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_ )
) \/
(
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (sid_m: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : forall (u_2: Z) , (((0 <= u_2) /\ (u_2 < n_pre)) -> forall (v_2: Z) , (((0 <= v_2) /\ (v_2 < n_pre)) -> ((((Znth (u_2) (sid_m) (0)) = (Znth (v_2) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u_2 v_2 )) /\ ((mutually_reachable g_high_level_spec u_2 v_2 ) -> ((Znth (u_2) (sid_m) (0)) = (Znth (v_2) (sid_m) (0)))))))) ,
  TT && emp 
|--
  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))) ”
  &&  emp
).

Definition kosaraju_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (sid_m: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : forall (u_2: Z) , (((0 <= u_2) /\ (u_2 < n_pre)) -> forall (v_2: Z) , (((0 <= v_2) /\ (v_2 < n_pre)) -> ((((Znth (u_2) (sid_m) (0)) = (Znth (v_2) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u_2 v_2 )) /\ ((mutually_reachable g_high_level_spec u_2 v_2 ) -> ((Znth (u_2) (sid_m) (0)) = (Znth (v_2) (sid_m) (0)))))))) ,
  forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))
.

Definition kosaraju_partial_solve_wit_1 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH4 : (AdjGraphValid g_high_level_spec )) (PreH5 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH6 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH7 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH8 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((m_of (fadj_row_l_high_level_spec)) > 0) ”
  &&  (((fadj_row_pre + (n_pre * sizeof(INT)))) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  (IntArray.missing_i fadj_row_pre n_pre 0 (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
.

Definition kosaraju_partial_solve_wit_2_pure := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH4 : (AdjGraphValid g_high_level_spec )) (PreH5 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH6 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH7 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH8 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "radj_col" ) )) # Ptr  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ ((Znth n_pre fadj_row_l_high_level_spec 0) > 0) ”
) \/
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((Znth n_pre fadj_row_l_high_level_spec 0) <= INT_MAX)) (PreH3 : (n_pre >= INT_MIN)) (PreH4 : ((Znth n_pre fadj_row_l_high_level_spec 0) >= INT_MIN)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : (AdjGraphValid g_high_level_spec )) (PreH9 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "radj_col" ) )) # Ptr  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ ((Znth n_pre fadj_row_l_high_level_spec 0) > 0) ”
).

Definition kosaraju_partial_solve_wit_2_pure_split_goal_1 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((Znth n_pre fadj_row_l_high_level_spec 0) <= INT_MAX)) (PreH3 : (n_pre >= INT_MIN)) (PreH4 : ((Znth n_pre fadj_row_l_high_level_spec 0) >= INT_MIN)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : (AdjGraphValid g_high_level_spec )) (PreH9 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "radj_col" ) )) # Ptr  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ ((Znth n_pre fadj_row_l_high_level_spec 0) > 0) ”
.

Definition kosaraju_partial_solve_wit_2_aux := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH4 : (AdjGraphValid g_high_level_spec )) (PreH5 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH6 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH7 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH8 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ ((Znth n_pre fadj_row_l_high_level_spec 0) > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((m_of (fadj_row_l_high_level_spec)) > 0) ”
  &&  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
.

Definition kosaraju_partial_solve_wit_2 := kosaraju_partial_solve_wit_2_pure -> kosaraju_partial_solve_wit_2_aux.

Definition kosaraju_partial_solve_wit_3_pure := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2147483646)) (PreH4 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH5 : (AdjGraphValid g_high_level_spec )) (PreH6 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH7 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH8 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH9 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "radj_row" ) )) # Ptr  |->_)
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  ((( &( "radj_col" ) )) # Ptr  |-> retval)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ ((n_pre + 1 ) > 0) ”
.

Definition kosaraju_partial_solve_wit_3_aux := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2147483646)) (PreH4 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH5 : (AdjGraphValid g_high_level_spec )) (PreH6 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH7 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH8 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH9 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ ((n_pre + 1 ) > 0) ” 
  &&  “ ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((m_of (fadj_row_l_high_level_spec)) > 0) ”
  &&  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
.

Definition kosaraju_partial_solve_wit_3 := kosaraju_partial_solve_wit_3_pure -> kosaraju_partial_solve_wit_3_aux.

Definition kosaraju_partial_solve_wit_4_pure := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (PreH1 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH2 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH6 : (AdjGraphValid g_high_level_spec )) (PreH7 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH9 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH10 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "pos" ) )) # Ptr  |->_)
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> retval_2)
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  ((( &( "radj_col" ) )) # Ptr  |-> retval)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (n_pre > 0) ”
.

Definition kosaraju_partial_solve_wit_4_aux := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (PreH1 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH2 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH6 : (AdjGraphValid g_high_level_spec )) (PreH7 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH9 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH10 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((m_of (fadj_row_l_high_level_spec)) > 0) ”
  &&  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
.

Definition kosaraju_partial_solve_wit_4 := kosaraju_partial_solve_wit_4_pure -> kosaraju_partial_solve_wit_4_aux.

Definition kosaraju_partial_solve_wit_5_pure := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (l_3: (@list Z)) (retval_3: Z) (PreH1 : ((Zlength (l_3)) = n_pre)) (PreH2 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH3 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH7 : (AdjGraphValid g_high_level_spec )) (PreH8 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH9 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH10 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH11 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "vis1" ) )) # Ptr  |->_)
  **  (IntArray.full retval_3 n_pre l_3 )
  **  ((( &( "pos" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> retval_2)
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  ((( &( "radj_col" ) )) # Ptr  |-> retval)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (n_pre > 0) ”
.

Definition kosaraju_partial_solve_wit_5_aux := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (l_3: (@list Z)) (retval_3: Z) (PreH1 : ((Zlength (l_3)) = n_pre)) (PreH2 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH3 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH7 : (AdjGraphValid g_high_level_spec )) (PreH8 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH9 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH10 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH11 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  (IntArray.full retval_3 n_pre l_3 )
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_3)) = n_pre) ” 
  &&  “ ((Zlength (l_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((m_of (fadj_row_l_high_level_spec)) > 0) ”
  &&  (IntArray.full retval_3 n_pre l_3 )
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
.

Definition kosaraju_partial_solve_wit_5 := kosaraju_partial_solve_wit_5_pure -> kosaraju_partial_solve_wit_5_aux.

Definition kosaraju_partial_solve_wit_6_pure := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (l_3: (@list Z)) (retval_3: Z) (l_4: (@list Z)) (retval_4: Z) (PreH1 : ((Zlength (l_4)) = n_pre)) (PreH2 : ((Zlength (l_3)) = n_pre)) (PreH3 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH4 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : (AdjGraphValid g_high_level_spec )) (PreH9 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "fin" ) )) # Ptr  |->_)
  **  (IntArray.full retval_4 n_pre l_4 )
  **  ((( &( "vis1" ) )) # Ptr  |-> retval_4)
  **  (IntArray.full retval_3 n_pre l_3 )
  **  ((( &( "pos" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> retval_2)
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  ((( &( "radj_col" ) )) # Ptr  |-> retval)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (n_pre > 0) ”
.

Definition kosaraju_partial_solve_wit_6_aux := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (l_3: (@list Z)) (retval_3: Z) (l_4: (@list Z)) (retval_4: Z) (PreH1 : ((Zlength (l_4)) = n_pre)) (PreH2 : ((Zlength (l_3)) = n_pre)) (PreH3 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH4 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2147483646)) (PreH7 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH8 : (AdjGraphValid g_high_level_spec )) (PreH9 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  (IntArray.full retval_4 n_pre l_4 )
  **  (IntArray.full retval_3 n_pre l_3 )
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_4)) = n_pre) ” 
  &&  “ ((Zlength (l_3)) = n_pre) ” 
  &&  “ ((Zlength (l_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((m_of (fadj_row_l_high_level_spec)) > 0) ”
  &&  (IntArray.full retval_4 n_pre l_4 )
  **  (IntArray.full retval_3 n_pre l_3 )
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
.

Definition kosaraju_partial_solve_wit_6 := kosaraju_partial_solve_wit_6_pure -> kosaraju_partial_solve_wit_6_aux.

Definition kosaraju_partial_solve_wit_7_pure := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (l_3: (@list Z)) (retval_3: Z) (l_4: (@list Z)) (retval_4: Z) (l_5: (@list Z)) (retval_5: Z) (PreH1 : ((Zlength (l_5)) = n_pre)) (PreH2 : ((Zlength (l_4)) = n_pre)) (PreH3 : ((Zlength (l_3)) = n_pre)) (PreH4 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH5 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH9 : (AdjGraphValid g_high_level_spec )) (PreH10 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH11 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH12 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH13 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  ((( &( "vis2" ) )) # Ptr  |->_)
  **  (IntArray.full retval_5 n_pre l_5 )
  **  ((( &( "fin" ) )) # Ptr  |-> retval_5)
  **  (IntArray.full retval_4 n_pre l_4 )
  **  ((( &( "vis1" ) )) # Ptr  |-> retval_4)
  **  (IntArray.full retval_3 n_pre l_3 )
  **  ((( &( "pos" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> retval_2)
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  ((( &( "radj_col" ) )) # Ptr  |-> retval)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "m" ) )) # Int  |-> (Znth n_pre fadj_row_l_high_level_spec 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (n_pre > 0) ”
.

Definition kosaraju_partial_solve_wit_7_aux := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (l: (@list Z)) (retval: Z) (l_2: (@list Z)) (retval_2: Z) (l_3: (@list Z)) (retval_3: Z) (l_4: (@list Z)) (retval_4: Z) (l_5: (@list Z)) (retval_5: Z) (PreH1 : ((Zlength (l_5)) = n_pre)) (PreH2 : ((Zlength (l_4)) = n_pre)) (PreH3 : ((Zlength (l_3)) = n_pre)) (PreH4 : ((Zlength (l_2)) = (n_pre + 1 ))) (PreH5 : ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2147483646)) (PreH8 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH9 : (AdjGraphValid g_high_level_spec )) (PreH10 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH11 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH12 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH13 : ((m_of (fadj_row_l_high_level_spec)) > 0)) ,
  (IntArray.full retval_5 n_pre l_5 )
  **  (IntArray.full retval_4 n_pre l_4 )
  **  (IntArray.full retval_3 n_pre l_3 )
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
|--
  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_5)) = n_pre) ” 
  &&  “ ((Zlength (l_4)) = n_pre) ” 
  &&  “ ((Zlength (l_3)) = n_pre) ” 
  &&  “ ((Zlength (l_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (l)) = (Znth n_pre fadj_row_l_high_level_spec 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((m_of (fadj_row_l_high_level_spec)) > 0) ”
  &&  (IntArray.full retval_5 n_pre l_5 )
  **  (IntArray.full retval_4 n_pre l_4 )
  **  (IntArray.full retval_3 n_pre l_3 )
  **  (IntArray.full retval_2 (n_pre + 1 ) l_2 )
  **  (IntArray.full retval (Znth n_pre fadj_row_l_high_level_spec 0) l )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
.

Definition kosaraju_partial_solve_wit_7 := kosaraju_partial_solve_wit_7_pure -> kosaraju_partial_solve_wit_7_aux.

Definition kosaraju_partial_solve_wit_8 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vm: (@list Z)) (vm2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm) (0)) = 0))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col m radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full vis1 n_pre vm )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vm2 )
|--
  “ (u < n_pre) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (timer = 0) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (fin_l0)) = n_pre) ” 
  &&  “ ((Zlength (vm)) = n_pre) ” 
  &&  “ ((Zlength (vm2)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm) (0)) = 0)) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2) (0)) = 0)) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (((vis1 + (u * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i vis1 u 0 n_pre vm )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col m radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vm2 )
.

Definition kosaraju_partial_solve_wit_9 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vm: (@list Z)) (vm2: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= u)) (PreH6 : (u <= n_pre)) (PreH7 : (timer = 0)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (fin_l0)) = n_pre)) (PreH10 : ((Zlength (vm)) = n_pre)) (PreH11 : ((Zlength (vm2)) = n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm) (0)) = 0))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2) (0)) = 0))) (PreH14 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : (AdjGraphValid g_high_level_spec )) (PreH16 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH17 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH18 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full vis1 n_pre (replace_Znth (u) (0) (vm)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col m radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vm2 )
|--
  “ (u < n_pre) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (timer = 0) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (fin_l0)) = n_pre) ” 
  &&  “ ((Zlength (vm)) = n_pre) ” 
  &&  “ ((Zlength (vm2)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < u)) -> ((Znth (i) (vm) (0)) = 0)) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < u)) -> ((Znth (i_2) (vm2) (0)) = 0)) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (((vis2 + (u * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i vis2 u 0 n_pre vm2 )
  **  (IntArray.full vis1 n_pre (replace_Znth (u) (0) (vm)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col m radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full fin n_pre fin_l0 )
.

Definition kosaraju_partial_solve_wit_10_pure := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2147483646)) (PreH4 : (timer = 0)) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis1_zero)) = n_pre)) (PreH7 : ((Zlength (vis2_zero)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0))) (PreH9 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH10 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH11 : (AdjGraphValid g_high_level_spec )) (PreH12 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH13 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH14 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pos_l0)) = n_pre) ” 
  &&  “ ((Zlength (radj_row_l0)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (radj_col_l0)) = m) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (0 <= m) ”
) \/
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (PreH1 : (timer <= INT_MAX)) (PreH2 : (m <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (timer >= INT_MIN)) (PreH5 : (m >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (timer = 0)) (PreH11 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH12 : ((Zlength (vis1_zero)) = n_pre)) (PreH13 : ((Zlength (vis2_zero)) = n_pre)) (PreH14 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (0 <= m) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ ((Zlength (radj_col_l0)) = m) ” 
  &&  “ ((Zlength (radj_row_l0)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pos_l0)) = n_pre) ”
).

Definition kosaraju_partial_solve_wit_10_pure_split_goal_1 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (PreH1 : (timer <= INT_MAX)) (PreH2 : (m <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (timer >= INT_MIN)) (PreH5 : (m >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (timer = 0)) (PreH11 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH12 : ((Zlength (vis1_zero)) = n_pre)) (PreH13 : ((Zlength (vis2_zero)) = n_pre)) (PreH14 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (0 <= m) ”
.

Definition kosaraju_partial_solve_wit_10_pure_split_goal_2 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (PreH1 : (timer <= INT_MAX)) (PreH2 : (m <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (timer >= INT_MIN)) (PreH5 : (m >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (timer = 0)) (PreH11 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH12 : ((Zlength (vis1_zero)) = n_pre)) (PreH13 : ((Zlength (vis2_zero)) = n_pre)) (PreH14 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (m <= 2147483646) ”
.

Definition kosaraju_partial_solve_wit_10_pure_split_goal_3 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (PreH1 : (timer <= INT_MAX)) (PreH2 : (m <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (timer >= INT_MIN)) (PreH5 : (m >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (timer = 0)) (PreH11 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH12 : ((Zlength (vis1_zero)) = n_pre)) (PreH13 : ((Zlength (vis2_zero)) = n_pre)) (PreH14 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ ((Zlength (radj_col_l0)) = m) ”
.

Definition kosaraju_partial_solve_wit_10_pure_split_goal_4 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (PreH1 : (timer <= INT_MAX)) (PreH2 : (m <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (timer >= INT_MIN)) (PreH5 : (m >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (timer = 0)) (PreH11 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH12 : ((Zlength (vis1_zero)) = n_pre)) (PreH13 : ((Zlength (vis2_zero)) = n_pre)) (PreH14 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ ((Zlength (radj_row_l0)) = (n_pre + 1 )) ”
.

Definition kosaraju_partial_solve_wit_10_pure_split_goal_5 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (PreH1 : (timer <= INT_MAX)) (PreH2 : (m <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (timer >= INT_MIN)) (PreH5 : (m >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 2147483646)) (PreH10 : (timer = 0)) (PreH11 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH12 : ((Zlength (vis1_zero)) = n_pre)) (PreH13 : ((Zlength (vis2_zero)) = n_pre)) (PreH14 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l0 )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_l0 )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ ((Zlength (pos_l0)) = n_pre) ”
.

Definition kosaraju_partial_solve_wit_10_aux := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (radj_col_l0: (@list Z)) (radj_row_l0: (@list Z)) (pos_l0: (@list Z)) (fin_l0: (@list Z)) (m: Z) (timer: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2147483646)) (PreH4 : (timer = 0)) (PreH5 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH6 : ((Zlength (vis1_zero)) = n_pre)) (PreH7 : ((Zlength (vis2_zero)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0))) (PreH9 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0))) (PreH10 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH11 : (AdjGraphValid g_high_level_spec )) (PreH12 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH13 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH14 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pos_l0)) = n_pre) ” 
  &&  “ ((Zlength (radj_row_l0)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (radj_col_l0)) = m) ” 
  &&  “ (m <= 2147483646) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (timer = 0) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis1_zero)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis1_zero) (0)) = 0)) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth (i_2) (vis2_zero) (0)) = 0)) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (fadj_row_l_high_level_spec)) radj_col_l0 )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l0 )
  **  (IntArray.full pos n_pre pos_l0 )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full vis1 n_pre vis1_zero )
  **  (IntArray.full fin n_pre fin_l0 )
  **  (IntArray.full vis2 n_pre vis2_zero )
.

Definition kosaraju_partial_solve_wit_10 := kosaraju_partial_solve_wit_10_pure -> kosaraju_partial_solve_wit_10_aux.

Definition kosaraju_partial_solve_wit_11 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis2: Z) (fin: Z) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (timer: Z) (u: Z) (m: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (PreH1 : (u < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= u)) (PreH7 : (u <= n_pre)) (PreH8 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH9 : ((Zlength (vis1_m)) = n_pre)) (PreH10 : ((Zlength (vis2_zero)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH12 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH13 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH15 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH18 : (AdjGraphValid g_high_level_spec )) (PreH19 : ((adj_verts (g_high_level_spec)) = n_pre)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (u < n_pre) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis1_m)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre ) ” 
  &&  “ (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ”
  &&  (((vis1 + (u * sizeof(INT)))) # Int  |-> (Znth u vis1_m 0))
  **  (IntArray.missing_i vis1 u 0 n_pre vis1_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_zero )
.

Definition kosaraju_partial_solve_wit_12_pure := 
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (m: Z) (timer: Z) (u: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (m = (m_of (radj_row_l)))) (PreH3 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH4 : ((Zlength (vis2_zero)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH6 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH7 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )) (PreH8 : (csr1_faithful g_high_level_spec radj_col_l radj_row_l )) (PreH9 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH10 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )) (PreH11 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH12 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH13 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH14 : (0 <= u)) (PreH15 : (u < n_pre)) (PreH16 : (n_pre <= 2147483646)) (PreH17 : ((Znth (u) (vis1_m) (0)) = 0)) (PreH18 : (0 <= timer)) (PreH19 : (timer <= (count_nonzero (vis1_m)))) (PreH20 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH21 : (AdjGraphValid g_high_level_spec )) (PreH22 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH23 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_high_level_spec radj_col_l radj_row_l ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) ) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u) (vis1_m) (0)) = 0) ” 
  &&  “ (0 <= timer) ” 
  &&  “ (timer <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer < n_pre) ”
) \/
(
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (m: Z) (timer: Z) (u: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (PreH1 : (u <= INT_MAX)) (PreH2 : (timer <= INT_MAX)) (PreH3 : (m <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (u >= INT_MIN)) (PreH6 : (timer >= INT_MIN)) (PreH7 : (m >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH10 : (m = (m_of (radj_row_l)))) (PreH11 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH12 : ((Zlength (vis2_zero)) = n_pre)) (PreH13 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH15 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )) (PreH16 : (csr1_faithful g_high_level_spec radj_col_l radj_row_l )) (PreH17 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH18 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )) (PreH19 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH20 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH21 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH22 : (0 <= u)) (PreH23 : (u < n_pre)) (PreH24 : (n_pre <= 2147483646)) (PreH25 : ((Znth (u) (vis1_m) (0)) = 0)) (PreH26 : (0 <= timer)) (PreH27 : (timer <= (count_nonzero (vis1_m)))) (PreH28 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH29 : (AdjGraphValid g_high_level_spec )) (PreH30 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH31 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (timer < n_pre) ”
).

Definition kosaraju_partial_solve_wit_12_pure_split_goal_1 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (m: Z) (timer: Z) (u: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (PreH1 : (u <= INT_MAX)) (PreH2 : (timer <= INT_MAX)) (PreH3 : (m <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (u >= INT_MIN)) (PreH6 : (timer >= INT_MIN)) (PreH7 : (m >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH10 : (m = (m_of (radj_row_l)))) (PreH11 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH12 : ((Zlength (vis2_zero)) = n_pre)) (PreH13 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH14 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH15 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )) (PreH16 : (csr1_faithful g_high_level_spec radj_col_l radj_row_l )) (PreH17 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH18 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )) (PreH19 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH20 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH21 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH22 : (0 <= u)) (PreH23 : (u < n_pre)) (PreH24 : (n_pre <= 2147483646)) (PreH25 : ((Znth (u) (vis1_m) (0)) = 0)) (PreH26 : (0 <= timer)) (PreH27 : (timer <= (count_nonzero (vis1_m)))) (PreH28 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH29 : (AdjGraphValid g_high_level_spec )) (PreH30 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH31 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre pos_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (timer < n_pre) ”
.

Definition kosaraju_partial_solve_wit_12_aux := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (sid_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis2_zero: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (pos_l: (@list Z)) (m: Z) (timer: Z) (u: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (m = (m_of (radj_row_l)))) (PreH3 : ((Zlength (sid_l_high_level_spec)) = n_pre)) (PreH4 : ((Zlength (vis2_zero)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0))) (PreH6 : (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre )) (PreH7 : (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m )) (PreH8 : (csr1_faithful g_high_level_spec radj_col_l radj_row_l )) (PreH9 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH10 : (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer )) (PreH11 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u )) (PreH12 : (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre )) (PreH13 : (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) )) (PreH14 : (0 <= u)) (PreH15 : (u < n_pre)) (PreH16 : (n_pre <= 2147483646)) (PreH17 : ((Znth (u) (vis1_m) (0)) = 0)) (PreH18 : (0 <= timer)) (PreH19 : (timer <= (count_nonzero (vis1_m)))) (PreH20 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH21 : (AdjGraphValid g_high_level_spec )) (PreH22 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH23 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_zero )
|--
  “ (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_high_level_spec radj_col_l radj_row_l ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) ) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u) (vis1_m) (0)) = 0) ” 
  &&  “ (0 <= timer) ” 
  &&  “ (timer <= (count_nonzero (vis1_m))) ” 
  &&  “ (timer < n_pre) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ ((Zlength (sid_l_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (vis2_zero)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth (i) (vis2_zero) (0)) = 0)) ” 
  &&  “ (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l radj_row_l n_pre ) ” 
  &&  “ (csr_wf1 g_high_level_spec radj_col_l radj_row_l vis1_m fin_m ) ” 
  &&  “ (csr1_faithful g_high_level_spec radj_col_l radj_row_l ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (dfs1_sequence_state_ready g_high_level_spec radj_col_l radj_row_l vis1_m fin_m timer ) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer n_pre u ) ” 
  &&  “ (dfs1_finish_prefix_marked fin_m vis1_m timer n_pre ) ” 
  &&  “ (safeExec (pre_dfs1_sequence (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_m) (fin_m) (timer)) (bind ((dfs_finish (g_high_level_spec) (u))) ((dfs_finish_scheduleK (g_high_level_spec) ((u + 1 )) (((n_pre - u ) - 1 ))))) (result_state ((pre_dfs1_sequence_initial (g_high_level_spec) (radj_col_l) (radj_row_l) (vis1_zero) (fin_l0) (n_pre))) ((dfs_finish_schedule (g_high_level_spec) (0) (n_pre)))) ) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ ((Znth (u) (vis1_m) (0)) = 0) ” 
  &&  “ (0 <= timer) ” 
  &&  “ (timer <= (count_nonzero (vis1_m))) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ”
  &&  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_high_level_spec )
  **  (IntArray.full pos n_pre pos_l )
  **  (IntArray.full vis2 n_pre vis2_zero )
.

Definition kosaraju_partial_solve_wit_12 := kosaraju_partial_solve_wit_12_pure -> kosaraju_partial_solve_wit_12_aux.

Definition kosaraju_partial_solve_wit_13 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (radj_col_l: (@list Z)) (sid_m: (@list Z)) (vis2_m: (@list Z)) (vis1_m: (@list Z)) (order_l: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l: (@list Z)) (m: Z) (PreH1 : (i < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m)) = n_pre)) (PreH9 : ((Zlength (order_l)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_m)) = n_pre)) (PreH12 : ((Zlength (sid_m)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (i < n_pre) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (fin_m)) = n_pre) ” 
  &&  “ ((Zlength (order_l)) = n_pre) ” 
  &&  “ ((Zlength (vis1_m)) = n_pre) ” 
  &&  “ ((Zlength (vis2_m)) = n_pre) ” 
  &&  “ ((Zlength (sid_m)) = n_pre) ” 
  &&  “ forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0)) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0)))) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ”
  &&  (((fin + (((n_pre - 1 ) - i ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre - 1 ) - i ) fin_m 0))
  **  (IntArray.missing_i fin ((n_pre - 1 ) - i ) 0 n_pre fin_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
.

Definition kosaraju_partial_solve_wit_14 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_l0: (@list Z)) (vis1_zero: (@list Z)) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (radj_col_l: (@list Z)) (sid_m: (@list Z)) (vis2_m: (@list Z)) (vis1_m: (@list Z)) (order_l: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (radj_row_l: (@list Z)) (m: Z) (PreH1 : (i < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (fin_m)) = n_pre)) (PreH9 : ((Zlength (order_l)) = n_pre)) (PreH10 : ((Zlength (vis1_m)) = n_pre)) (PreH11 : ((Zlength (vis2_m)) = n_pre)) (PreH12 : ((Zlength (sid_m)) = n_pre)) (PreH13 : forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0))) (PreH14 : forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0))))) (PreH15 : (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre )) (PreH16 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH17 : (AdjGraphValid g_high_level_spec )) (PreH18 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH19 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH20 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH21 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (i < n_pre) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (fin_m)) = n_pre) ” 
  &&  “ ((Zlength (order_l)) = n_pre) ” 
  &&  “ ((Zlength (vis1_m)) = n_pre) ” 
  &&  “ ((Zlength (vis2_m)) = n_pre) ” 
  &&  “ ((Zlength (sid_m)) = n_pre) ” 
  &&  “ forall (u0: Z) , (((0 <= u0) /\ (u0 < n_pre)) -> ((Znth (u0) (vis2_m) (0)) = 0)) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < i)) -> ((Znth (u) (order_l) (0)) = (Znth (((n_pre - 1 ) - u )) (fin_m) (0)))) ” 
  &&  “ (phase1_sequence_refinement g_high_level_spec radj_col_l radj_row_l vis1_m fin_m vis1_zero fin_l0 timer_m n_pre n_pre ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ”
  &&  (((pos + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos i 0 n_pre order_l )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full vis1 n_pre vis1_m )
.

Definition kosaraju_partial_solve_wit_15 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (vis1: Z) (pos: Z) (radj_row: Z) (radj_col: Z) (fin: Z) (vis2: Z) (k: Z) (m: Z) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH9 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH10 : (AdjGraphValid g_high_level_spec )) (PreH11 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH12 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH14 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) (PreH15 : ((k = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (k < n_pre) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ” 
  &&  “ ((k = n_pre) -> forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ”
  &&  (((pos + (k * sizeof(INT)))) # Int  |-> (Znth k order_l 0))
  **  (IntArray.missing_i pos k 0 n_pre order_l )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full vis1 n_pre vis1_m )
.

Definition kosaraju_partial_solve_wit_16 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (PreH1 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH2 : (m = (m_of (radj_row_l)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2147483646)) (PreH5 : (0 <= k)) (PreH6 : (k < n_pre)) (PreH7 : (0 <= root)) (PreH8 : (root < n_pre)) (PreH9 : (root = (Znth (k) (order_l) (0)))) (PreH10 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH11 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH12 : (AdjGraphValid g_high_level_spec )) (PreH13 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH14 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH15 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH16 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (root < n_pre) ” 
  &&  “ (root = (Znth (k) (order_l) (0))) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ”
  &&  (((vis2 + (root * sizeof(INT)))) # Int  |-> (Znth root vis2_m 0))
  **  (IntArray.missing_i vis2 root 0 n_pre vis2_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
.

Definition kosaraju_partial_solve_wit_17 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (PreH1 : ((Znth root vis2_m 0) = 0)) (PreH2 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH3 : (m = (m_of (radj_row_l)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2147483646)) (PreH6 : (0 <= k)) (PreH7 : (k < n_pre)) (PreH8 : (0 <= root)) (PreH9 : (root < n_pre)) (PreH10 : (root = (Znth (k) (order_l) (0)))) (PreH11 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) (PreH12 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH13 : (AdjGraphValid g_high_level_spec )) (PreH14 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH15 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH16 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH17 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m )) ,
  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ ((Znth root vis2_m 0) = 0) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (root < n_pre) ” 
  &&  “ (root = (Znth (k) (order_l) (0))) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m ) ”
  &&  (((sid_pre + (root * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i sid_pre root 0 n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
.

Definition kosaraju_partial_solve_wit_18_pure := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (sid_m1: (@list Z)) (PreH1 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 )) (PreH2 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH3 : (AdjGraphValid g_high_level_spec )) (PreH4 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH5 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH6 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH7 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : (m = (m_of (radj_row_l)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : (0 <= k)) (PreH12 : (k < n_pre)) (PreH13 : (0 <= root)) (PreH14 : (root < n_pre)) (PreH15 : (root = (Znth (k) (order_l) (0)))) (PreH16 : ((Znth (root) (vis2_m) (0)) = 0)) (PreH17 : ((Znth (root) (sid_m1) (0)) = root)) (PreH18 : (sid_m1 = (replace_Znth (root) (root) (sid_m)))) (PreH19 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "timer" ) )) # Int  |-> timer_m)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m1 )
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n_pre fin_m )
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col)
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row)
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  ((( &( "pos" ) )) # Ptr  |-> pos)
  **  (IntArray.full pos n_pre order_l )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (root < n_pre) ” 
  &&  “ (root = root) ” 
  &&  “ (root = (Znth (k) (order_l) (0))) ” 
  &&  “ ((Znth (root) (vis2_m) (0)) = 0) ” 
  &&  “ ((Znth (root) (vis2_m) (0)) = 0) ” 
  &&  “ ((Znth (root) (sid_m1) (0)) = root) ” 
  &&  “ (sid_m1 = (replace_Znth (root) (root) (sid_m))) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k ) ”
.

Definition kosaraju_partial_solve_wit_18_aux := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (timer_m: Z) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (m: Z) (k: Z) (root: Z) (vis2: Z) (fin: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (sid_m1: (@list Z)) (PreH1 : (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 )) (PreH2 : (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH3 : (AdjGraphValid g_high_level_spec )) (PreH4 : ((adj_verts (g_high_level_spec)) = n_pre)) (PreH5 : (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec )) (PreH6 : ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0)) (PreH7 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH8 : (m = (m_of (radj_row_l)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2147483646)) (PreH11 : (0 <= k)) (PreH12 : (k < n_pre)) (PreH13 : (0 <= root)) (PreH14 : (root < n_pre)) (PreH15 : (root = (Znth (k) (order_l) (0)))) (PreH16 : ((Znth (root) (vis2_m) (0)) = 0)) (PreH17 : ((Znth (root) (sid_m1) (0)) = root)) (PreH18 : (sid_m1 = (replace_Znth (root) (root) (sid_m)))) (PreH19 : (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k )) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m1 )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
|--
  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (root < n_pre) ” 
  &&  “ (root = root) ” 
  &&  “ (root = (Znth (k) (order_l) (0))) ” 
  &&  “ ((Znth (root) (vis2_m) (0)) = 0) ” 
  &&  “ ((Znth (root) (vis2_m) (0)) = 0) ” 
  &&  “ ((Znth (root) (sid_m1) (0)) = root) ” 
  &&  “ (sid_m1 = (replace_Znth (root) (root) (sid_m))) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k ) ” 
  &&  “ (csr_wf2 g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec vis2_m sid_m1 ) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (root < n_pre) ” 
  &&  “ (root = (Znth (k) (order_l) (0))) ” 
  &&  “ ((Znth (root) (vis2_m) (0)) = 0) ” 
  &&  “ ((Znth (root) (sid_m1) (0)) = root) ” 
  &&  “ (sid_m1 = (replace_Znth (root) (root) (sid_m))) ” 
  &&  “ (phase2_sequence_residual_refinement g_high_level_spec fin_m order_l vis1_m vis2_m sid_m timer_m n_pre k ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m1 )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full radj_col (m_of (radj_row_l)) radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
.

Definition kosaraju_partial_solve_wit_18 := kosaraju_partial_solve_wit_18_pure -> kosaraju_partial_solve_wit_18_aux.

Definition kosaraju_partial_solve_wit_19 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (radj_col: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (sid_m: (@list Z)) (vis2_m: (@list Z)) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (radj_col_l: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full radj_col m radj_col_l )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))) ”
  &&  (IntArray.full radj_col m radj_col_l )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
.

Definition kosaraju_partial_solve_wit_20 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (radj_row: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (sid_m: (@list Z)) (vis2_m: (@list Z)) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))) ”
  &&  (IntArray.full radj_row (n_pre + 1 ) radj_row_l )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
.

Definition kosaraju_partial_solve_wit_21 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (pos: Z) (vis1: Z) (fin: Z) (vis2: Z) (sid_m: (@list Z)) (vis2_m: (@list Z)) (fin_m: (@list Z)) (order_l: (@list Z)) (vis1_m: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full pos n_pre order_l )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))) ”
  &&  (IntArray.full pos n_pre order_l )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
.

Definition kosaraju_partial_solve_wit_22 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (vis1: Z) (fin: Z) (vis2: Z) (sid_m: (@list Z)) (vis2_m: (@list Z)) (fin_m: (@list Z)) (vis1_m: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))) ”
  &&  (IntArray.full vis1 n_pre vis1_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
.

Definition kosaraju_partial_solve_wit_23 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (fin: Z) (vis2: Z) (sid_m: (@list Z)) (vis2_m: (@list Z)) (fin_m: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full vis2 n_pre vis2_m )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))) ”
  &&  (IntArray.full fin n_pre fin_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
.

Definition kosaraju_partial_solve_wit_24 := 
forall (sid_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) (m: Z) (vis2: Z) (sid_m: (@list Z)) (vis2_m: (@list Z)) (radj_row_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2147483646)) (PreH3 : (m = (m_of (fadj_row_l_high_level_spec)))) (PreH4 : (m = (m_of (radj_row_l)))) (PreH5 : forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0)))))))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full vis2 n_pre vis2_m )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (m = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m = (m_of (radj_row_l))) ” 
  &&  “ forall (u: Z) , (((0 <= u) /\ (u < n_pre)) -> forall (v: Z) , (((0 <= v) /\ (v < n_pre)) -> ((((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))) -> (mutually_reachable g_high_level_spec u v )) /\ ((mutually_reachable g_high_level_spec u v ) -> ((Znth (u) (sid_m) (0)) = (Znth (v) (sid_m) (0))))))) ”
  &&  (IntArray.full vis2 n_pre vis2_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
.

Definition transpose_derive_high_level_spec_by_low_level_spec := 
forall (pos_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (m_pre: Z) (n_pre: Z) (pos_l_high_level_spec: (@list Z)) (radj_row_l_high_level_spec: (@list Z)) (radj_col_l_high_level_spec: (@list Z)) (fadj_row_l_high_level_spec: (@list Z)) (fadj_col_l_high_level_spec: (@list Z)) (g_high_level_spec: AdjGraph) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre = (m_of (fadj_row_l_high_level_spec))) ” 
  &&  “ (m_pre <= 2147483646) ” 
  &&  “ (csr_wf2_core g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_high_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec ) ” 
  &&  “ (AdjGraphValid g_high_level_spec ) ” 
  &&  “ ((adj_verts (g_high_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_high_level_spec)) = m_pre) ” 
  &&  “ ((Zlength (radj_row_l_high_level_spec)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pos_l_high_level_spec)) = n_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_high_level_spec)) radj_col_l_high_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_high_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_high_level_spec )
|--
EX (g_low_level_spec: AdjGraph) (fadj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (pos_l_low_level_spec: (@list Z)) ,
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2147483646) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre = (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (m_pre <= 2147483646) ” 
  &&  “ (csr_wf2_core g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((csr_lo (0) (fadj_row_l_low_level_spec)) = 0) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ (AdjGraphValid g_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (radj_col_l_low_level_spec)) = m_pre) ” 
  &&  “ ((Zlength (radj_row_l_low_level_spec)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pos_l_low_level_spec)) = n_pre) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full pos_pre n_pre pos_l_low_level_spec ))
  **
  ((EX pos_l__2 radj_col_l__2 radj_row_l__2,
  “ (transpose_spec g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec radj_col_l__2 radj_row_l__2 n_pre ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_low_level_spec)) radj_col_l__2 )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l__2 )
  **  (IntArray.full pos_pre n_pre pos_l__2 ))
  -*
  (EX pos_l_ radj_col_l_ radj_row_l_,
  “ (transpose_spec g_high_level_spec fadj_col_l_high_level_spec fadj_row_l_high_level_spec radj_col_l_ radj_row_l_ n_pre ) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_high_level_spec)) fadj_col_l_high_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_high_level_spec )
  **  (IntArray.full radj_col_pre (m_of (fadj_row_l_high_level_spec)) radj_col_l_ )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_ )
  **  (IntArray.full pos_pre n_pre pos_l_ )))
.

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

Axiom proof_of_transpose_safety_wit_1 : transpose_safety_wit_1.
Axiom proof_of_transpose_safety_wit_2 : transpose_safety_wit_2.
Axiom proof_of_transpose_safety_wit_3 : transpose_safety_wit_3.
Axiom proof_of_transpose_safety_wit_4 : transpose_safety_wit_4.
Axiom proof_of_transpose_safety_wit_5 : transpose_safety_wit_5.
Axiom proof_of_transpose_safety_wit_6 : transpose_safety_wit_6.
Axiom proof_of_transpose_safety_wit_7 : transpose_safety_wit_7.
Axiom proof_of_transpose_safety_wit_8 : transpose_safety_wit_8.
Axiom proof_of_transpose_safety_wit_9 : transpose_safety_wit_9.
Axiom proof_of_transpose_safety_wit_10 : transpose_safety_wit_10.
Axiom proof_of_transpose_safety_wit_11 : transpose_safety_wit_11.
Axiom proof_of_transpose_safety_wit_12 : transpose_safety_wit_12.
Axiom proof_of_transpose_safety_wit_13 : transpose_safety_wit_13.
Axiom proof_of_transpose_safety_wit_14 : transpose_safety_wit_14.
Axiom proof_of_transpose_safety_wit_15 : transpose_safety_wit_15.
Axiom proof_of_transpose_safety_wit_16 : transpose_safety_wit_16.
Axiom proof_of_transpose_safety_wit_17 : transpose_safety_wit_17.
Axiom proof_of_transpose_safety_wit_18 : transpose_safety_wit_18.
Axiom proof_of_transpose_safety_wit_19 : transpose_safety_wit_19.
Axiom proof_of_transpose_entail_wit_1 : transpose_entail_wit_1.
Axiom proof_of_transpose_entail_wit_2 : transpose_entail_wit_2.
Axiom proof_of_transpose_entail_wit_3 : transpose_entail_wit_3.
Axiom proof_of_transpose_entail_wit_4 : transpose_entail_wit_4.
Axiom proof_of_transpose_entail_wit_5 : transpose_entail_wit_5.
Axiom proof_of_transpose_entail_wit_6 : transpose_entail_wit_6.
Axiom proof_of_transpose_entail_wit_7 : transpose_entail_wit_7.
Axiom proof_of_transpose_entail_wit_8 : transpose_entail_wit_8.
Axiom proof_of_transpose_entail_wit_9 : transpose_entail_wit_9.
Axiom proof_of_transpose_entail_wit_10 : transpose_entail_wit_10.
Axiom proof_of_transpose_entail_wit_11 : transpose_entail_wit_11.
Axiom proof_of_transpose_entail_wit_12 : transpose_entail_wit_12.
Axiom proof_of_transpose_entail_wit_13 : transpose_entail_wit_13.
Axiom proof_of_transpose_return_wit_1 : transpose_return_wit_1.
Axiom proof_of_transpose_partial_solve_wit_1 : transpose_partial_solve_wit_1.
Axiom proof_of_transpose_partial_solve_wit_2 : transpose_partial_solve_wit_2.
Axiom proof_of_transpose_partial_solve_wit_3 : transpose_partial_solve_wit_3.
Axiom proof_of_transpose_partial_solve_wit_4 : transpose_partial_solve_wit_4.
Axiom proof_of_transpose_partial_solve_wit_5 : transpose_partial_solve_wit_5.
Axiom proof_of_transpose_partial_solve_wit_6 : transpose_partial_solve_wit_6.
Axiom proof_of_transpose_partial_solve_wit_7 : transpose_partial_solve_wit_7.
Axiom proof_of_transpose_partial_solve_wit_8 : transpose_partial_solve_wit_8.
Axiom proof_of_transpose_partial_solve_wit_9 : transpose_partial_solve_wit_9.
Axiom proof_of_transpose_partial_solve_wit_10 : transpose_partial_solve_wit_10.
Axiom proof_of_transpose_partial_solve_wit_11 : transpose_partial_solve_wit_11.
Axiom proof_of_transpose_partial_solve_wit_12 : transpose_partial_solve_wit_12.
Axiom proof_of_transpose_partial_solve_wit_13 : transpose_partial_solve_wit_13.
Axiom proof_of_transpose_partial_solve_wit_14 : transpose_partial_solve_wit_14.
Axiom proof_of_kosaraju_safety_wit_1 : kosaraju_safety_wit_1.
Axiom proof_of_kosaraju_safety_wit_2 : kosaraju_safety_wit_2.
Axiom proof_of_kosaraju_safety_wit_3 : kosaraju_safety_wit_3.
Axiom proof_of_kosaraju_safety_wit_4 : kosaraju_safety_wit_4.
Axiom proof_of_kosaraju_safety_wit_5 : kosaraju_safety_wit_5.
Axiom proof_of_kosaraju_safety_wit_6 : kosaraju_safety_wit_6.
Axiom proof_of_kosaraju_safety_wit_7 : kosaraju_safety_wit_7.
Axiom proof_of_kosaraju_safety_wit_8 : kosaraju_safety_wit_8.
Axiom proof_of_kosaraju_safety_wit_9 : kosaraju_safety_wit_9.
Axiom proof_of_kosaraju_safety_wit_10 : kosaraju_safety_wit_10.
Axiom proof_of_kosaraju_safety_wit_11 : kosaraju_safety_wit_11.
Axiom proof_of_kosaraju_safety_wit_12 : kosaraju_safety_wit_12.
Axiom proof_of_kosaraju_safety_wit_13 : kosaraju_safety_wit_13.
Axiom proof_of_kosaraju_safety_wit_14 : kosaraju_safety_wit_14.
Axiom proof_of_kosaraju_safety_wit_15 : kosaraju_safety_wit_15.
Axiom proof_of_kosaraju_safety_wit_16 : kosaraju_safety_wit_16.
Axiom proof_of_kosaraju_safety_wit_17 : kosaraju_safety_wit_17.
Axiom proof_of_kosaraju_safety_wit_18 : kosaraju_safety_wit_18.
Axiom proof_of_kosaraju_safety_wit_19 : kosaraju_safety_wit_19.
Axiom proof_of_kosaraju_safety_wit_20 : kosaraju_safety_wit_20.
Axiom proof_of_kosaraju_entail_wit_1 : kosaraju_entail_wit_1.
Axiom proof_of_kosaraju_entail_wit_2 : kosaraju_entail_wit_2.
Axiom proof_of_kosaraju_entail_wit_3 : kosaraju_entail_wit_3.
Axiom proof_of_kosaraju_entail_wit_4 : kosaraju_entail_wit_4.
Axiom proof_of_kosaraju_entail_wit_5 : kosaraju_entail_wit_5.
Axiom proof_of_kosaraju_entail_wit_6 : kosaraju_entail_wit_6.
Axiom proof_of_kosaraju_entail_wit_7 : kosaraju_entail_wit_7.
Axiom proof_of_kosaraju_entail_wit_8_1 : kosaraju_entail_wit_8_1.
Axiom proof_of_kosaraju_entail_wit_8_2 : kosaraju_entail_wit_8_2.
Axiom proof_of_kosaraju_entail_wit_9 : kosaraju_entail_wit_9.
Axiom proof_of_kosaraju_entail_wit_10 : kosaraju_entail_wit_10.
Axiom proof_of_kosaraju_entail_wit_11 : kosaraju_entail_wit_11.
Axiom proof_of_kosaraju_entail_wit_12 : kosaraju_entail_wit_12.
Axiom proof_of_kosaraju_entail_wit_13 : kosaraju_entail_wit_13.
Axiom proof_of_kosaraju_entail_wit_14 : kosaraju_entail_wit_14.
Axiom proof_of_kosaraju_entail_wit_15_1 : kosaraju_entail_wit_15_1.
Axiom proof_of_kosaraju_entail_wit_15_2 : kosaraju_entail_wit_15_2.
Axiom proof_of_kosaraju_entail_wit_16 : kosaraju_entail_wit_16.
Axiom proof_of_kosaraju_return_wit_1 : kosaraju_return_wit_1.
Axiom proof_of_kosaraju_partial_solve_wit_1 : kosaraju_partial_solve_wit_1.
Axiom proof_of_kosaraju_partial_solve_wit_2_pure : kosaraju_partial_solve_wit_2_pure.
Axiom proof_of_kosaraju_partial_solve_wit_2 : kosaraju_partial_solve_wit_2.
Axiom proof_of_kosaraju_partial_solve_wit_3_pure : kosaraju_partial_solve_wit_3_pure.
Axiom proof_of_kosaraju_partial_solve_wit_3 : kosaraju_partial_solve_wit_3.
Axiom proof_of_kosaraju_partial_solve_wit_4_pure : kosaraju_partial_solve_wit_4_pure.
Axiom proof_of_kosaraju_partial_solve_wit_4 : kosaraju_partial_solve_wit_4.
Axiom proof_of_kosaraju_partial_solve_wit_5_pure : kosaraju_partial_solve_wit_5_pure.
Axiom proof_of_kosaraju_partial_solve_wit_5 : kosaraju_partial_solve_wit_5.
Axiom proof_of_kosaraju_partial_solve_wit_6_pure : kosaraju_partial_solve_wit_6_pure.
Axiom proof_of_kosaraju_partial_solve_wit_6 : kosaraju_partial_solve_wit_6.
Axiom proof_of_kosaraju_partial_solve_wit_7_pure : kosaraju_partial_solve_wit_7_pure.
Axiom proof_of_kosaraju_partial_solve_wit_7 : kosaraju_partial_solve_wit_7.
Axiom proof_of_kosaraju_partial_solve_wit_8 : kosaraju_partial_solve_wit_8.
Axiom proof_of_kosaraju_partial_solve_wit_9 : kosaraju_partial_solve_wit_9.
Axiom proof_of_kosaraju_partial_solve_wit_10_pure : kosaraju_partial_solve_wit_10_pure.
Axiom proof_of_kosaraju_partial_solve_wit_10 : kosaraju_partial_solve_wit_10.
Axiom proof_of_kosaraju_partial_solve_wit_11 : kosaraju_partial_solve_wit_11.
Axiom proof_of_kosaraju_partial_solve_wit_12_pure : kosaraju_partial_solve_wit_12_pure.
Axiom proof_of_kosaraju_partial_solve_wit_12 : kosaraju_partial_solve_wit_12.
Axiom proof_of_kosaraju_partial_solve_wit_13 : kosaraju_partial_solve_wit_13.
Axiom proof_of_kosaraju_partial_solve_wit_14 : kosaraju_partial_solve_wit_14.
Axiom proof_of_kosaraju_partial_solve_wit_15 : kosaraju_partial_solve_wit_15.
Axiom proof_of_kosaraju_partial_solve_wit_16 : kosaraju_partial_solve_wit_16.
Axiom proof_of_kosaraju_partial_solve_wit_17 : kosaraju_partial_solve_wit_17.
Axiom proof_of_kosaraju_partial_solve_wit_18_pure : kosaraju_partial_solve_wit_18_pure.
Axiom proof_of_kosaraju_partial_solve_wit_18 : kosaraju_partial_solve_wit_18.
Axiom proof_of_kosaraju_partial_solve_wit_19 : kosaraju_partial_solve_wit_19.
Axiom proof_of_kosaraju_partial_solve_wit_20 : kosaraju_partial_solve_wit_20.
Axiom proof_of_kosaraju_partial_solve_wit_21 : kosaraju_partial_solve_wit_21.
Axiom proof_of_kosaraju_partial_solve_wit_22 : kosaraju_partial_solve_wit_22.
Axiom proof_of_kosaraju_partial_solve_wit_23 : kosaraju_partial_solve_wit_23.
Axiom proof_of_kosaraju_partial_solve_wit_24 : kosaraju_partial_solve_wit_24.
Axiom proof_of_transpose_derive_high_level_spec_by_low_level_spec : transpose_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_dfs2_derive_bind_spec_by_low_level_spec : dfs2_derive_bind_spec_by_low_level_spec.
Axiom proof_of_dfs2_derive_phase2_spec_by_low_level_spec : dfs2_derive_phase2_spec_by_low_level_spec.
Axiom proof_of_dfs2_derive_high_level_spec_by_low_level_spec : dfs2_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_dfs1_derive_bind_spec_by_low_level_spec : dfs1_derive_bind_spec_by_low_level_spec.
Axiom proof_of_dfs1_derive_high_level_spec_by_low_level_spec : dfs1_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
